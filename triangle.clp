(defglobal
  ?*high-priority* = 2
  ?*mid-high-priority* = 1
  ?*low-priority* = -2
)

(deffunction cosines-law-angle (?a ?b ?c)
  (bind ?num (- (+ (* ?b ?b) (* ?c ?c)) (* ?a ?a)))
  (bind ?den (* 2 ?b ?c))
  (bind ?cosA (/ ?num ?den))
  (acos ?cosA)
)

(deffunction cosines-law-side (?a ?b ?C)
  (sqrt (- (+ (* ?a ?a) (* ?b ?b)) (* 2 ?a ?b (cos ?C))))
)

(deffunction sines-law-angle (?a ?b ?B)
  (asin (* (/ ?a ?b) (sin ?B)))
)

(deffunction sines-law-side (?a ?A ?B)
  (* ?a (/ (sin ?B) (sin ?A)))
)

(defrule triangle-solved
  ?solving <- (solving-triangle)
  (side-has-length ?a ?la&~nil)
  (side-has-length ?b&:(neq ?b ?a) ?lb&~nil)
  (side-has-length ?c&:(neq ?c ?a ?b) ?lc&~nil)
  (angle-has-value ?A ?vA&~nil)
  (angle-has-value ?B&:(neq ?B ?A) ?vB&~nil)
  (angle-has-value ?C&:(neq ?C ?A ?B) ?vC&~nil)
  =>
  (printout t
    "Triangle solved:" crlf
    "  " ?a "=" ?la ", " ?b "=" ?lb ", " ?c "=" ?lc crlf
    "  " ?A "=" (rad-deg ?vA) ", " ?B "=" (rad-deg ?vB) ", and "
         ?C "=" (rad-deg ?vC) crlf)
  (retract ?solving)
  (assert (solved-triangle))
)

(defrule cosines-law-angle
  "Apply Cosines Law to calculate missing angle using the three known sides"
  (declare (salience ?*mid-high-priority*))
  (solving-triangle)
  (side-has-length ?a ?la&~nil)
  (side-has-length ?b&:(neq ?b ?a) ?lb&~nil)
  (side-has-length ?c&:(neq ?c ?a ?b) ?lc&~nil)
  (opposite-angle ?a ?A)
  ?unknown <- (angle-has-value ?A nil)
  =>
  (printout t "Using Cosines Law to obtain " ?A " from " ?a ", " ?b ", and " ?c crlf)
  (retract ?unknown)
  (assert (angle-has-value ?A (cosines-law-angle ?la ?lb ?lc)))
)

(defrule cosines-law-side
  "Apply Cosines Law to calculate missing side using two known sides and angle in between"
  (solving-triangle)
  (side-has-length ?a ?la&~nil)
  (side-has-length ?b&:(neq ?b ?a) ?lb&~nil)
  ?unknown <- (side-has-length ?c nil)
  (opposite-angle ?c ?C)
  (angle-has-value ?C ?vC&~nil)
  =>
  (printout t "Using Cosines Law to obtain " ?c " from " ?a ", " ?b ", and " ?C crlf)
  (retract ?unknown)
  (assert (side-has-length ?c (cosines-law-side ?la ?lb ?vC)))
)

(defrule sines-law-angle
  "Apply Sines Law to calculate missing angle using two known sides and angle not in between"
  (solving-triangle)
  (side-has-length ?a ?la&~nil)
  (side-has-length ?b&:(neq ?b ?a) ?lb&~nil)
  (opposite-angle ?a ?A)
  (opposite-angle ?b ?B)
  (angle-has-value ?B ?vB)
  ?unknown <- (angle-has-value ?A nil)
  =>
  (printout t "Using Sines Law to obtain " ?A " from " ?a ", " ?b ", and " ?B crlf)
  (retract ?unknown)
  (assert (angle-has-value ?A (sines-law-angle ?la ?lb ?vB)))
)

(defrule sines-law-side
  "Apply Sines Law to calculate missing side using two angles and one side"
  (solving-triangle)
  (side-has-length ?a ?la&~nil)
  ?unknown <- (side-has-length ?b nil)
  (opposite-angle ?a ?A)
  (opposite-angle ?b ?B)
  (angle-has-value ?A ?vA&~nil)
  (angle-has-value ?B ?vB&~nil)
  =>
  (printout t "Using Sines Law to obtain " ?b " from " ?a ", " ?A ", and " ?B crlf)
  (retract ?unknown)
  (assert (side-has-length ?b (sines-law-side ?la ?vA ?vB)))
)

(defrule angles-sum-pi
  "Angles sum to pi, so use this when only one of the angles is missing"
  (declare (salience ?*high-priority*))
  (solving-triangle)
  (angle-has-value ?A ?vA&~nil)
  (angle-has-value ?B&:(neq ?B ?A) ?vB&~nil)
  ?unknown <- (angle-has-value ?C nil)
  =>
  (printout t "Subtracting " ?A " and " ?B " from 180 to obtain " ?C crlf)
  (retract ?unknown)
  (assert (angle-has-value ?C (- (pi) ?vA ?vB)))
)
  
(defrule not-enough-data
  (declare (salience ?*low-priority*))
  ?solving <- (solving-triangle)
  =>
  (printout t "Not enough data to solve triangle" crlf)
  (retract ?solving)
  (assert (unsolvable-triangle "Not enough data")))

