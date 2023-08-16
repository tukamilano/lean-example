theorem p : a ∧ b → b ∧ a := by
  intro h
  constructor
  exact h.right
  exact h.left  