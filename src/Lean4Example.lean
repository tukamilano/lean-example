theorem p0 : a ∧ b → b ∧ a := by
  intro h
  constructor
  exact h.right
  exact h.left

theorem p1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp