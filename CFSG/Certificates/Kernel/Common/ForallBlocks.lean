module

public section

namespace CFSG.KC.ForallBlocks

theorem forall_of_blocks {P : Nat → Prop} {R G n : Nat} (hR : 0 < R) (hn : n ≤ R * G)
    (h : ∀ j < G, ∀ i < R, R * j + i < n → P (R * j + i)) : ∀ k < n, P k := by
  intro k hk
  have hj : k / R < G := Nat.div_lt_of_lt_mul (by omega)
  have e := Nat.div_add_mod k R
  have := h (k / R) hj (k % R) (Nat.mod_lt _ hR) (by omega)
  rwa [e] at this

end CFSG.KC.ForallBlocks

end
