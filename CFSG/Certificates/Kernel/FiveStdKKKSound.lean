module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat7

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.FiveStd.Mat

@[expose] def muE (x : E) : Fin 5 := detA x * detA x

theorem s_normE (z : E) : (normE z).s = z.s := rfl

theorem s_mulE (x y : E) : (mulE x y).s = (x.s != y.s) := by
  rw [mulE_eq, s_normE]
  cases hx : x.s <;> cases hy : y.s <;> simp [mulRaw, hx, hy]

theorem s_invE (x : E) : (invE x).s = x.s := by
  rw [invE_eq, s_normE]
  cases hx : x.s <;> simp [invRaw, hx]

theorem detA_normE (z : E) : detA (normE z) = cn z * cn z * detA z := by
  rw [normE_eq_scaleE, detA_scaleE]

theorem sq4 : ∀ c d : Fin 5, c ≠ 0 → (c * c * d) * (c * c * d) = d * d := by decide

theorem sqB : ∀ a b : Fin 5, a * b = 1 → b * b = a * a := by decide

theorem sq_inv5 : ∀ a : Fin 5, a ≠ 0 → inv5 a * inv5 a = a * a := by decide

theorem sq_inv5B : ∀ a b : Fin 5, a * b = 1 → inv5 b * inv5 b = a * a := by decide

theorem kk5 : ∀ a b : Fin 5, a * b = 1 → (a = b ↔ a * a = 1) := by decide

theorem mu_sq : ∀ a b : Fin 5, a * b = 1 → a * a * (a * a) = 1 := by decide

theorem sq_mul : ∀ a b : Fin 5, a * b * (a * b) = a * a * (b * b) := by decide

theorem mu3 : ∀ a b : Fin 5, a * b * a = b * (a * a) := by decide

theorem muE_normE {z : E} (hA : detA z ≠ 0) : muE (normE z) = muE z := by
  unfold muE
  rw [detA_normE]
  exact sq4 _ _ (cn_ne_zero hA)

theorem muE_mulE {x y : E} (hx : validE x = true) (hy : validE y = true) :
    muE (mulE x y) = muE x * muE y := by
  obtain ⟨hxA, -⟩ := det_ne_zero_of_valid hx
  obtain ⟨hyA, hyB⟩ := det_ne_zero_of_valid hy
  have hy1 := ((validE_iff y).1 hy).2
  rw [mulE_eq]
  cases hs : x.s
  · rw [muE_normE (by rw [detA_mulRaw_of_false y hs]; exact mul_ne_zero_fin5 _ _ hxA hyA)]
    unfold muE
    rw [detA_mulRaw_of_false y hs, sq_mul]
  · rw [muE_normE (by rw [detA_mulRaw_of_true y hs]; exact mul_ne_zero_fin5 _ _ hxA hyB)]
    unfold muE
    rw [detA_mulRaw_of_true y hs, sq_mul, sqB _ _ hy1]

theorem muE_invE {x : E} (hx : validE x = true) : muE (invE x) = muE x := by
  obtain ⟨hxA, hxB⟩ := det_ne_zero_of_valid hx
  have hx1 := ((validE_iff x).1 hx).2
  rw [invE_eq]
  cases hs : x.s
  · rw [muE_normE (by rw [detA_invRaw_false hx hs]; exact inv5_ne_zero _ hxA)]
    unfold muE
    rw [detA_invRaw_false hx hs]
    exact sq_inv5 _ hxA
  · rw [muE_normE (by rw [detA_invRaw_true hx hs]; exact inv5_ne_zero _ hxB)]
    unfold muE
    rw [detA_invRaw_true hx hs]
    exact sq_inv5B _ _ hx1

theorem inKK_iff {x : E} (hx : validE x = true) : inKK x = true ↔ x.s = false ∧ muE x = 1 := by
  unfold inKK
  rw [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
  exact and_congr_right fun _ => kk5 _ _ ((validE_iff x).1 hx).2

theorem muE_sq {x : E} (hx : validE x = true) : muE x * muE x = 1 :=
  mu_sq _ _ ((validE_iff x).1 hx).2

theorem inKK_conjE {c x : E} (hc : validE c = true) (hx : validE x = true) :
    inKK (conjE c x) = inKK x := by
  have hcx := validE_mulE hc hx
  have hci := validE_invE hc
  unfold conjE
  rw [Bool.eq_iff_iff, inKK_iff (validE_mulE hcx hci), inKK_iff hx]
  rw [s_mulE, s_mulE, s_invE, muE_mulE hcx hci, muE_mulE hc hx, muE_invE hc, mu3, muE_sq hc, mul_one]
  cases c.s <;> cases x.s <;> simp

end CFSG.KC.FiveStdK

end
