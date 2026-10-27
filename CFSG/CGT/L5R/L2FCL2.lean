module

public import CFSG.CGT.L5R.L2FCL

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

section FC

variable
  (hcard : Nat.card N8 = 322560)
include hcard

theorem swapL (f : N8 → N8) (hfD : ∀ x ∈ DL, f x ∈ DL)
    (hfmul : ∀ x ∈ DL, ∀ y ∈ DL, f (x * y) = f x * f y)
    (hfinj : ∀ x ∈ DL, ∀ y ∈ DL, f x = f y → x = y) (hfA : ∀ a ∈ DL, a ∈ T8 → f a ∈ B8L)
    (hfB : ∀ b ∈ B8L, f b ∈ T8)
    (hz1 : ∀ m : N8, m * f z1L * m⁻¹ ∈ T8 ∨
      Nat.card ↥(T8 ⊓ Subgroup.centralizer ({m * f z1L * m⁻¹} : Set N8)) ≠ 4)
    (hz2 : ∀ m n : N8, n * bL 0 * n⁻¹ ≠ m * f z2L * m⁻¹) :
    ∃ e ∈ DL, ∀ i, e * f (dL i) * e⁻¹ = thL i := by
  have hf1 : f 1 = 1 := by
    have := hfmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  have hwv : ∀ w : List (Fin 2), wv2 dL w ∈ DL ∧ f (wv2 dL w) = wv2 (fun k => f (dL k)) w := by
    intro w
    induction w with
    | nil => exact ⟨one_mem _, hf1⟩
    | cons k w ih =>
      rw [wv2_cons, wv2_cons, hfmul _ (dL_mem hcard k) _ ih.1, ih.2]
      exact ⟨DL.mul_mem (dL_mem hcard k) ih.1, rfl⟩
  set u : Fin 2 → N8 := fun k => f (dL k) with hu
  have hadm : AdmL u := by
    refine ⟨fun l r hlr => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun m => ?_,
      fun m n => ?_⟩
    · rw [← (hwv l).2, ← (hwv r).2, hlr]
    · rw [← (hwv w).2]
      intro h
      exact hw (hfinj _ (hwv w).1 _ (one_mem _) (h.trans hf1.symm))
    · rw [← (hwv w).2]
      exact hfA _ (hwv w).1 hw
    · rw [← (hwv w).2]
      exact hfB _ hw
    · rw [← (hwv z1DW).2]
      exact hz1 m
    · rw [← (hwv z2DW).2]
      exact hz2 m n
  have hu0D : u 0 ∈ DL := hfD _ (dL_mem hcard 0)
  have hu01 : u 0 ≠ 1 := by
    have := hadm.2.1 [0] (by rw [wv2_cons, wv2_nil, mul_one]; exact dL_ne_one hcard)
    simpa [wv2_cons, wv2_nil] using this
  have hu07 : wv2 (fun _ => u 0) sevenW = 1 := by
    have h := hadm.1 sevenW [] (by rw [dL_pow7 hcard, wv2_nil])
    rw [wv2_nil] at h
    exact h
  obtain ⟨e₀, he₀, hr⟩ := stage0_sound hcard hu0D hu01 hu07
  set u' : Fin 2 → N8 := fun k => e₀ * u k * e₀⁻¹ with hu'
  have hadm' : AdmL u' := hadm.conj (T8_normal hcard) he₀
  have hu'eq : u' = ![e₀ * u 0 * e₀⁻¹, u' 1] := by
    funext k
    fin_cases k <;> rfl
  rw [hu'eq] at hadm'
  have hu'1D : u' 1 ∈ DL :=
    DL.mul_mem (DL.mul_mem he₀ (hfD _ (dL_mem hcard 1))) (DL.inv_mem he₀)
  obtain ⟨hr0, k, hk⟩ := stage1_sound hcard hr hu'1D hadm'
  refine ⟨thL 0 ^ k * e₀, DL.mul_mem (DL.pow_mem (thL_mem hcard 0) k) he₀, fun i => ?_⟩
  have e1 : thL 0 ^ k * e₀ * f (dL i) * (thL 0 ^ k * e₀)⁻¹ =
      thL 0 ^ k * u' i * (thL 0 ^ k)⁻¹ := by
    simp only [hu', hu, mul_inv_rev]
    group
  rw [e1]
  fin_cases i
  · show thL 0 ^ k * (e₀ * u 0 * e₀⁻¹) * (thL 0 ^ k)⁻¹ = thL 0
    rw [hr0, ← pow_succ, pow_succ', mul_assoc, mul_inv_cancel, mul_one]
  · exact hk

end FC

end CFSG.CGT.L5R
