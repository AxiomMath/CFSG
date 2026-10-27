module

public import CFSG.GF2Type.SmithTypeE.E7.ClsPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

theorem mem_Wp_iff (v : V12) : v ∈ Wp ↔ (∀ i : Fin 6, i ≠ 5 → v.1 i = 0) ∧ v.2 5 = 0 :=
  Iff.rfl

theorem mem_Cc_iff (v : V12) : v ∈ Cc ↔ (∀ i : Fin 6, i ≠ 5 → v.1 i = 0) ∧ v.1 5 = v.2 5 :=
  Iff.rfl

theorem B12_zero_single_right (x y : Fin 6 → ZMod 2) (j : Fin 6) :
    B12 (x, y) (0, Pi.single j 1) = x j := by
  simp [B12, Pi.single_apply]

theorem B12_E_right (x y : Fin 6 → ZMod 2) (j : Fin 6) :
    B12 (x, y) (Pi.single j 1, 0) = y j := by
  simp [B12, Pi.single_apply]

theorem B12_E_diag (x y : Fin 6 → ZMod 2) (j : Fin 6) :
    B12 (x, y) (Pi.single j 1, Pi.single j 1) = x j + y j := by
  simp [B12, Pi.single_apply, Finset.sum_add_distrib]

theorem Wp_perp (v : V12) (h : ∀ y ∈ Wp, B12 v y = 0) : v ∈ Wp := by
  obtain ⟨a, b⟩ := v
  have hA : ∀ i : Fin 6, i ≠ 5 → a i = 0 := by
    intro i hi
    have hy : ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) ∈ Wp := by
      rw [mem_Wp_iff]
      exact ⟨fun _ _ => rfl, by simp [Pi.single_apply, hi, Ne.symm hi]⟩
    have h0 := h _ hy
    rwa [B12_zero_single_right] at h0
  have hb5 : b 5 = 0 := by
    have hy : ((Pi.single 5 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2)) ∈ Wp := by
      rw [mem_Wp_iff]
      exact ⟨fun k hk => by simp [Pi.single_apply, hk, Ne.symm hk], rfl⟩
    have h0 := h _ hy
    rwa [B12_E_right] at h0
  exact (mem_Wp_iff (a, b)).2 ⟨hA, hb5⟩

theorem Cc_perp (v : V12) (h : ∀ y ∈ Cc, B12 v y = 0) : v ∈ Cc := by
  obtain ⟨a, b⟩ := v
  have key : ∀ s t : ZMod 2, s + t = 0 → s = t := by decide
  have hA : ∀ i : Fin 6, i ≠ 5 → a i = 0 := by
    intro i hi
    have hy : ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) ∈ Cc := by
      rw [mem_Cc_iff]
      exact ⟨fun _ _ => rfl, by simp [Pi.single_apply, hi, Ne.symm hi]⟩
    have h0 := h _ hy
    rwa [B12_zero_single_right] at h0
  have hab5 : a 5 = b 5 := by
    have hy : ((Pi.single 5 1 : Fin 6 → ZMod 2), (Pi.single 5 1 : Fin 6 → ZMod 2)) ∈ Cc := by
      rw [mem_Cc_iff]
      exact ⟨fun k hk => by simp [Pi.single_apply, hk, Ne.symm hk], rfl⟩
    have h0 := h _ hy
    rw [B12_E_diag] at h0
    exact key _ _ h0
  exact (mem_Cc_iff (a, b)).2 ⟨hA, hab5⟩

theorem Cc_isotropic {x y : V12} (hx : x ∈ Cc) (hy : y ∈ Cc) : B12 x y = 0 := by
  obtain ⟨hx1, hx2⟩ := (mem_Cc_iff x).1 hx
  obtain ⟨hy1, hy2⟩ := (mem_Cc_iff y).1 hy
  have key : ∀ s t : ZMod 2, s * t + t * s = 0 := by decide
  unfold B12
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = 5
  · subst hk
    rw [← hx2, ← hy2]
    exact key _ _
  · simp [hx1 k hk, hy1 k hk]

theorem Cc_singular_iff (v : V12) (hv : v ∈ Cc) : q12 v = 0 ↔ v.1 = 0 ∧ v.2 5 = 0 := by
  obtain ⟨h1, h2⟩ := (mem_Cc_iff v).1 hv
  have hs : ∑ i, v.1 i * v.2 i = v.1 5 * v.2 5 := by
    apply Finset.sum_eq_single (5 : Fin 6)
    · intro k _ hk
      rw [h1 k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hq : q12 v = v.1 5 := by
    rw [q12_apply, hs, ← h2, zmod2_mul_self]
  rw [hq]
  constructor
  · intro h0
    have hv1 : v.1 = 0 := by
      funext k
      by_cases hk : k = 5
      · subst hk
        exact h0
      · exact h1 k hk
    exact ⟨hv1, by rw [← h2]; exact h0⟩
  · rintro ⟨h0, -⟩
    exact congrFun h0 5

theorem hs2t5_Tmat_mulVec (v w : Fin 6 → ZMod 2) : Tmat v *ᵥ w = w + w 5 • v := by
  funext i
  fin_cases i <;>
    simp [Tmat, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply, Matrix.of_apply] <;>
    ring

theorem hs2t5_transpose_mulVec {v a : Fin 6 → ZMod 2} (hv : v 5 = 0)
    (ha : ∀ i, i ≠ 5 → a i = 0) : (Tmat v)ᵀ *ᵥ a = a := by
  have h0 : a 0 = 0 := ha 0 (by decide)
  have h1 : a 1 = 0 := ha 1 (by decide)
  have h2 : a 2 = 0 := ha 2 (by decide)
  have h3 : a 3 = 0 := ha 3 (by decide)
  have h4 : a 4 = 0 := ha 4 (by decide)
  funext i
  fin_cases i <;>
    simp [Tmat, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.of_apply, Matrix.transpose_apply, h0, h1, h2, h3, h4, hv]

theorem hs2t5_mulVec_of_eq_zero {N : M6} {a : Fin 6 → ZMod 2} (ha : ∀ i, i ≠ 5 → a i = 0) :
    N *ᵥ a = a 5 • fun i => N i 5 := by
  have h0 : a 0 = 0 := ha 0 (by decide)
  have h1 : a 1 = 0 := ha 1 (by decide)
  have h2 : a 2 = 0 := ha 2 (by decide)
  have h3 : a 3 = 0 := ha 3 (by decide)
  have h4 : a 4 = 0 := ha 4 (by decide)
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, h0, h1, h2, h3, h4] <;> ring

theorem sAkN_apply_Wp {A : GL6} {v : Fin 6 → ZMod 2} (hv : v 5 = 0) (hA : (A : M6) = Tmat v)
    (hAi : ((A⁻¹ : GL6) : M6) = Tmat v) {N : M6} (hN : IsAlt N) {a b : Fin 6 → ZMod 2}
    (ha : ∀ i, i ≠ 5 → a i = 0) (hb : b 5 = 0) :
    (sA A * kN N) (a, b) = (a, b + a 5 • fun i => N i 5) := by
  have hNa : N *ᵥ a = a 5 • fun i => N i 5 := hs2t5_mulVec_of_eq_zero ha
  have hw5 : (b + N *ᵥ a) 5 = 0 := by
    simp [hb, hNa, hN.2 5]
  simp only [LinearEquiv.mul_apply, kN_apply, sA_apply, hAi, hA, Prod.mk.injEq]
  refine ⟨hs2t5_transpose_mulVec hv ha, ?_⟩
  rw [hs2t5_Tmat_mulVec, hw5, zero_smul, add_zero, hNa]

theorem sAkN_apply_Cc {A : GL6} {v : Fin 6 → ZMod 2} (hv : v 5 = 0) (hA : (A : M6) = Tmat v)
    (hAi : ((A⁻¹ : GL6) : M6) = Tmat v) {N : M6} (hN : IsAlt N) {a b : Fin 6 → ZMod 2}
    (ha : ∀ i, i ≠ 5 → a i = 0) (hb : b 5 = a 5) :
    (sA A * kN N) (a, b) = (a, b + a 5 • ((fun i => N i 5) + v)) := by
  have hNa : N *ᵥ a = a 5 • fun i => N i 5 := hs2t5_mulVec_of_eq_zero ha
  have hw5 : (b + N *ᵥ a) 5 = a 5 := by
    simp [hb, hNa, hN.2 5]
  simp only [LinearEquiv.mul_apply, kN_apply, sA_apply, hAi, hA, Prod.mk.injEq]
  refine ⟨hs2t5_transpose_mulVec hv ha, ?_⟩
  rw [hs2t5_Tmat_mulVec, hw5, hNa, smul_add, add_assoc]

section Cert

theorem mem_UFix_Wp_iff (x : Stab0) {v : Fin 6 → ZMod 2} (hv : v 5 = 0)
    (hA : ((alphaS x : GL6) : M6) = Tmat v) : x.1 ∈ UFix Wp ↔ ∀ i, nS x i 5 = 0 := by
  have hAi := inv_eq_Tmat hv hA
  have hN := nS_isAlt x
  have hs := sig_eq_sA_kN x
  rw [mem_UFix]
  constructor
  · intro h i
    have h0 : ∀ j : Fin 6, j ≠ 5 → (Pi.single 5 1 : Fin 6 → ZMod 2) j = 0 := fun j hj => by
      simp [Pi.single_apply, hj]
    have h1 := h ((Pi.single 5 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2)) ⟨h0, rfl⟩
    rw [hs, sAkN_apply_Wp hv hA hAi hN h0 rfl] at h1
    have h2 := congrFun (congrArg Prod.snd h1) i
    simpa using h2
  · intro h y hy
    obtain ⟨a, b⟩ := y
    obtain ⟨ha, hb⟩ := hy
    rw [hs, sAkN_apply_Wp hv hA hAi hN ha hb]
    have hz : (fun i => nS x i 5) = 0 := funext h
    simp [hz]

theorem mem_UFix_Cc_iff (x : Stab0) {v : Fin 6 → ZMod 2} (hv : v 5 = 0)
    (hA : ((alphaS x : GL6) : M6) = Tmat v) : x.1 ∈ UFix Cc ↔ ∀ i, nS x i 5 = v i := by
  have hAi := inv_eq_Tmat hv hA
  have hN := nS_isAlt x
  have hs := sig_eq_sA_kN x
  rw [mem_UFix]
  constructor
  · intro h i
    have h0 : ∀ j : Fin 6, j ≠ 5 → (Pi.single 5 1 : Fin 6 → ZMod 2) j = 0 := fun j hj => by
      simp [Pi.single_apply, hj]
    have h1 := h ((Pi.single 5 1 : Fin 6 → ZMod 2), (Pi.single 5 1 : Fin 6 → ZMod 2)) ⟨h0, rfl⟩
    rw [hs, sAkN_apply_Cc hv hA hAi hN h0 rfl] at h1
    have h2 := congrArg Prod.snd h1
    simp only [Pi.single_eq_same, one_smul] at h2
    have h3 : (fun i => nS x i 5) + v = 0 := add_left_cancel (h2.trans (add_zero _).symm)
    have h4 := congrFun h3 i
    simp only [Pi.add_apply, Pi.zero_apply] at h4
    exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ h4
  · intro h y hy
    obtain ⟨a, b⟩ := y
    obtain ⟨ha, hb⟩ := hy
    rw [hs, sAkN_apply_Cc hv hA hAi hN ha hb.symm]
    have hz : (fun i => nS x i 5) = v := funext h
    have : (fun i => nS x i 5) + v = 0 := by
      rw [hz]
      funext i
      exact zmod2_add_self_eq_zero _
    simp [this]

end Cert

end CFSG.GF2Type.SmithTypeE.E7
