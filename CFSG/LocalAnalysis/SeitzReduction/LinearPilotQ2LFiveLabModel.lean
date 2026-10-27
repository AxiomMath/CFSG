module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Model

variable {n : ℕ} {K : Type*} [Field K]

theorem pointRadElem_single_eq {c j : Fin n} (hjc : j ≠ c) :
    pointRadElem c (Pi.single j (1 : K)) =
      SpecialLinearGroup.transvection hjc.symm (1 : K) := by
  apply Subtype.ext
  rw [coe_pointRadElem, pointRadMat_single hjc, SpecialLinearGroup.transvection_coe]
  congr 1
  ext a b
  simp only [vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  rcases eq_or_ne a c with rfl | ha
  · rcases eq_or_ne b j with rfl | hb
    · simp
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]

theorem dualAut_proj_transvection [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    LinearFlag.dualAut n K (LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K))) =
      LinearFlag.proj n K (SpecialLinearGroup.transvection hij.symm (1 : K)) := by
  rw [LinearFlag.dualAut_proj]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_transpose, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single, CharTwo.neg_eq]

theorem dualAut_symm_proj_transvection [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    (LinearFlag.dualAut n K).symm
        (LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K))) =
      LinearFlag.proj n K (SpecialLinearGroup.transvection hij.symm (1 : K)) := by
  rw [MulEquiv.symm_apply_eq, dualAut_proj_transvection hij.symm]

theorem eq_zero_of_proj_pointRadElem_commute (hK : Nat.card K = 2) {c a j : Fin n}
    (hjc : j ≠ c) (hja : j ≠ a) (r : Fin n → K)
    (h : LinearFlag.proj n K (pointRadElem c r) *
        LinearFlag.proj n K (SpecialLinearGroup.transvection hja (1 : K)) =
      LinearFlag.proj n K (SpecialLinearGroup.transvection hja (1 : K)) *
        LinearFlag.proj n K (pointRadElem c r)) :
    r j = 0 := by
  have hm := mul_eq_mul_of_proj_mul_eq hK h
  rw [coe_pointRadElem, SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul] at hm
  have he := congrFun₂ hm c a
  have hjc' : ¬ (j = c) := hjc
  simp [Matrix.mul_apply, Matrix.single_apply, hjc'] at he
  rw [pointRadMat_apply, Matrix.one_apply_ne hjc.symm, zero_add] at he
  simpa [hjc] using he

end Model

section Seitz2

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem linTv_mem_pointRadical (e : L ≃* LinearFlag.projectiveSL n K) {c j : Fin n}
    (hcj : c ≠ j) : linTv e hcj ∈ modelToG e (pointRadical (K := K) c) := by
  have h := proj_pointRadElem_single_mem (K := K) hcj.symm
  rw [pointRadElem_single_eq hcj.symm] at h
  exact symm_mem_modelToG e h

theorem modelToG_pointRadical_le (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (c : Fin n) {H : Subgroup G} (hH : ∀ j (hcj : c ≠ j), linTv e hcj ∈ H) :
    modelToG e (pointRadical (K := K) c) ≤ H := by
  set φ : Matrix.SpecialLinearGroup (Fin n) K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (LinearFlag.proj n K)) with hφ
  have hφapp : ∀ A, φ A = ((e.symm (LinearFlag.proj n K A) : L) : G) := fun A => rfl
  have hsingle : ∀ (j : Fin n) (x : K), φ (pointRadElem c (Pi.single j x)) ∈ H := by
    intro j x
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK x with rfl | rfl
    · rw [Pi.single_zero, pointRadElem_zero, map_one]
      exact one_mem H
    · by_cases hjc : j = c
      · subst hjc
        have h1 : pointRadElem j (Pi.single j (1 : K)) = 1 := by
          rw [← pointRadElem_update_eq j _ 0]
          have : Function.update (Pi.single j (1 : K) : Fin n → K) j 0 = (0 : Fin n → K) := by
            ext k
            by_cases hk : k = j
            · subst hk; simp
            · simp [hk]
          rw [this, pointRadElem_zero]
        rw [h1, map_one]
        exact one_mem H
      · rw [pointRadElem_single_eq hjc, hφapp]
        exact hH j (Ne.symm hjc)
  have hs : ∀ (r : Fin n → K) (s : Finset (Fin n)),
      φ (pointRadElem c (∑ j ∈ s, Pi.single j (r j))) ∈ H := by
    intro r s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, pointRadElem_zero, map_one]
      exact one_mem H
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← pointRadElem_mul, map_mul]
      exact mul_mem (hsingle a (r a)) ih
  intro g hg
  obtain ⟨v, hv, rfl⟩ := (mem_modelToG e).1 hg
  obtain ⟨r, -, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hv
  have h := hs r Finset.univ
  rwa [Finset.univ_sum_single] at h

theorem exists_pointRadElem_of_mem (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    {c : Fin n} (a : Fin n) {v : G} (hv : v ∈ modelToG e (pointRadical (K := K) c)) :
    ∃ r : Fin n → K, r c = 0 ∧
      v = ((e.symm (LinearFlag.proj n K (pointRadElem c r)) : L) : G) ∧
      ∀ j (_hjc : j ≠ c) (hja : j ≠ a), v * linTv e hja = linTv e hja * v → r j = 0 := by
  obtain ⟨p, hp, rfl⟩ := (mem_modelToG e).1 hv
  obtain ⟨r, hrc, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hp
  refine ⟨r, hrc, rfl, fun j hjc hja h => ?_⟩
  apply eq_zero_of_proj_pointRadElem_commute hK hjc hja r
  have h1 : e.symm (LinearFlag.proj n K (pointRadElem c r)) *
      e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hja (1 : K))) =
      e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hja (1 : K))) *
        e.symm (LinearFlag.proj n K (pointRadElem c r)) := Subtype.ext h
  have h2 := congrArg e h1
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

theorem eq_one_or_of_pointRadElem (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    {c a b : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) {r : Fin n → K}
    (hr : ∀ j, j ≠ a → j ≠ b → r j = 0) :
    let v := ((e.symm (LinearFlag.proj n K (pointRadElem c r)) : L) : G)
    v = 1 ∨ v = linTv e hcb ∨ v = linTv e hca ∨ v = linTv e hcb * linTv e hca := by
  intro v
  have hr' : r = Pi.single b (r b) + Pi.single a (r a) := by
    ext j
    by_cases hja : j = a
    · subst hja
      simp [hab]
    · by_cases hjb : j = b
      · subst hjb
        simp [hja]
      · simp [hja, hjb, hr j hja hjb]
  have hv : v = ((e.symm (LinearFlag.proj n K (pointRadElem c (Pi.single b (r b))))) : G) *
      ((e.symm (LinearFlag.proj n K (pointRadElem c (Pi.single a (r a))))) : G) := by
    simp only [v]
    rw [hr', ← pointRadElem_mul, map_mul, map_mul, Subgroup.coe_mul]
    congr 3 <;> simp [hab, hab.symm]
  have hsingle : ∀ (j : Fin n) (hcj : c ≠ j) (x : K), x = 0 ∨ x = 1 →
      ((e.symm (LinearFlag.proj n K (pointRadElem c (Pi.single j x)))) : G) = 1 ∨
        ((e.symm (LinearFlag.proj n K (pointRadElem c (Pi.single j x)))) : G) = linTv e hcj := by
    intro j hcj x hx
    rcases hx with rfl | rfl
    · left
      rw [Pi.single_zero, pointRadElem_zero, map_one, map_one, Subgroup.coe_one]
    · right
      rw [pointRadElem_single_eq hcj.symm]
      rfl
  rcases hsingle b hcb (r b) (eq_zero_or_eq_one_of_natCard_eq_two hK _) with h1 | h1 <;>
    rcases hsingle a hca (r a) (eq_zero_or_eq_one_of_natCard_eq_two hK _) with h2 | h2 <;>
    rw [hv, h1, h2]
  · left; group
  · right; right; left; group
  · right; left; group
  · right; right; right; rfl

theorem eq_one_or_of_pointRadElem_one (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    {c a : Fin n} (hca : c ≠ a) {r : Fin n → K} (hr : ∀ j, j ≠ a → r j = 0) :
    ((e.symm (LinearFlag.proj n K (pointRadElem c r)) : L) : G) = 1 ∨
      ((e.symm (LinearFlag.proj n K (pointRadElem c r)) : L) : G) = linTv e hca := by
  have hr' : r = Pi.single a (r a) := by
    ext j
    by_cases hja : j = a
    · subst hja
      simp
    · simp [hja, hr j hja]
  rw [hr']
  rcases eq_zero_or_eq_one_of_natCard_eq_two hK (r a) with h | h <;> rw [h]
  · left
    rw [Pi.single_zero, pointRadElem_zero, map_one, map_one, Subgroup.coe_one]
  · right
    rw [pointRadElem_single_eq hca.symm]
    rfl

end Seitz2

section Seitz

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem linTv_trans_dualAut [CharP K 2] (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n}
    (hij : i ≠ j) : linTv (e.trans (LinearFlag.dualAut n K)) hij = linTv e hij.symm := by
  rw [linTv, linTv, MulEquiv.symm_trans_apply, dualAut_symm_proj_transvection]

theorem linTv_commutator (e : L ≃* LinearFlag.projectiveSL n K) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    linTv e hij * linTv e hjk * (linTv e hij)⁻¹ * (linTv e hjk)⁻¹ = linTv e hik := by
  have h := transvection_mul_transvection_mul_inv_mul_inv (K := K) hij hjk hik 1 1
  rw [one_mul] at h
  rw [linTv, linTv, linTv, ← h]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

end Seitz

end CFSG.SeitzReduction.LinearPilot
