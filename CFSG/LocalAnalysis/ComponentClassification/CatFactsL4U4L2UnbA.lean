module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Unb

open CFSG Subgroup CFSG.GH74.KGroups Equiv CFSG.ComponentClassification.GrSLit

theorem pow_sixteen_of_autModel {K : Type} [Group K] {n : ℕ} (M : AutModel K (Perm (Fin n)))
    (hPA : M.P ≤ M.A)
    (hinv : ∀ x ∈ M.P, x * x = 1 → x ≠ 1 → ∀ y ∈ M.A, y * x = x * y → y ^ 16 = 1)
    {k : K} (hk2 : k * k = 1) (hk1 : k ≠ 1) {ψ : MulAut K}
    (hψ : ψ * MulAut.conj k = MulAut.conj k * ψ) : ψ ^ 16 = 1 := by
  set x : Perm (Fin n) := (M.e k : Perm (Fin n)) with hx
  have hxP : x ∈ M.P := (M.e k).2
  have hxx : x * x = 1 := by
    rw [hx, ← Subgroup.coe_mul, ← map_mul, hk2, map_one, Subgroup.coe_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply hk1
    apply M.e.injective
    rw [map_one]
    exact Subtype.ext h
  have hιk : M.ι (MulAut.conj k) = x := by
    set β := M.Φ.symm ⟨x, hPA hxP⟩ with hβ
    have hβk : β = MulAut.conj k := by
      apply MulEquiv.ext
      intro u
      apply M.e.injective
      apply Subtype.ext
      rw [M.spec, hβ, MulEquiv.apply_symm_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
        Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hβk, hβ]
    change ((M.Φ (M.Φ.symm ⟨x, hPA hxP⟩) : M.A) : Perm (Fin n)) = x
    rw [MulEquiv.apply_symm_apply]
  have hcomm : M.ι ψ * x = x * M.ι ψ := by
    rw [← hιk, ← map_mul, ← map_mul, hψ]
  have h16 := hinv x hxP hxx hx1 _ (M.ι_mem ψ) hcomm
  apply M.ι_injective
  rw [map_pow, h16, map_one]

theorem pow_sixteen_of_psl27
    {K : Type} [Group K] (h : Blueprint.LieModel K .PSL 2 7 1) {k : K} (hk2 : k * k = 1)
    (hk1 : k ≠ 1) {ψ : MulAut K} (hψ : ψ * MulAut.conj k = MulAut.conj k * ψ) :
    ψ ^ 16 = 1 := by
  obtain ⟨e⟩ := L27.equiv_of_lieModel h
  obtain ⟨M, hP, hA⟩ := L27.autModel e
  refine pow_sixteen_of_autModel M ?_ ?_ hk2 hk1 hψ
  · rw [hP, hA]
    intro x hx
    exact (mem_iff_sift _ L27.QA_ok x).2 (forall_of_all _ L27.QP_ok l27_sub_check x hx)
  · rw [hP, hA]
    intro x hx hx2 hx1 y hy hyx
    have h1 := forall_of_all _ L27.QP_ok l27_inv_check x hx
    simp only [hx2, hx1, decide_true, decide_false, Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.1 h1 y ((mem_elemsT _ L27.QA_ok y).2 hy)
    simpa [hyx] using h2

theorem pow_sixteen_of_alternating_five {K : Type} [Group K]
    (e : K ≃* alternatingGroup (Fin 5)) {k : K} (hk2 : k * k = 1) (hk1 : k ≠ 1) {ψ : MulAut K}
    (hψ : ψ * MulAut.conj k = MulAut.conj k * ψ) : ψ ^ 16 = 1 := by
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
    (by norm_num)
  let Φ' : (⊤ : Subgroup (Perm (Fin 5))) ≃* MulAut (alternatingGroup (Fin 5)) :=
    topEquiv.trans (MulEquiv.ofBijective _ hbij)
  let M : AutModel K (Perm (Fin 5)) := AutModel.ofRealization (alternatingGroup (Fin 5)) ⊤ e Φ'
    (fun σ x => by
      show ((MulAut.conjNormal (σ : Perm (Fin 5)) x : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        σ * x * (σ : Perm (Fin 5))⁻¹
      rw [MulAut.conjNormal_apply])
  refine pow_sixteen_of_autModel M le_top ?_ hk2 hk1 hψ
  intro x hx hx2 hx1 y _ hyx
  exact a5_inv_check x y (Perm.mem_alternatingGroup.mp hx) hx2 hx1 hyx

theorem pow_sixteen_of_comm_conj
    {K : Type} [Group K]
    (hK : IsL2Type 5 K ∨ IsL2Type 7 K) {k : K} (hk2 : k * k = 1) (hk1 : k ≠ 1) {ψ : MulAut K}
    (hψ : ψ * MulAut.conj k = MulAut.conj k * ψ) : ψ ^ 16 = 1 := by
  rcases hK with h5 | h7
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) h5
    obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by simpa using hF))
    exact pow_sixteen_of_alternating_five (e.trans e') hk2 hk1 hψ
  · exact pow_sixteen_of_psl27 h7 hk2 hk1 hψ

end L2Unb

end CFSG.ComponentClassification.CatFactsL4U4
