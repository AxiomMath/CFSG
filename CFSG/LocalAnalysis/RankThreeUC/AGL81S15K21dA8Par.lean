module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Mat
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dA8Proof

open CFSG.Quasithin.H13.C1294

@[expose] def LL (M : M4) : Prop := M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 3 0 = 0 ∧ M 3 1 = 0

theorem mulVec_mem_Wc_one {M : M4} (h : LL M) {x : V4} (hx : x ∈ Wc 1) :
    Matrix.mulVec M x ∈ Wc 1 := by
  obtain ⟨h20, h21, h30, h31⟩ := h
  have hx2 : x 2 = 0 := hx 2 (by decide)
  have hx3 : x 3 = 0 := hx 3 (by decide)
  intro i hi
  fin_cases i
  · simp at hi
  · simp at hi
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h20, h21, hx2, hx3]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h30, h31, hx2, hx3]


theorem LL_inv {g : SL4} (h : LL (g : M4)) : LL ((g⁻¹ : SL4) : M4) := by
  have hbt : (g : M4).BlockTriangular (fun i : Fin (3 + 1) => (i : ℕ) / 2) := by
    intro i j hij
    obtain ⟨h20, h21, h30, h31⟩ := h
    fin_cases i <;> fin_cases j <;> simp_all
  have h1 : ((g⁻¹ : SL4) : M4) * (g : M4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (g : M4) * ((g⁻¹ : SL4) : M4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  letI : Invertible (g : M4) := ⟨((g⁻¹ : SL4) : M4), h1, h2⟩
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hbt
  rw [Matrix.inv_eq_left_inv h1] at hinv
  exact ⟨hinv (i := 2) (j := 0) (by decide), hinv (i := 2) (j := 1) (by decide),
    hinv (i := 3) (j := 0) (by decide), hinv (i := 3) (j := 1) (by decide)⟩

theorem stab_Wc_one_iff (g : SL4) :
    (∀ x : V4, x ∈ Wc 1 ↔ Matrix.mulVec (g : M4) x ∈ Wc 1) ↔ LL (g : M4) := by
  constructor
  · intro h
    have key : ∀ j : Fin (3 + 1), j.val ≤ 1 → ∀ i : Fin (3 + 1), 1 < i.val → (g : M4) i j = 0 := by
      intro j hj i hi
      have hx : (Pi.single j 1 : V4) ∈ Wc 1 := by
        intro i' hi'
        have hne : i' ≠ j := by
          intro heq
          rw [heq] at hi'
          omega
        exact Pi.single_eq_of_ne hne _
      have hmem := (h _).1 hx i hi
      rw [Matrix.mulVec_single_one] at hmem
      exact hmem
    exact ⟨key 0 (by decide) 2 (by decide), key 1 (by decide) 2 (by decide),
      key 0 (by decide) 3 (by decide), key 1 (by decide) 3 (by decide)⟩
  · intro h x
    exact ⟨mulVec_mem_Wc_one h, fun hx => by
      have := mulVec_mem_Wc_one (LL_inv h) hx
      rwa [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at this⟩


local instance instModuleV4 :
    @Module (ZMod 2) V4 _ (@AddCommGroup.toAddCommMonoid V4 Pi.addCommGroup) :=
  Pi.module _ _ _

theorem D_char (hns : ¬ Group.IsSolvable SL4) {D : Subgroup SL4} (hUD : upperSub ≤ D)
    (hDs : Group.IsSolvable ↥D) (h9 : 9 ∣ Nat.card D) :
    (∀ g : SL4, g ∈ D ↔ LL (g : M4)) ∧ Nat.card D = 576 := by
  let e : V4 ≃ₗ[ZMod 2] V4 := LinearEquiv.refl (ZMod 2) V4
  have hV : Module.finrank (ZMod 2) V4 = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hfin : ∀ k : ℕ, k ≤ 2 → Module.finrank (ZMod 2) (flagI e k) = k + 1 :=
    fun k hk => finrank_flagI e k hk
  have hmono : ∀ k k' : ℕ, k ≤ k' → flagI e k ≤ flagI e k' :=
    fun k k' h => Submodule.map_mono (Wc_le h)
  have hlt01 : flagI e 0 < flagI e 1 :=
    flag_lt_of_le_finrank_ne (hmono 0 1 (by norm_num))
      (by rw [hfin 0 (by norm_num), hfin 1 (by norm_num)]; norm_num)
  have hlt12 : flagI e 1 < flagI e 2 :=
    flag_lt_of_le_finrank_ne (hmono 1 2 (by norm_num))
      (by rw [hfin 1 (by norm_num), hfin 2 (by norm_num)]; norm_num)
  have hF1 := factF1_holds
  unfold FactF1 at hF1
  obtain ⟨i35, i15p, i15P, i105a, i105b, i105c, i315, hover⟩ :=
    hF1.2 V4 hV (flagI e 0) (flagI e 1) (flagI e 2) (hfin 0 (by norm_num)) (hfin 1 (by norm_num))
      (hfin 2 (by norm_num)) hlt01 hlt12
  have hB : stabS (flagI e 0) ⊓ stabS (flagI e 1) ⊓ stabS (flagI e 2) ≤ D.map (PsiE e) := by
    have := map_upperSub_eq_Bstd e
    unfold Bstd at this
    rw [← this]
    exact Subgroup.map_mono hUD
  have hmul : Nat.card D * (D.map (PsiE e)).index = 20160 := by
    have := Subgroup.card_mul_index (D.map (PsiE e))
    rwa [Subgroup.card_map_of_injective (PsiE_injective e), natCard_GL_four hV] at this
  have hSL : Nat.card SL4 = 20160 := by
    rw [Nat.card_congr (Equiv.ofBijective (PsiE e) (PsiE_bijective e))]
    exact natCard_GL_four hV
  rcases hover _ hB with h | h | h | h | h | h | h | h
  · exfalso
    rw [h, Subgroup.index_top] at hmul
    have hDtop : D = ⊤ := (Subgroup.card_eq_iff_eq_top D).1 (by rw [hSL]; omega)
    subst hDtop
    haveI := hDs
    exact hns (solvable_of_solvable_injective
      (f := (Subgroup.topEquiv (G := SL4)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := SL4)).symm.injective)
  · exfalso
    rw [h, i15p] at hmul
    omega
  · rw [h, i35] at hmul
    have h576 : Nat.card D = 576 := by omega
    refine ⟨fun g => ?_, h576⟩
    rw [← Subgroup.mem_map_iff_mem (PsiE_injective e), h]
    exact (PsiE_mem_stabS_flagI_iff e g 1).trans (stab_Wc_one_iff g)
  · exfalso
    rw [h, i15P] at hmul
    omega
  · exfalso
    rw [h, i105a] at hmul
    omega
  · exfalso
    rw [h, i105b] at hmul
    omega
  · exfalso
    rw [h, i105c] at hmul
    omega
  · exfalso
    rw [h, i315] at hmul
    omega


theorem card_SL4 : Nat.card SL4 = 20160 := by
  have hV : Module.finrank (ZMod 2) V4 = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [Nat.card_congr (Equiv.ofBijective (PsiE (LinearEquiv.refl (ZMod 2) V4))
    (PsiE_bijective (LinearEquiv.refl (ZMod 2) V4)))]
  exact natCard_GL_four hV

theorem card_upperSub : Nat.card upperSub = 64 := by
  let e : V4 ≃ₗ[ZMod 2] V4 := LinearEquiv.refl (ZMod 2) V4
  have hV : Module.finrank (ZMod 2) V4 = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hfin : ∀ k : ℕ, k ≤ 2 → Module.finrank (ZMod 2) (flagI e k) = k + 1 :=
    fun k hk => finrank_flagI e k hk
  have hmono : ∀ k k' : ℕ, k ≤ k' → flagI e k ≤ flagI e k' :=
    fun k k' h => Submodule.map_mono (Wc_le h)
  have h64 := natCard_std_flag hV (hfin 0 (by norm_num)) (hfin 1 (by norm_num))
    (hfin 2 (by norm_num)) (hmono 0 1 (by norm_num)) (hmono 1 2 (by norm_num))
  have hB := map_upperSub_eq_Bstd e
  unfold Bstd at hB
  rw [← Subgroup.card_map_of_injective (PsiE_injective e), hB]
  exact h64

theorem exists_conj_upperSub {U : Subgroup SL4} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) :
    ∃ c : SL4, U = upperSub.map (MulAut.conj c).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at hU
  obtain ⟨-, hp, hodd⟩ := hU
  have hcU : Nat.card U = 64 := natCard_of_two_group_odd_index card_SL4 hp hodd
  have hK : IsPGroup 2 upperSub := (IsPGroup.iff_card (p := 2)).2 ⟨6, card_upperSub.trans (by norm_num)⟩
  exact exists_conj_of_card_64 card_SL4 hp hK hcU card_upperSub

end K21dA8Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
