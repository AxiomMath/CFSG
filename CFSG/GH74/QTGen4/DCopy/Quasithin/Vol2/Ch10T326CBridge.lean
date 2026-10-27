module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326S
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLieModel
public import CFSG.Quasithin.Vol2.Ch10T326CBridge

public section
namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

private theorem twoResidual_eq_oTwoUpper_c {D : Type*} [Group D] [Finite D]
    (X : Subgroup D) : twoResidual X = oTwoUpper X := by
  unfold twoResidual
  exact le_antisymm (iInf₂_le _ ⟨oTwoUpper_le X, le_normalizer_oTwoUpper X,
    fun _ hx => exists_pow_mem_oTwoUpper X hx⟩)
    (le_iInf₂ fun _ hN => oTwoUpper_le_of_pow_mem hN.2.2)

private theorem nonempty_mulEquiv_SL32_of_lieModel_c {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Blueprint.LieModel.nonempty_mulEquiv_SL_three_two h

theorem tmpL6_3_2_6C_of_stmt3_2_6C_F4 (h326 : Stmt3_2_6C_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
      (∃ _ : IsMulCommutative ↥(fsuV T I),
        qhatOf (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I)) ≤ 2) ∧
      (∃ _ : IsMulCommutative ↥(fsuVM T L I),
        qhatOf (V := ↥(fsuVM T L I)) (autOn (fsuM T L) (fsuVM T L I)) ≤ 2) ∧
      ((∃ _ : IsMulCommutative ↥(fsuV T I), I = fsuV T I ∧ fsuV T I = fsuVM T L I ∧
          ((∃ n : ℕ, Row711OmegaPlus T L I n) ∨ Row711L3Wreath T L I)) ∨
        Concl326ThreeC T L I) := by
  intro G _ _ T L I hfsu hlt
  obtain ⟨⟨hcV, hqV⟩, hcVM, hqVM, hcases⟩ := h326 G T L I hfsu hlt.ne
  refine ⟨⟨hcV, hqV⟩, ⟨hcVM, hqVM⟩, ?_⟩
  rcases hcases with ⟨n, K, _, _, hcard, hlie, hV0, hVVM, hreal⟩ | ⟨-, hV0, hVVM, hreal⟩ | h3
  ·
    refine Or.inl ⟨hcV, hV0, hVVM, Or.inl ⟨n, hlt, two_le_of_lieModel_psl_two hlie, K,
      inferInstance, inferInstance, hcard, ?_⟩⟩
    rw [← tensorNatModel_eq]
    exact realizesMod_of_eq hVVM _ _ hreal
  ·
    refine Or.inl ⟨hcV, hV0, hVVM, Or.inr ⟨hlt, ?_⟩⟩
    rw [← tensorNatModel_eq]
    exact realizesMod_of_eq hVVM _ _ hreal
  ·
    obtain ⟨⟨ha, hb, hb'⟩, hc⟩ := h3
    refine Or.inr ?_
    rcases hc with ⟨x, hx, hU, hVVM⟩ | ⟨⟨e⟩, hVVM, ⟨s, hsT, hsn⟩, ⟨x, hx, hall⟩, hcard⟩ |
      hiii | hiv
    ·
      refine Or.inl ⟨x, hx, ?_⟩
      rw [concl326Three_iff, fsuV_conjugate hx, fsuVM_conjugate hx]
      exact ⟨hcVM, isElemAbelian_fsuVM hfsu, fsuVM_le_normalizer_fsuCVM, ha, hb, hb',
        Or.inl ⟨hU, hVVM⟩⟩
    ·
      refine Or.inl ⟨x, hx, ?_⟩
      rw [concl326Three_iff, fsuV_conjugate hx, fsuVM_conjugate hx]
      obtain ⟨hU, hUs⟩ := hall s hsT hsn
      exact ⟨hcVM, isElemAbelian_fsuVM hfsu, fsuVM_le_normalizer_fsuCVM, ha, hb, hb',
        Or.inr (Or.inl ⟨⟨e.trans (MulAut.congr
          (specialLinearGroupEquivStatedSL 3 (ZMod 2))).symm⟩, hVVM,
          (card_conjugate I x).trans hcard, s, hsT.1, hsT.2, hsn, hU, hUs⟩)⟩
    ·
      refine Or.inl ⟨1, T.one_mem, ?_⟩
      rw [SecA.conjugate_one]
      obtain ⟨_, hlie, hsum, h5⟩ := hiii
      refine ⟨hcVM, isElemAbelian_fsuVM hfsu, fsuVM_le_normalizer_fsuCVM, ha, hb, hb',
        Or.inr (Or.inr ⟨nonempty_mulEquiv_SL32_of_lieModel_c hlie, hsum, ?_⟩)⟩
      have : Finite (MulAut ↥(fsuVM T L I)) := MulEquiv.finite_left
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      rw [twoResidual_eq_oTwoUpper_c]
      rcases h5 with h5 | ⟨h25, hexp⟩
      · exact Or.inl ⟨mulEquivOfPrimeCardEq h5 (by simp)⟩
      · exact Or.inr (nonempty_mulEquiv_zmod_prod (p := 5) (by rw [h25]; norm_num)
          (fun x => Subtype.ext (by simpa using hexp x.1 x.2)))
    ·
      exact Or.inr ⟨hcVM, hiv⟩

end CFSG.Quasithin.Vol2.Ch10
