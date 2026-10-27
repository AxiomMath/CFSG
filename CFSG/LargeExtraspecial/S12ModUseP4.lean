module

public import CFSG.LargeExtraspecial.S12ModUseAsm
public import CFSG.LargeExtraspecial.GLW4Cent
public import CFSG.LargeExtraspecial.S12InspP4R3
public import CFSG.LargeExtraspecial.S12InspP4Rank
public import CFSG.LargeExtraspecial.S14LitFischer
public import CFSG.LargeExtraspecial.S14NQIrred
public import CFSG.LargeExtraspecial.S14NQSix
public import CFSG.LargeExtraspecial.TI75Trans
public import CFSG.Timmesfeld.ARSInputThm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.Open CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem insp4PlusInput_of_residualN (hF : DW.DW2FieldInput) (h : Insp4PlusResidual) :
    Insp4PlusInput := by
  intro G _ _ _ S g t haQ hne hw hP hE hsec ht htA hS hred hcls
  have h2 : ∀ k, 2 ^ k ∣ Nat.card (S.Xbar12 g) → k ≤ 7 := fun _ hk =>
    Setting.le_seven_of_two_pow_dvd_card_Xbar12 hP hk
  have h20 := Setting.dvd_card_Xbar12_mul_card_outer_of_section hS hsec
  have hsx : 4 ∣ Nat.card (S.Xbar12 g) → ¬ 20160 ∣ Nat.card (S.Xbar12 g) → False :=
    fun h4 h20' => Setting.false_of_section hP hsec h4 h20'
  rcases hcls with ⟨hnd, hout⟩ | ⟨hdeg, hfis⟩
  · rcases S12Insp4P.outcome_cases hout h2 h20 with hL | hL | hJ
    · exact (Setting.false_of_lieModel_fieldF hF ht htA hS (τ := .PSL) (n := 3) (f := 2) le_rfl
        (Or.inl ⟨rfl, le_rfl⟩) hL).elim
    · exact h G S g t haQ hne hw hP hE hsec ht htA hS hred (Or.inl ⟨hnd, hL⟩)
    · exact (Setting.false_of_isSporadic_J2 ht htA hS hJ).elim
  refine h G S g t haQ hne hw hP hE hsec ht htA hS hred (Or.inr ⟨hdeg, ?_⟩)
  rcases hfis with ⟨m, hm, φ, hφ⟩ | ⟨m, hm, b, halt, hnd, hmod⟩ | hO | hU | hF3 | hFi | hFi | hFi
  · by_cases h35 : m = 3 ∨ m = 5
    · exact (S12Insp4P.false_of_perm_three_five h35 φ h20).elim
    by_cases h7 : 7 ≤ m
    · exact (Setting.false_of_perm_ge_seven haQ hne (by omega) ht htA h7 φ hφ).elim
    obtain rfl : m = 6 := by omega
    exact (hsx (by rw [S12Insp4.card_of_perm φ]; decide)
      (by rw [S12Insp4.card_of_perm φ]; decide)).elim
  · by_cases hm3 : 3 ≤ m
    · exact (S12Insp4.false_of_sp hm3 halt hnd hmod h2).elim
    obtain rfl : m = 2 := by omega
    obtain ⟨ψ⟩ := S12Insp4.nonempty_mulEquiv_perm_six_of_sp halt hnd hmod
    exact (hsx (by rw [S12Insp4.card_of_perm ψ]; decide)
      (by rw [S12Insp4.card_of_perm ψ]; decide)).elim
  · obtain ⟨m, hm, Q, hnd, hm2, hmod⟩ := hO
    by_cases hm4 : 4 ≤ m
    · exact (S12Insp4.false_of_orth hm4 hnd hmod h2).elim
    have hcX := S12Insp4P.card_eq_card_orthogonalGroup_of_model hmod
    rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
    · have hc := S12Insp4P.card_orthogonalGroup_minus_four hnd (hm2 rfl)
      exact (hsx (by rw [hcX, hc]; decide) (by rw [hcX, hc]; decide)).elim
    · rcases S12Insp4P.card_orthogonalGroup_six hnd with hc | hc
      · exact Or.inl ⟨Q, hnd, S12Insp4P.isPlus_of_card_orthogonalGroup hnd hc, hmod⟩
      · exact (hsx (by rw [hcX, hc]; decide) (by rw [hcX, hc]; decide)).elim
  · obtain ⟨m, hm, hmod⟩ := hU
    exact Or.inr ⟨m, hm, Setting.le_five_of_psu hP ht htA hm hmod, hmod⟩
  · obtain ⟨m, hm, f, hsymm, hnd, hmod⟩ := hF3
    by_cases hm6 : 6 ≤ m
    · exact (Setting.false_of_reflGroup_ge_six hE hm6 hsymm hnd hmod).elim
    obtain rfl : m = 5 := by omega
    exact (Setting.false_of_reflGroup_five hP hsec hsymm hnd hmod).elim
  · exact (S12Insp4.false_of_fi h2 (Or.inl hFi.1)).elim
  · exact (S12Insp4.false_of_fi h2 (Or.inr (Or.inl hFi.1))).elim
  · exact (S12Insp4.false_of_fi h2 (Or.inr (Or.inr hFi.1))).elim

namespace GLW4

open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

theorem centPlus6Stmt_of_inputs_narrowN
    (hTIs : CFSG.CGT.Timmesfeld75.SimpleCaseStmt)
    (hTI215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hDW : DW.DW2OutInspectionInputN)
    (hInsp : Insp4PlusResidual) (hFS : FSmith1977cOmegaInput) (hCE : CentralExtInput.{0}) :
    CentPlus6Stmt :=
  centPlus6Stmt_of rootInvolutionComponentsInput CFSG.Timmesfeld.arsInput
    S12Tri.fischerTrialityInput s12FischerStatement (insp4PlusInput_of_residualN hDW.field hInsp)
    (timmesfeld36Input_of hFS)
    SL4Mod.s12SL4ModuleInput (TI75.weaklyClosedTITransitive_of_inputs hTIs hTI215) hCE
    (nqIrredStmt_of hCE) (nqPlus6Stmt_of hCE)

end GLW4

end CFSG.LargeExtraspecial
