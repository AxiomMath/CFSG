module

public import CFSG.ClassicalInvolution.Q3.Q3MTKind
public import CFSG.ClassicalInvolution.Q3.Q3MTStar
public import CFSG.ClassicalInvolution.Q3.Q3MTModel5
public import CFSG.ClassicalInvolution.Uniform.U5Three2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallC
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallB
public import CFSG.ClassicalInvolution.Q3.Q3MTDatum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.Assembly CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups


theorem smallShape3_psl3 : SmallShape3 .PSL 3 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.PSL ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hE : Disconnected.DEdgeless Ω :=
    ih8ThreeU_proved G Ω hΩ htrans .PSL 3 1 ⟨M⟩ (Or.inl ⟨rfl, rfl⟩)
  rw [show muKind false .PSL 3 = .z2 by simp [muKind]]
  have hsub := starSubset3 M hΩ hG2 hD4 fun R hR S hS hJ =>
    star_commutes_lin3 M hΩ hG2 hD4 (stdDich3Lin_psl M.admissible) hR hS hJ
  intro K hK
  refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
  exact hE K hK J hJ.1 (Or.inl (hsub K hK hJ))

theorem smallShape3_psl4 : SmallShape3 .PSL 4 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.PSL ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .PSL 4 = .e4 by simp [muKind]]
  refine ⟨starSubset3 M hΩ hG2 hD4 fun R hR S hS hJ =>
    star_commutes_lin3 M hΩ hG2 hD4 (stdDich3Lin_psl M.admissible) hR hS hJ,
    noTriangle3 M hΩ hG2 hD4 ?_,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_psl4 M.admissible)⟩
  intro A hA B hB S hS hAB hAS hBS cAB cAS cBS
  exact noThree_psl4 (by norm_num : (3 : ℕ) ≠ 2) (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS)
    hAB hAS hBS cAB cAS cBS

theorem smallShape3_psl5 : SmallShape3 .PSL 5 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.PSL ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .PSL 5 = .e4 by simp [muKind]]
  refine ⟨starSubset3 M hΩ hG2 hD4 fun R hR S hS hJ =>
    star_commutes_lin3 M hΩ hG2 hD4 (stdDich3Lin_psl M.admissible) hR hS hJ,
    noTriangle3 M hΩ hG2 hD4 ?_, edge_of_commuting3 M hΩ hne hG2 hD4 ?_⟩
  · intro A hA B hB S hS hAB hAS hBS cAB cAS cBS
    exact noThree_psl5 (by norm_num : (3 : ℕ) ≠ 2) (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS)
      hAB hAS hBS cAB cAS cBS
  · exact exists_commuting_of_orth_nodes M.isFundTag M.admissible
      (i := (⟨0, by omega⟩ : Fin 4)) (j := (⟨2, by omega⟩ : Fin 4)) trivial trivial
      (by
        show CartanMatrix.A 4 _ _ = 0
        simp [CartanMatrix.A])

theorem smallShape3_psp2 : SmallShape3 .PSp 2 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.PSp ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .PSp 2 = .e4 by simp [muKind]]
  refine ⟨starSubset3 M hΩ hG2 hD4 fun R hR S hS hJ =>
    star_commutes_triv3 M hΩ hG2 hD4 (stdDich3Triv_psp M.admissible) hR hS hJ,
    noTriangle3 M hΩ hG2 hD4 ?_,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_sp4 M.admissible)⟩
  intro A hA B hB S hS hAB hAS hBS cAB cAS cBS
  exact noThree_psp2 (by norm_num : (3 : ℕ) ≠ 2) M.admissible (M.cls_sub hA) (M.cls_sub hB)
    (M.cls_sub hS) hAB hAS hBS cAB cAS cBS

theorem smallShape3_psu3 : SmallShape3 .PSU 3 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.PSU ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .PSU 3 = .s3 by simp [muKind]]
  refine ⟨ih8ThreeU_proved G Ω hΩ htrans .PSU 3 1 ⟨M⟩ (Or.inr ⟨rfl, rfl⟩), ?_⟩
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_psu (by norm_num : (3 : ℕ) ≠ 2) hne
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  rcases hadj.2 with h | h
  · exact ⟨R₁.map M.ψ, M.map_mem hR₁, _, h⟩
  · exact ⟨R₂.map M.ψ, M.map_mem hR₂, _, h⟩

theorem smallShape3_psu4 : SmallShape3 .PSU 4 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : LowTwoRank.StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.PSU ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  rw [show muKind false .PSU 4 = .s4 by simp [muKind]]
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS hAB hAS hBS cAB cAS =>
    matching_psu4 (by norm_num : (3 : ℕ) ≠ 2) M.admissible (M.cls_sub hA) (M.cls_sub hB)
      (M.cls_sub hS) hAB hAS hBS cAB cAS
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_psu (by norm_num : (3 : ℕ) ≠ 2) hne
  obtain ⟨-, hnc⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  have hadj := dstarAdj_unitary3 M hΩ hG2 hD4 hR₁ hR₂ hW
  exact ⟨matching3 M hΩ hG2 hD4 hMatch,
    edge_of_commuting3 M hΩ hne hG2 hD4 (exists_commuting_small_su4 M.admissible),
    _, M.map_mem hR₁, dComp_ne3 M hΩ hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

end CFSG.ClassicalInvolution.Q3.Q3MT
