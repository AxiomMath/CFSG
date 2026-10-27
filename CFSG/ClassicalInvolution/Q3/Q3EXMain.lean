module

public import CFSG.ClassicalInvolution.Q3.Q3EXModel
public import CFSG.ClassicalInvolution.Q3.Q3EXStar
public import CFSG.ClassicalInvolution.Q3.Q3EXD4Local

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

@[expose] def ShapeExoticG2D43 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  1 ≤ a ∧ (t = .G2 ∨ t = .trialityD4) ∧ StatedLieAdmissible t n 3 1

@[expose] def ShapeExoticD43 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 4 ∧ t = .POmegaPlus ∧ n = 4

@[expose] def ShapeExoticOrth3 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  RouteD.Exotic.ShapeSingleOrth a t n ∧ StatedLieAdmissible t n 3 1

theorem shapeTable_of_twinD {a : ℕ} {t : StatedLieTag} {n : ℕ} (h : CoreAssembly.ShapeTwinD a t n) :
    CoreAssembly.ShapeTable a t n := by
  unfold CoreAssembly.ShapeTable
  tauto


theorem shapePiece3_exc (h3 : OddThreeFreeInput) {t : StatedLieTag} {n : ℕ}
    (h : RouteD.Exotic.ShapeSingleExc 1 t n) (hadm : StatedLieAdmissible t n 3 1) :
    ShapePiece3 1 (CompData.model t n) := by
  obtain ⟨-, ht⟩ := h
  have hn : n = 0 := by
    rcases ht with rfl | rfl | rfl | rfl <;> exact hadm.2.2
  subst hn
  rcases ht with rfl | rfl | rfl | rfl
  · exact shapePiece3_F4 h3
  · exact shapePiece3_E6 h3
  · exact shapePiece3_E8 h3
  · exact shapePiece3_twistedE6 h3

section Main

theorem shapePiece3_exotic_of_residuals (h3 : OddThreeFreeInput)
    (hg : RowPiece3 ShapeExoticG2D43) (hd : RowPiece3 ShapeExoticD43)
    (ho : RowPiece3 ShapeExoticOrth3)
    {a : ℕ} {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (ha : 1 ≤ a) (hnt : ¬ ShapeTable3 a t n) :
    ShapePiece3 a (CompData.model t n) := by
  have hnA1 := not_psl_two_of_admissible3 hadm
  by_cases hG : t = .G2 ∨ t = .trialityD4
  · exact hg a t n ⟨ha, hG, hadm⟩
  · push Not at hG
    by_cases ha1 : a = 1
    · subst ha1
      have hex : CoreAssembly.ShapeExotic 1 t n :=
        ⟨ha, hnA1, fun h => hnt (Or.inl h)⟩
      rcases RouteD.Exotic.shapeSingle_cases hfund hadm ⟨hex, rfl, hG.1, hG.2⟩ with
        h' | h' | h'
      · exact absurd (Or.inr h') hnt
      · exact ho 1 t n ⟨h', hadm⟩
      · exact shapePiece3_exc h3 h' hadm
    · have ha2 : 2 ≤ a := by omega
      intro G _ _ _ hnab K z hR hshape
      have hmt := EX.exotic_modelTwinClass3 hR (h3 G K z hR) hfund hadm hG.1 hG.2 hshape
      rcases EX.mfTwin3 t n a hfund hG.1 hG.2 hadm hnA1 ha2 hmt with htab | ⟨ht, hn, ha4⟩
      · exact absurd (Or.inl htab) hnt
      · subst ht hn
        have ha34 : a = 3 ∨ a = 4 := by
          have h2 : a ≠ 2 := fun h2 => hnt (Or.inl (shapeTable_of_twinD ⟨h2, rfl, le_rfl⟩))
          omega
        rcases ha34 with rfl | rfl
        · exact shapePiece3_d4_three h3 G hnab K z hR hshape
        · exact hd 4 .POmegaPlus 4 ⟨rfl, rfl, rfl⟩ G hnab K z hR hshape

theorem pieceExotic₃_of_residuals (h3 : OddThreeFreeInput) (hrows : RowPiece3 ShapeTable3)
    (hA1 : PieceAllA1₃) (hM11 : PieceM11₃) (hg : RowPiece3 ShapeExoticG2D43)
    (hd : RowPiece3 ShapeExoticD43) (ho : RowPiece3 ShapeExoticOrth3) : PieceExotic₃ := by
  intro a t n ha hnt G _ _ _ hnab K z hR hshape
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := hshape
  have hvalid := D.valid i₁
  rw [hk] at hvalid
  rcases hvalid with ⟨t', n', hfund', hadm', heq⟩ | heq | heq
  · have hk' : D.kind i₁ = CompData.model t' n' := hk.trans heq
    by_cases ht' : ShapeTable3 a t' n'
    · exact hrows a t' n' ht' G hnab K z hR ⟨ι, hι, D, hcard, i₁, hk', hrest⟩
    · have hnt' : ¬ ShapeTable3 a t' n' := ht'
      exact shapePiece3_exotic_of_residuals h3 hg hd ho hfund' hadm' ha hnt' G hnab K z hR
        ⟨ι, hι, D, hcard, i₁, hk', hrest⟩
  · exact hA1 a G hnab K z hR ⟨ι, hι, D, hcard, i₁, hk.trans heq, hrest⟩
  · exact hM11 a G hnab K z hR ⟨ι, hι, D, hcard, i₁, hk.trans heq, hrest⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3W
