module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem canonLabel_uni_of_ggLabelRigidInput (hRig : GGLabelRigidInput) {J : Type} [Group J] [Finite J]
    {labJ : GLALabel} {a m : ℕ} {E : Type} [Field E] [Finite E] (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (hτ'm : ∀ x, τ' x = x ^ (2 ^ m)) (hE : Nat.card E = (2 ^ m) ^ 2)
    (ha : 3 ≤ a) (hJ : HasLabel J (fun l : GLALabel => l = labJ))
    (φ : J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) :
    canonLabel labJ = ⟨.twA, a - 1, m⟩ := by
  obtain ⟨hlab, hs, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  haveI := hs
  have hm : 1 ≤ m := by
    by_contra hm0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show m = 0 by omega] at h2
    norm_num at h2
  by_cases h31 : a = 3 ∧ m = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := h31
    haveI := isSolvable_quot_heldSU_three_two τ' hτ' (fun x => by simpa using hτ'm x)
      (by simpa using hE)
    exact not_isSolvable_quot_center
      (solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
  · have ham : (a, 2 ^ m) ≠ (3, 2) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
    obtain ⟨ψ⟩ := nonempty_quot_heldSU_equiv_statedProj uniScalar_holds τ' hτ' hτ'm hE ha ham
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hiso : GGLabelIso labJ ⟨.twA, b, m⟩ :=
      hRig labJ ⟨.twA, b, m⟩ (J ⧸ Subgroup.center J) hlab
        (largeEvenInLambda2_twA hm (by omega) fun hb => by omega) hhas
        (ggHasLabel_twA hE (φ.trans ψ))
    rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso]
    rfl

section Certificates


theorem canonLabel_uni_holds {J : Type} [Group J] [Finite J] {labJ : GLALabel} {a m : ℕ} {E : Type}
    [Field E] [Finite E] (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x) (hτ'm : ∀ x, τ' x = x ^ (2 ^ m))
    (hE : Nat.card E = (2 ^ m) ^ 2) (ha : 3 ≤ a) (hJ : HasLabel J (fun l : GLALabel => l = labJ))
    (φ : J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) :
    canonLabel labJ = ⟨.twA, a - 1, m⟩ :=
  canonLabel_uni_of_ggLabelRigidInput ggLabelRigidInput_holds τ' hτ' hτ'm hE ha hJ φ

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni

end
