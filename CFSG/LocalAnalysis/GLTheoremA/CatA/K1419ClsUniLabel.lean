module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem k1419ClsUniLabel (hRig : CFSG.StandardType.GGLabelRigidInput) {X : Type} [Group X] [Finite X]
    {n : ℕ}
    (hlab : (HasLabel X (fun l : GLALabel => l = ⟨.A, 2, n⟩) ∧ (n % 6 = 2 ∨ n % 6 = 4)) ∨
      (HasLabel X (fun l : GLALabel => l = ⟨.twA, 2, n⟩) ∧ (n % 6 = 1 ∨ n % 6 = 5)))
    {a m : ℕ} {E : Type} [Field E] [Finite E] (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (ha : 2 ≤ a) (hτ'm : ∀ x, τ' x = x ^ 2 ^ m) (hE : Nat.card E = (2 ^ m) ^ 2)
    (he : Nonempty (X ⧸ Subgroup.center X ≃*
      heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) :
    a = 3 ∧ m = n ∧ (n % 6 = 1 ∨ n % 6 = 5) := by
  obtain ⟨e⟩ := he
  have hkey : ∀ (labJ : GLALabel), HasLabel X (fun l : GLALabel => l = labJ) →
      (a = 2 ∧ canonLabel labJ = ⟨.A, 1, m⟩) ∨
        (3 ≤ a ∧ canonLabel labJ = ⟨.twA, a - 1, m⟩) := by
    intro labJ hJ
    obtain ⟨hlam, hs, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
    haveI := hs
    have hm : 1 ≤ m := by
      by_contra hm0
      have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
      rw [hE, show m = 0 by omega] at h2
      norm_num at h2
    rcases Nat.lt_or_ge a 3 with ha3 | ha3
    · obtain rfl : a = 2 := by omega
      left
      refine ⟨rfl, ?_⟩
      obtain ⟨k, _, _, hk, ⟨ψ⟩⟩ := Y10GInnUni.exists_quot_heldSU_two_equiv_psl τ' hτ' hτ'm hE
      simpa using Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig X labJ 2 m k le_rfl hk hJ
        ⟨e.trans ψ⟩
    · right
      refine ⟨ha3, ?_⟩
      by_cases h31 : a = 3 ∧ m = 1
      · obtain ⟨rfl, rfl⟩ := h31
        exfalso
        haveI := Y10GInnUni.isSolvable_quot_heldSU_three_two τ' hτ'
          (fun x => by simpa using hτ'm x) (by simpa using hE)
        exact Y10GInnUni.not_isSolvable_quot_center
          (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
      · have ham : (a, 2 ^ m) ≠ (3, 2) := by
          intro h
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
        obtain ⟨ψ⟩ := Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
          Y10GInnUni.uniScalar_holds τ' hτ' hτ'm hE ha3 ham
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        have hiso : CFSG.StandardType.GGLabelIso labJ ⟨.twA, b, m⟩ :=
          hRig labJ ⟨.twA, b, m⟩ (X ⧸ Subgroup.center X) hlam
            (Y10GInnUni.largeEvenInLambda2_twA hm (by omega) fun hb => by omega) hhas
            (Y10GInnUni.ggHasLabel_twA hE (e.trans ψ))
        have hc := Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso
        rw [show canonLabel (⟨.twA, b, m⟩ : GLALabel) = ⟨.twA, b, m⟩ from rfl] at hc
        simpa using hc
  rcases hlab with ⟨hJ, _⟩ | ⟨hJ, hmod⟩
  · rcases hkey ⟨.A, 2, n⟩ hJ with ⟨-, hc⟩ | ⟨-, hc⟩
    · rw [show canonLabel (⟨.A, 2, n⟩ : GLALabel) = ⟨.A, 2, n⟩ from rfl] at hc
      have hrank : (2 : ℕ) = 1 := congrArg LargeEvenLabel.rank hc
      omega
    · rw [show canonLabel (⟨.A, 2, n⟩ : GLALabel) = ⟨.A, 2, n⟩ from rfl] at hc
      have htag : LargeEvenLieTag.A = LargeEvenLieTag.twA := congrArg LargeEvenLabel.tag hc
      cases htag
  · rcases hkey ⟨.twA, 2, n⟩ hJ with ⟨-, hc⟩ | ⟨-, hc⟩
    · rw [show canonLabel (⟨.twA, 2, n⟩ : GLALabel) = ⟨.twA, 2, n⟩ from rfl] at hc
      have htag : LargeEvenLieTag.twA = LargeEvenLieTag.A := congrArg LargeEvenLabel.tag hc
      cases htag
    · rw [show canonLabel (⟨.twA, 2, n⟩ : GLALabel) = ⟨.twA, 2, n⟩ from rfl] at hc
      have hrank : (2 : ℕ) = a - 1 := congrArg LargeEvenLabel.rank hc
      have hn : n = m := congrArg LargeEvenLabel.n hc
      exact ⟨by omega, by omega, hmod⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419
