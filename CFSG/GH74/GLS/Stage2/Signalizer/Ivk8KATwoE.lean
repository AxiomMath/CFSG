module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBFix
public import CFSG.GH74.KGroups.PSLN
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.RankThree.PartTwo.KFacts.L34

theorem unitaryFix_of_card_seventytwo {Y : Type} [Group Y] (hF : LieModel Y .PSL 3 2 2)
    {α : MulAut Y} (hα2 : α * α = 1) (hinn : α ∉ innSub Y) (hcard : Nat.card ↥(fixSub α) = 72) :
    UnitaryFix α := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k := GaloisField 2 2
  have hk : Nat.card k = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hfin := LinearFieldFour.finite_of_card_eq_four hk
  have hchar := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨φ0⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := k) 3 2 2 (by norm_num) hk hF
  let φ : Y ≃* projectiveSL 3 k :=
    φ0.trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 k)).symm
  set αB : MulAut (projectiveSL 3 k) := MulAut.congr φ α with hαB
  have hαB2 : αB * αB = 1 := by rw [hαB, ← map_mul, hα2, map_one]
  have hαBinn : αB ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
    rintro ⟨g, hg⟩
    apply hinn
    refine ⟨φ.symm g, (MulAut.congr φ).injective ?_⟩
    have : MulAut.congr φ (MulAut.conj (φ.symm g)) = MulAut.conj g := by
      ext x
      simp [MulAut.congr_apply]
    rw [this, hg]
  have hfixB : (fixSub α).map φ.toMonoidHom = GL3TwoFixedModel.autFixed αB := fixSub_congr φ α
  have hcardB : Nat.card ↥(GL3TwoFixedModel.autFixed αB) = 72 := by
    rw [← hfixB, Nat.card_congr (Subgroup.equivMapOfInjective _ _ φ.injective).toEquiv.symm]
    exact hcard
  rcases involution_cases_card hk hσ hαB2 with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨⟨H, hH⟩, -⟩
  · exact absurd h hαBinn
  · rw [hcardB] at h
    omega
  · rw [hcardB] at h
    omega
  · obtain ⟨eU⟩ := nonempty_autFixed_betaAut_equiv hk hσ
    have h3 : GL3TwoFixedModel.autFixed αB =
        (GL3TwoFixedModel.autFixed (betaAut (frobeniusEquiv k 2))).map
          (conjAut 3 k H).toMonoidHom := by
      rw [hH]
      exact autFixed_conj _ _
    let e1 : ↥(fixSub α) ≃* ↥((fixSub α).map φ.toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ φ.injective
    let e2 : ↥((GL3TwoFixedModel.autFixed (betaAut (frobeniusEquiv k 2))).map
          (conjAut 3 k H).toMonoidHom) ≃*
        ↥(GL3TwoFixedModel.autFixed (betaAut (frobeniusEquiv k 2))) :=
      (Subgroup.equivMapOfInjective _ _ (conjAut 3 k H).injective).symm
    have e3 := CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv
      (unitaryFieldData_of_card hk) (n := 3) (by norm_num)
    exact ⟨k, inferInstance, inferInstance, hk, ⟨((e1.trans (MulEquiv.subgroupCongr
      (hfixB.trans h3))).trans e2).trans (eU.trans e3)⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
