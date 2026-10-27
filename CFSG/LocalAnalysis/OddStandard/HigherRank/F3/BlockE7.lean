module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Member
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeE7Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7Model

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ClassicalInvolution.ModelFacts

theorem blockData_e7sc : BlockData (E7sc 3 1) := by
  have hQ7 : IsQuasisimple (E7sc 3 1) :=
    LieType.CurtisTits.isQuasisimple_e7 (GaloisField 3 1)
  have hZ : Nat.card ↥(center (E7sc 3 1)) = 2 :=
    ComponentClassification.HarrisLit.T1.P54.E7Row.card_center_E7sc (p := 3) (f := 1)
      (by norm_num) one_ne_zero
  refine ⟨hQ7, ⟨1, le_rfl, by rw [hZ, pow_one]⟩, ?_, ?_⟩
  · refine ⟨.E7, 0, ?_, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    refine Or.inr (Or.inl ⟨rfl, by decide, ?_, ?_⟩)
    · exact ⟨Nat.prime_three, le_rfl, rfl⟩
    · exact LieType.CurtisTits.untwistedChevalleyModel_of_surjective hQ7
        (GaloisField.card 3 1 one_ne_zero)
        (LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 3 1))
        (LieType.Steinberg.Isogeny.e7Isogeny_surjective _)
        (LieType.CurtisTits.exists_ne_one_of_surjective_adjointGroup (by decide)
          (LieType.Steinberg.Isogeny.e7Isogeny_surjective _))
        (MulEquiv.refl _)
  · have hM : Nat.card (Open.griessHopfMultiplier (E7sc 3 1 ⧸ center (E7sc 3 1))) = 2 := by
      obtain ⟨eQ⟩ := LieType.CurtisTits.adjointQuotientEquiv_of_surjective hQ7
        (LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 3 1))
        (LieType.Steinberg.Isogeny.e7Isogeny_surjective _)
        (LieType.CurtisTits.exists_ne_one_of_surjective_adjointGroup (by decide)
          (LieType.Steinberg.Isogeny.e7Isogeny_surjective _))
      obtain ⟨-, ⟨eM⟩⟩ := LieType.Steinberg.CentralExt.FieldThree.e7_three_hopfMultiplier
        (K := GaloisField 3 1) (by rw [GaloisField.card 3 1 one_ne_zero, pow_one])
      have hg : Nat.gcd 2 (Nat.card (GaloisField 3 1) - 1) = 2 := by
        rw [GaloisField.card 3 1 one_ne_zero, pow_one]
        norm_num
      have h1 : Nat.card (Open.griessHopfMultiplier (E7sc 3 1 ⧸ center (E7sc 3 1))) =
          Nat.card (Open.griessHopfMultiplier
            (CFSG.Blueprint.AdjointQuotient .E7 (GaloisField 3 1))) :=
        Nat.card_congr
          (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eQ).toEquiv
      rw [h1, Nat.card_congr eM.toEquiv, hg]
      simp
    rw [hM, hZ]

end CFSG.OddStandard.HigherRank.F3
