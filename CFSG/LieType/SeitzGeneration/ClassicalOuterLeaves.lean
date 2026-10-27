module

public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.LieType.SeitzGeneration.OuterHeisCoreProof
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLLtProof
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.LieType.SeitzGeneration.RootPairOrthOmega
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlusChar2
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinusChar2
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.ClassicalAssembly
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.LieType.SeitzGeneration.OuterNarrowThree
public import CFSG.LieType.SeitzGeneration.OuterSUCat
public import CFSG.LieType.SeitzGeneration.OuterSpCat

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def SeitzOuterLinearWide : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ¬ NarrowScope p E ∧
    ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q ∧ 2 ≤ m

@[expose] def SeitzOuterUnitaryWide : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ¬ NarrowScope p E ∧ IsUnitaryIndex' d.1 ∧
    ¬ CentralPrimeFree p d.1

@[expose] def SeitzOuterOrthogonalThree : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsOrthogonalIndex d.1 ∧
    ¬ IsDFourIndex d.1

section Assembly


theorem seitzOuterClassical_of_leaves
    (hPlusF2 : SubfieldPairOmegaPlusF2) (hMinusF2 : SubfieldPairOmegaMinusF2)
    (hL : SeitzOuterLinearWide) (hU : SeitzOuterUnitaryWide)
    (hO3 : SeitzOuterOrthogonalThree) : SeitzOuterClassical := by
  have hSL := subfieldPairSLLt
  have hSp := subfieldPairSpOdd subfieldPairSpF2_holds
  have hSU := subfieldPairSUOdd
    (CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds)
  have hOm := subfieldPairOmega_of_char2 (subfieldPairOmegaPlusChar2_of_F2 hPlusF2)
      (subfieldPairOmegaMinusChar2_of_F2 hMinusF2)
  have hOH := outerHeisCore
  have hUH := unitaryHeisCore
  have hUOH := unitaryOuterHeisCore_of_finite_cases HeisSmall.outerB12AtCard_five
      HeisSmall.outerB12AtCard_eight HeisSmall.outerB12AtCard_eleven
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hcl, hD4⟩
  have hrange : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases (isClassicalIndex_iff hrange).1 hcl with ⟨m, q, hd⟩ | ⟨m, q, hd⟩ | hsp | hor
  ·
    have hm1 : 1 ≤ m := by
      have := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange
      subst hd; exact this.1
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · exact seitzOuter_A1 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, q, hd⟩
    · by_cases hs : NarrowScope p E
      · by_cases hx : p = 3 ∧ ∃ q', d = .A 2 q' ∧ 3 ∣ q'.card - 1
        · exact seitzOuter_A2_three hOH ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, ⟨m, q, hd⟩, hx⟩
        · exact seitzOuter_linear hSL ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, ⟨m, q, hd⟩, hx⟩
      · exact hL ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, m, q, hd, hm2⟩
  ·
    by_cases hlift : CentralPrimeFree p d
    · exact seitzOuter_unitary_centralPrimeFree hSU ⟨d, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hout, ⟨m, q, hd⟩, hlift⟩
    · by_cases hs : NarrowScope p E
      · subst hd
        have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange
        have hl : p ∣ q.card + 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
        rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
        · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hl.2
          exact seitzOuter_twistedA2_three hUH hUOH ⟨.twistedA 2 q, hv⟩ p hp hp2 hpd hex E hE hc
            ⟨hout, hs, ⟨2, q, rfl⟩, hp3, q, rfl, hp3 ▸ hl.1⟩
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hl.2))) hp2
        · exact absurd hs.1 (not_rankLE2_unitary hv hp hl.1 hm4)
      · exact hU ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, ⟨m, q, hd⟩, hlift⟩
  ·
    exact seitzOuter_symplectic hSp ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hsp⟩
  ·
    rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
    · exact hO3 ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hout, rfl, hor, fun h => hD4 ⟨rfl, h⟩⟩
    · exact seitzOuter_orthogonal_five hOm ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hp5, hor⟩

end Assembly

end CFSG.LieType.SeitzGeneration
