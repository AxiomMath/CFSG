module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeOutSmall
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinFamily
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.UnitaryFamily
import CFSG.HardMathSupport.Lang.E6Descent.FixedThreeE6Final
import CFSG.HardMathSupport.Lang.E6Descent.RankBoundProof
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeReduce
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorCore

public section

namespace CFSG.AGLEmbedding.FixedThree

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open TauCeti
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem not_dvd_card_outer_POmegaOdd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaOdd n r m) (hℓm : ¬ ℓ ∣ m) :
    ¬ ℓ ∣ Nat.card (Outer X) := by
  have h0 := h
  obtain ⟨⟨hr, -, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaOdd (.inl rfl) n r m
    h K hK (quadOdd n K) (coe_quadOdd n K) e
  obtain ⟨a, ha⟩ := CFSG.RankThree.Classical.SteinbergBY.exists_card_abelianization_eq_two_pow
    (oddIndexEquiv n) (quadOdd n K) hab.1
  have ha' : Nat.card (Abelianization (matrixIsometries (coordinateQuadOdd n K))) = 2 ^ a := ha
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  have h1 := relIndex_inner_dvd (coordinateQuadOdd n K)
  have h2 := relIndex_isometryRange_dvd (coordinateQuadOdd n K) hQ
  have h3 := (relIndex_linearRange_dvd (coordinateQuadOdd n K)).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection (coordinateQuadOdd n K)).range).trans
      (card_ringAut_and_isCyclic hr K hK).1.dvd)
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
  have hk : (matrixProjectiveImage (coordinateQuadOdd n K)).index = 1 := by
    rw [htop, Subgroup.index_top]
  rw [Nat.card_congr (equivalence (coordinateOddWitnessEquiv K e)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_eq, hk, mul_one]
  intro hdvd
  have hnot2 : ¬ ℓ ∣ 2 := fun hd => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp hd)
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h12 | hc
  · rcases (Nat.Prime.dvd_mul hℓ).mp h12 with hA | hB
    · rw [ha'] at h1
      exact hnot2 (hℓ.dvd_of_dvd_pow (hA.trans h1))
    · rw [hsq] at h2
      exact hnot2 ((hB.trans h2).trans (Nat.gcd_dvd_right _ _))
  · exact hℓm (hc.trans h3)


theorem outSmallLie_holds : OutSmallLie where
  twistedA _ _ q hv hq := fun ⟨e⟩ => not_three_dvd_card_outer_twistedA_three q hv hq e
  b K _ q hv hq := fun ⟨e⟩ => by
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_three hq
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv
      (by omega) le_rfl e
    rw [hp, hf] at hm
    exact not_dvd_card_outer_POmegaOdd Nat.prime_three (by norm_num) hm (by norm_num)
  g _ _ q hv hq := fun ⟨e⟩ => not_three_dvd_card_outer_G2_three q hv hq e

theorem kFactCompFixedThreeEltN_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (hOutS : ∀ s : SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (CFSGIndex.sporadic s).Group)) : KFactCompFixedThreeEltN :=
  (kFactCompFixedThreeElt_of_families hGA hOutS outSmallLie_holds
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.fixedThreeLinear
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.fixedThreeUnitary
    (CFSG.HardMathSupport.Lang.E6Descent.fixedThreeE6_of_blackburn_griess
      CFSG.HardMathSupport.Lang.E6Descent.rankBoundTStar hGA)).toN

end CFSG.AGLEmbedding.FixedThree
