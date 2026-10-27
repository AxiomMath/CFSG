module

public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.InCatalog
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.Adapters.TauCetiExceptional.ReeBridge
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.Foundations
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.TauCetiBridge

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti

theorem nonempty_candidate_equiv_of_card
    {L : Type} [Field L] [Algebra (ZMod 2) L] [IsAlgClosed L] (hZ : ReeF4.ZerosInAdjoint L)
    {m : ℕ} {S : F4ShortRoot.PrimeField.points L →* F4ShortRoot.PrimeField.points L}
    (hS : ReeF4.IsReeSteinberg m S)
    (hSS : ∀ g, S (S g) = F4ShortRoot.PrimeField.frobenius (2 * m + 1) L g)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nonempty (FixedPointCandidate S ≃* FixedPointCandidate (ReeF4.reeF K m)) := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K L := φ.toRingHom.toAlgebra
  exact ReeF4.nonempty_candidate_equiv hZ hS hSS hK

theorem reeF4_candidate_equiv_of_card
    (d : ReeF4LieIndex) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ (2 * d.toSuzukiReeIndex.halfExponent + 1)) :
    Nonempty (FixedPointCandidate d.steinberg ≃*
      FixedPointCandidate (ReeF4.reeF K d.toSuzukiReeIndex.halfExponent)) := by
  have hSS : ∀ g, d.steinberg (d.steinberg g) = F4ShortRoot.PrimeField.frobenius
      (2 * d.toSuzukiReeIndex.halfExponent + 1) d.1.Closure g := fun g => by
    rw [d.steinberg_steinberg, ReeF4LieIndex.frobenius_def,
      d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]
  exact nonempty_candidate_equiv_of_card (ReeF4.zerosInAdjoint_reeF4 d)
    (ReeF4.isReeSteinberg_reeF4 d) hSS hK

theorem tits_candidate_equiv_of_card
    (d : TitsLieIndex) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nonempty (FixedPointCandidate d.steinberg ≃* FixedPointCandidate (ReeF4.reeF K 0)) := by
  have hSS : ∀ g, d.steinberg (d.steinberg g) =
      F4ShortRoot.PrimeField.frobenius (2 * 0 + 1) d.1.Closure g := fun g => by
    rw [d.steinberg_steinberg, TitsLieIndex.frobenius_def]
  exact nonempty_candidate_equiv_of_card (ReeF4.zerosInAdjoint_tits d)
    (ReeF4.isReeSteinberg_tits d) hSS hK

theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

theorem chevalleyExceptionalModel_inCatalog
    {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel G t p f) : InCatalog G := by
  have hB := Even.chevalleyBridgesAll
  obtain ⟨hadm, hm⟩ := h
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := PrimePower.card_def q
  cases t <;> simp only [chevalleyExceptionalTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, false_or] at ht
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.G2 q).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := hB.g2 q hv K (by rw [hK, hq])
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩

theorem reeTitsModel_inCatalog
    {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags)
    (h : ReeTitsModel G t p f) : InCatalog G := by
  obtain ⟨hadm, a, hfa, hm⟩ := h
  cases t <;> simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_false, false_or] at ht
  · obtain ⟨-, -, -, rfl, -, h3⟩ := hadm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have ha : 1 ≤ a := by omega
    have hv : (LieTypeIndex.reeG2 a).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff] using ha
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := reeG2Bridge a hv K (by rw [hK, hfa])
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩
  · obtain ⟨-, -, -, rfl, -, h3⟩ := hadm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have ha : 1 ≤ a := by omega
    have hv : (LieTypeIndex.reeF4 a).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff] using ha
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    have := charP_two_of_card_eq_two_pow hK
    have hhalf : (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent = a :=
      SuzukiReeIndex.halfExponent_reeF4 a hv
    have hcard : Nat.card K =
        2 ^ (2 * (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent + 1) := by
      rw [hhalf, ← hfa]
      exact hK
    obtain ⟨e₁⟩ := reeF4_candidate_equiv_of_card (ReeF4LieIndex.of a hv) hcard
    rw [hhalf] at e₁
    have e₂ : G ≃* ValidLieTypeIndex.Group ⟨.reeF4 a, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv a)).trans e₁.symm
    exact ⟨.lie ⟨.reeF4 a, hv⟩, ⟨e₂⟩⟩
  · obtain ⟨-, -, -, rfl, rfl⟩ := hadm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have ha : a = 0 := by omega
    subst ha
    have := charP_two_of_card_eq_two_pow hK
    obtain ⟨e₁⟩ := tits_candidate_equiv_of_card TitsLieIndex.of hK
    have hv : LieTypeIndex.tits.Valid := by simp
    have e₂ : G ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv 0)).trans e₁.symm
    exact ⟨.lie ⟨.tits, hv⟩, ⟨e₂⟩⟩

theorem suzukiModel_inCatalog {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    InCatalog G := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hv : (LieTypeIndex.suzuki a).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨ha, not_false⟩
  exact ⟨.lie ⟨_, hv⟩, ⟨(e.trans
    (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
    (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

theorem exceptionalRep_inCatalog
    (G : Type) [Group G] (h : ExceptionalRep G) : InCatalog G := by
  rcases h with ⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩
  · exact chevalleyExceptionalModel_inCatalog ht h
  · exact reeTitsModel_inCatalog ht h
  · exact suzukiModel_inCatalog h

end CFSG.TauCetiBridge
