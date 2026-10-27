module

public import CFSG.Blueprint.Catalog
public import CFSG.Models
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
import CFSG.Adapters.ExceptionalCatalogReverse
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.LieType.Chevalley.RootCommutatorData
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.TauCetiBridge

open CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti

theorem exists_index_of_chevalley_even
    {X : Type} [Group X] {t : StatedLieTag} {f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel X t 2 f) :
    ∃ d : ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t 2 f ∧ Nonempty (X ≃* d.Group) := by
  have hB := Even.chevalleyBridgesAll
  obtain ⟨hadm, hm⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  let q : PrimePower := ⟨2, f, Nat.prime_two, hf⟩
  have hq : q.card = 2 ^ f := PrimePower.card_def q
  cases t <;> simp only [chevalleyExceptionalTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, false_or] at ht
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.G2 q).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := hB.g2 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩

theorem exists_index_of_reeTits_even
    {X : Type} [Group X] {t : StatedLieTag} {f : ℕ} (ht : t ∈ reeTitsTags)
    (h : ReeTitsModel X t 2 f) :
    ∃ d : ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t 2 f ∧ Nonempty (X ≃* d.Group) := by
  obtain ⟨hadm, a, hfa, hm⟩ := h
  cases t <;> simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_false, false_or] at ht
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · obtain ⟨-, -, -, -, -, h3⟩ := hadm
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
    have e₂ : X ≃* ValidLieTypeIndex.Group ⟨.reeF4 a, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv a)).trans e₁.symm
    exact ⟨⟨.reeF4 a, hv⟩, ⟨rfl, hfa⟩, ⟨e₂⟩⟩
  · obtain ⟨-, -, -, -, rfl⟩ := hadm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have ha : a = 0 := by omega
    subst ha
    have := charP_two_of_card_eq_two_pow hK
    obtain ⟨e₁⟩ := tits_candidate_equiv_of_card TitsLieIndex.of hK
    have hv : LieTypeIndex.tits.Valid := by simp
    have e₂ : X ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv 0)).trans e₁.symm
    exact ⟨⟨.tits, hv⟩, ⟨rfl, rfl⟩, ⟨e₂⟩⟩

end CFSG.TauCetiBridge
