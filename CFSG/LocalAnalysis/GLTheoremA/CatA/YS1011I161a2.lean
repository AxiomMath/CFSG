module

public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.Models
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I161aNames

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti CFSG.Models CFSG.TauCetiBridge




theorem names_chevalley
    {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel G t p f) :
    ∃ d : TauCeti.ValidLieTypeIndex, NamesTag d.1 t p f ∧ Nonempty (G ≃* d.Group) := by
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
    exact ⟨⟨LieTypeIndex.G2 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨⟨LieTypeIndex.F4 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨LieTypeIndex.E6 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨LieTypeIndex.E7 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨LieTypeIndex.E8 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨LieTypeIndex.twistedE6 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨LieTypeIndex.trialityD4 q, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩

theorem names_reeTits
    {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags)
    (h : ReeTitsModel G t p f) :
    ∃ d : TauCeti.ValidLieTypeIndex, NamesTag d.1 t p f ∧ Nonempty (G ≃* d.Group) := by
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
    exact ⟨⟨LieTypeIndex.reeG2 a, hv⟩, ⟨rfl, hfa⟩, ⟨e.trans b⟩⟩
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
    exact ⟨⟨LieTypeIndex.reeF4 a, hv⟩, ⟨rfl, hfa⟩, ⟨e₂⟩⟩
  · obtain ⟨-, -, -, rfl, rfl⟩ := hadm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have ha : a = 0 := by omega
    subst ha
    have := charP_two_of_card_eq_two_pow hK
    obtain ⟨e₁⟩ := tits_candidate_equiv_of_card TitsLieIndex.of hK
    have hv : LieTypeIndex.tits.Valid := by simp
    have e₂ : G ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv 0)).trans e₁.symm
    exact ⟨⟨LieTypeIndex.tits, hv⟩, ⟨rfl, rfl⟩, ⟨e₂⟩⟩

theorem names_suzuki {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    ∃ d : TauCeti.ValidLieTypeIndex, NamesTag d.1 .twistedB2 p f ∧ Nonempty (G ≃* d.Group) := by
  obtain ⟨hp2, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hv : (LieTypeIndex.suzuki a).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨ha, not_false⟩
  exact ⟨⟨LieTypeIndex.suzuki a, hv⟩, ⟨hp2, rfl⟩, ⟨(e.trans
    (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
    (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩


theorem suzuki_admissible {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    StatedLieAdmissible StatedLieTag.twistedB2 0 p f := by
  obtain ⟨hp2, a, ha, K, _, _, rfl, -, -⟩ := h
  subst hp2
  exact ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩

theorem lieModel_models_of_blueprint {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel G t n p f) : CFSG.Models.LieModel G t n p f := by
  rcases h with ⟨_, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩
  · exact ⟨hm.1, Or.inl hm⟩
  · subst hn
    obtain ⟨d, hd, he⟩ := names_chevalley ht hm
    exact ⟨hm.1, Or.inr ⟨rfl, d, hd, he⟩⟩
  · subst hn
    obtain ⟨d, hd, he⟩ := names_reeTits ht hm
    exact ⟨hm.1, Or.inr ⟨rfl, d, hd, he⟩⟩
  · subst hn
    subst ht
    obtain ⟨d, hd, he⟩ := names_suzuki hm
    exact ⟨suzuki_admissible hm, Or.inr ⟨rfl, d, hd, he⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I161aNames

end
