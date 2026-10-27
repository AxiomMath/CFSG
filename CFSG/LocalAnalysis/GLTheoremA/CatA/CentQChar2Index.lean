module

public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3Bridge
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.StandardType.Marking
public import Certificates.Certificate8064
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.Adapters.TauCetiExceptional.ReeBridge
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti
open CFSG.TauCetiBridge CFSG.StandardType

section Exceptional


theorem index_of_chevalleyExceptional {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel G t p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧ Nonempty (G ≃* (CFSGIndex.lie d).Group) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
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
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, by simp [q], ⟨e.trans b⟩⟩

theorem index_of_reeTits_two {G : Type} [Group G] {t : StatedLieTag} {f : ℕ}
    (ht : t = .twistedF4 ∨ t = .Tits) (h : ReeTitsModel G t 2 f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (G ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, a, hfa, hm⟩ := h
  rcases ht with rfl | rfl
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
    have e₂ : G ≃* ValidLieTypeIndex.Group ⟨.reeF4 a, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv a)).trans e₁.symm
    exact ⟨⟨.reeF4 a, hv⟩, by simp, ⟨e₂⟩⟩
  · obtain ⟨-, -, -, hf1⟩ := hadm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have ha : a = 0 := by omega
    subst ha
    have := charP_two_of_card_eq_two_pow hK
    obtain ⟨e₁⟩ := tits_candidate_equiv_of_card TitsLieIndex.of (by rw [hK, hf1.2]; norm_num)
    have hv : LieTypeIndex.tits.Valid := by simp
    have e₂ : G ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩ :=
      (e.trans (ReeF4.nativeModelEquiv 0)).trans e₁.symm
    exact ⟨⟨.tits, hv⟩, by simp, ⟨e₂⟩⟩

theorem index_of_suzuki {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (G ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hv : (LieTypeIndex.suzuki a).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨ha, not_false⟩
  exact ⟨⟨_, hv⟩, by simp, ⟨(e.trans
    (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
    (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

end Exceptional

@[expose] def CentQIndexCases (R : Type) [Group R] : Prop :=
  (∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (R ≃* (CFSGIndex.lie d).Group)) ∨
    Nonempty (R ≃* alternatingGroup (Fin 5)) ∨ Nonempty (R ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (R ≃* alternatingGroup (Fin 8)) ∨ Nat.card R = 168 ∨
    ((∃ d : ValidLieTypeIndex, d.1.characteristic = 3 ∧ Nonempty (R ≃* (CFSGIndex.lie d).Group)) ∧
      Nat.card R = 6048)

section Classical

private theorem f_eq_two_of_pow_eq_four {f : ℕ} (h : 2 ^ f = 4) : f = 2 :=
  Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num : (4 : ℕ) = 2 ^ 2))

private theorem f_eq_one_of_pow_eq_two {f : ℕ} (h : 2 ^ f = 2) : f = 1 :=
  Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num : (2 : ℕ) = 2 ^ 1))

private theorem two_pow_ne_odd {f m : ℕ} (hm : m % 2 = 1) (h1 : 2 ≤ m) : 2 ^ f ≠ m := by
  intro h
  rcases f with _ | f
  · simp at h
    omega
  · rw [pow_succ] at h
    omega

theorem classical_two_cases {R : Type} [Group R] {t : StatedLieTag} {n f : ℕ}
    (hm : StatedClassicalModel R t n 2 f) :
    (∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (R ≃* (CFSGIndex.lie d).Group)) ∨
      (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) := by
  by_cases hdup : CFSG.HardMathSupport.Dickson.Sec6.I1431.TauCetiDuplicate t n 2 f
  · right
    rcases hdup with ⟨rfl, ⟨rfl, h4 | h5 | h9⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ | ⟨-, -, h3⟩
    · exact Or.inl ⟨rfl, rfl, f_eq_two_of_pow_eq_four h4⟩
    · exact absurd h5 (two_pow_ne_odd (by norm_num) (by norm_num))
    · exact absurd h9 (two_pow_ne_odd (by norm_num) (by norm_num))
    · exact Or.inr (Or.inl ⟨rfl, rfl, f_eq_one_of_pow_eq_two h2⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl, f_eq_one_of_pow_eq_two h2⟩)
    · exact absurd h3 (two_pow_ne_odd (by norm_num) (by norm_num))
  · left
    exact CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_tauCeti_index_of_statedClassicalModel hm hdup


theorem centQIndexCases_of_classical_two {R : Type} [Group R] {t : StatedLieTag} {n f : ℕ}
    (hm : StatedClassicalModel R t n 2 f) : CentQIndexCases R := by
  rcases classical_two_cases hm with h | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl h
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inl (by rw [hK]; norm_num))
    exact Or.inr (Or.inl ⟨e.trans e₅⟩)
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hm]
    decide
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (Or.inl ⟨by decide, hm⟩)))))

end Classical

section Main


theorem exists_index_of_markedModel {lab : CFSG.Assembly.LargeEvenLabel}
    {R : Type} [Group R] (h : MarkedModel lab R) : CentQIndexCases R := by
  obtain ⟨tag, rank, n⟩ := lab
  have hclass : ∀ {t' : StatedLieTag} {n' f' : ℕ}, LieModel R t' n' 2 f' → t' ∈ classicalTags →
      CentQIndexCases R := fun hm ht =>
    centQIndexCases_of_classical_two (hm.statedClassicalModel ht)
  have hchev : ∀ {t' : StatedLieTag} {n' f' : ℕ}, LieModel R t' n' 2 f' →
      t' ∈ chevalleyExceptionalTags → CentQIndexCases R := fun hm ht =>
    Or.inl (index_of_chevalleyExceptional ht (hm.chevalleyExceptionalModel ht))
  cases tag
  · exact hclass (t' := .PSL) h (by simp [classicalTags])
  · exact hclass (t' := .PSU) h (by simp [classicalTags])
  · exact hclass (t' := .PSp) h (by simp [classicalTags])
  · exact hclass (t' := .PSp) h (by simp [classicalTags])
  · by_cases hr : rank = 3
    · subst hr
      exact hclass (t' := .PSL) h (by simp [classicalTags])
    · have h' : LieModel R .POmegaPlus rank 2 n := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg, hr] using h
      exact hclass h' (by simp [classicalTags])
  · by_cases hr2 : rank = 2
    · subst hr2
      exact hclass (t' := .PSL) h (by simp [classicalTags])
    · by_cases hr3 : rank = 3
      · subst hr3
        exact hclass (t' := .PSU) h (by simp [classicalTags])
      · have h' : LieModel R .POmegaMinus rank 2 n := by
          simpa [MarkedModel, markTag, markRank, markChar, markDeg, hr2, hr3] using h
        exact hclass h' (by simp [classicalTags])
  · exact hchev (t' := .E6) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .E7) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .E8) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .F4) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .twistedE6) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .trialityD4) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .G2) h (by simp [chevalleyExceptionalTags])
  ·
    obtain ⟨-, -, hS⟩ : (0 = 0) ∧ (StatedLieTag.twistedB2 = .twistedB2) ∧ SuzukiModel R 2 n := by
      rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
      · exact absurd ht (by simp [classicalTags, markTag])
      · exact absurd ht (by simp [chevalleyExceptionalTags, markTag])
      · exact absurd ht (by simp [reeTitsTags, markTag])
      · exact ⟨rfl, rfl, hS⟩
    exact Or.inl (index_of_suzuki hS)
  ·
    obtain ⟨-, hR⟩ := LieModel.reeTitsModel (t := .twistedF4) h (by simp [reeTitsTags])
    exact Or.inl (index_of_reeTits_two (Or.inl rfl) hR)
  ·
    exact Or.inr (Or.inr (Or.inl (LieModel.nonempty_mulEquiv_alternating_six h)))
  ·
    have hc : StatedClassicalModel R .PSU 3 3 1 :=
      LieModel.statedClassicalModel (t := .PSU) h (by simp [classicalTags])
    obtain ⟨d, hd, e⟩ := CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_tauCeti_index_of_statedClassicalModel
      hc (by simp [CFSG.HardMathSupport.Dickson.Sec6.I1431.TauCetiDuplicate])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨d, hd, e⟩,
      LieModel.card_psu_three_three (X := R) h⟩))))
  ·
    obtain ⟨-, hR⟩ := LieModel.reeTitsModel (t := .Tits) h (by simp [reeTitsTags])
    exact Or.inl (index_of_reeTits_two (Or.inr rfl) hR)

theorem centQIndexCases_of_marking {L : Type} [Group L]
    {P : CFSG.Assembly.LargeEvenMarkProp L} (h : CFSG.Assembly.LargeEvenMarking L P) :
    CentQIndexCases (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, -, hM⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel_centerQuot h
  exact exists_index_of_markedModel hM

end Main

end CFSG.LocalAnalysis.GLTheoremA
