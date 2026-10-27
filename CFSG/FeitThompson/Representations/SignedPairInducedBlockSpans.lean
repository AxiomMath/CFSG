module

public import CFSG.FeitThompson.Representations.DegreeZeroIsometryDisjointConjPairs
import CFSG.FeitThompson.Representations.EqualDegreeDifferencesAssignedPairs
import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
public import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

noncomputable section

section SignedPair

variable {G : Type*} [Group G]

theorem ne_neg_of_mem_Irr [Finite G] {α β : G → ℂ} (hα : α ∈ Irr G) (hβ : β ∈ Irr G) :
    α ≠ -β := by
  classical
  have : Fintype G := Fintype.ofFinite G
  intro h
  have h2 : cfInner α α = -cfInner α β := by rw [← cfInner_neg_right, ← h]
  rw [cfInner_self_of_mem_Irr hα, cfInner_eq_ite_of_mem_Irr hα hβ] at h2
  split_ifs at h2 <;> norm_num at h2

open scoped Classical in
def signedPair (α : G → ℂ) : Finset (G → ℂ) := {α, -star α}

omit [Group G] in
theorem mem_signedPair {α ρ : G → ℂ} : ρ ∈ signedPair α ↔ ρ = α ∨ ρ = -star α := by
  classical
  simp [signedPair]

omit [Group G] in
theorem self_mem_signedPair (α : G → ℂ) : α ∈ signedPair α := mem_signedPair.2 (Or.inl rfl)

omit [Group G] in
theorem neg_star_mem_signedPair (α : G → ℂ) : -star α ∈ signedPair α :=
  mem_signedPair.2 (Or.inr rfl)

theorem signedPair_subset_signedIrr [Finite G] {α : G → ℂ} (hα : α ∈ Irr G) :
    (signedPair α : Set (G → ℂ)) ⊆ signedIrr G := by
  intro ρ hρ
  rcases mem_signedPair.1 (by simpa using hρ) with rfl | rfl
  · exact Irr_subset_signedIrr hα
  · exact mem_signedIrr.2 (Or.inr (by simpa using star_mem_Irr hα))

omit [Group G] in
theorem pair_subset_span_of_signedPair_subset {α : G → ℂ} {R : Finset (G → ℂ)}
    (hR : signedPair α ⊆ R) :
    ({α, star α} : Set (G → ℂ)) ⊆ (Submodule.span ℤ (R : Set (G → ℂ)) : Set (G → ℂ)) := by
  intro ρ hρ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl
  · exact Submodule.subset_span (by simpa using hR (self_mem_signedPair ρ))
  · exact neg_mem_iff.1 (Submodule.subset_span (by simpa using hR (neg_star_mem_signedPair α)))

theorem card_signedPair [Finite G] {α : G → ℂ} (hα : α ∈ Irr G) : (signedPair α).card = 2 := by
  classical
  rw [show signedPair α = {α, -star α} from rfl,
    Finset.card_pair (ne_neg_of_mem_Irr hα (star_mem_Irr hα))]

theorem sum_signedPair [Finite G] {α : G → ℂ} (hα : α ∈ Irr G) :
    ∑ ρ ∈ signedPair α, ρ = α - star α := by
  classical
  rw [show signedPair α = {α, -star α} from rfl,
    Finset.sum_pair (ne_neg_of_mem_Irr hα (star_mem_Irr hα))]
  ring

theorem cfInner_of_mem_signedPair [Fintype G] {α ρ σ : G → ℂ} (hα : α ∈ Irr G)
    (hnr : star α ≠ α) (hρ : ρ ∈ signedPair α) (hσ : σ ∈ signedPair α) :
    cfInner ρ σ = if ρ = σ then 1 else 0 := by
  classical
  have hsα := star_mem_Irr hα
  have hne : α ≠ -star α := ne_neg_of_mem_Irr hα hsα
  have h0 : cfInner α (star α) = 0 := cfInner_eq_zero_of_mem_Irr hα hsα (Ne.symm hnr)
  have h0' : cfInner (star α) α = 0 := cfInner_eq_zero_of_mem_Irr hsα hα hnr
  rcases mem_signedPair.1 hρ with rfl | rfl <;> rcases mem_signedPair.1 hσ with rfl | rfl
  · rw [if_pos rfl, cfInner_self_of_mem_Irr hα]
  · rw [if_neg hne, cfInner_neg_right, h0, neg_zero]
  · rw [if_neg (Ne.symm hne), cfInner_neg_left, h0', neg_zero]
  · rw [if_pos rfl, cfInner_neg_left, cfInner_neg_right, neg_neg, cfInner_self_of_mem_Irr hsα]

theorem cfInner_eq_zero_of_mem_signedPair [Fintype G] {α β : G → ℂ} (hα : α ∈ Irr G)
    (hβ : β ∈ Irr G) (hd : Disjoint ({α, star α} : Set (G → ℂ)) {β, star β}) {ρ σ : G → ℂ}
    (hρ : ρ ∈ signedPair α) (hσ : σ ∈ signedPair β) : cfInner ρ σ = 0 := by
  classical
  have hzero : ∀ a ∈ ({α, star α} : Set (G → ℂ)), ∀ b ∈ ({β, star β} : Set (G → ℂ)),
      cfInner a b = 0 := by
    intro a ha b hb
    have hab : a ≠ b := Set.disjoint_iff_forall_ne.1 hd ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    have haI : a ∈ Irr G := by rcases ha with rfl | rfl; exacts [hα, star_mem_Irr hα]
    have hbI : b ∈ Irr G := by rcases hb with rfl | rfl; exacts [hβ, star_mem_Irr hβ]
    exact cfInner_eq_zero_of_mem_Irr haI hbI hab
  have hmα : α ∈ ({α, star α} : Set (G → ℂ)) := by simp
  have hmsα : star α ∈ ({α, star α} : Set (G → ℂ)) := by simp
  have hmβ : β ∈ ({β, star β} : Set (G → ℂ)) := by simp
  have hmsβ : star β ∈ ({β, star β} : Set (G → ℂ)) := by simp
  rcases mem_signedPair.1 hρ with rfl | rfl <;> rcases mem_signedPair.1 hσ with rfl | rfl
  · exact hzero _ hmα _ hmβ
  · rw [cfInner_neg_right, hzero _ hmα _ hmsβ, neg_zero]
  · rw [cfInner_neg_left, hzero _ hmsα _ hmβ, neg_zero]
  · rw [cfInner_neg_left, cfInner_neg_right, hzero _ hmsα _ hmsβ, neg_zero, neg_zero]

theorem disjoint_signedPair [Finite G] {α β : G → ℂ} (hα : α ∈ Irr G) (hβ : β ∈ Irr G)
    (hd : Disjoint ({α, star α} : Set (G → ℂ)) {β, star β}) :
    Disjoint (signedPair α) (signedPair β) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Finset.disjoint_left]
  intro ρ hρ hρ'
  have h0 := cfInner_eq_zero_of_mem_signedPair hα hβ hd hρ hρ'
  rw [cfInner_self_of_mem_signedIrr (signedPair_subset_signedIrr hα (by simpa using hρ))] at h0
  exact one_ne_zero h0

end SignedPair

namespace IsAntirealIsometry

variable {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G] {X : Set (L → ℂ)}
  {τ : (L → ℂ) → G → ℂ} (hτ : IsAntirealIsometry X τ)

include hτ

theorem map_sum {ι : Type*} {s : Finset ι} {f : ι → L → ℂ}
    (hf : ∀ i ∈ s, f i ∈ charSpanZero X) : τ (∑ i ∈ s, f i) = ∑ i ∈ s, τ (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using hτ.map_zero
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        hτ.map_add _ (hf a (Finset.mem_cons_self ..)) _
          (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_cons_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

end IsAntirealIsometry

variable {L G : Type*} [Group L] [Group G]

theorem irrConstituents_subset_irrDetect [Fintype L] (H : Subgroup L) [H.Normal] {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) : irrConstituents θ ⊆ irrDetect ℂ H := by
  rw [← iUnion_irrConstituents H]
  exact fun _ hχ => Set.mem_biUnion hθ hχ

theorem ne_of_mem_irrConstituents [Fintype L] (H : Subgroup L) [H.Normal] {θ θ' : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) (hθ' : θ' ∈ indFam H (nonprincipalIrr H))
    (hne : θ' ≠ θ) {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ)
    (hψ : ψ ∈ irrConstituents θ') : ψ ≠ χ := fun hc =>
  Set.disjoint_left.1 (pairwiseDisjoint_irrConstituents H hθ hθ' (Ne.symm hne)) hχ (hc ▸ hψ)

theorem ne_star_of_mem_irrConstituents [Fintype L] (H : Subgroup L) [H.Normal] {θ θ' : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) (hθ' : θ' ∈ indFam H (nonprincipalIrr H))
    (hne : θ' ≠ star θ) {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ)
    (hψ : ψ ∈ irrConstituents θ') : ψ ≠ star χ := by
  intro hc
  rw [hc] at hψ
  exact Set.disjoint_left.1
    (pairwiseDisjoint_irrConstituents H (conj_mem_indFam_nonprincipalIrr H hθ) hθ' (Ne.symm hne))
    (conj_mem_irrConstituents hχ) hψ

structure IsNormalInducedSignedFamily [Fintype L] [Fintype G] (H : Subgroup L) [H.Normal]
    (τ η : (L → ℂ) → G → ℂ) : Prop where
  odd_natCard : Odd (Nat.card L)
  ne_bot : H ≠ ⊥
  isAntirealIsometry : IsAntirealIsometry (irrDetect ℂ H) τ
  eq_sum_irrConstituents : ∀ θ ∈ indFam H (nonprincipalIrr H),
    θ = ∑ χ ∈ irrConstituentsFinset θ, χ
  apply_one_eq : ∀ θ ∈ indFam H (nonprincipalIrr H), ∀ χ ∈ irrConstituents θ,
    ∀ ψ ∈ irrConstituents θ, χ 1 = ψ 1
  root_mem_Irr : ∀ χ ∈ irrDetect ℂ H, η χ ∈ Irr G
  map_sub_star_eq : ∀ χ ∈ irrDetect ℂ H, τ (χ - star χ) = η χ - star (η χ)

open scoped Classical in
def signedRootBlock [Fintype L] (η : (L → ℂ) → G → ℂ) (θ : L → ℂ) : Finset (G → ℂ) :=
  (irrConstituentsFinset θ).biUnion fun χ => signedPair (η χ)

omit [Group G] in
theorem mem_signedRootBlock [Fintype L] (η : (L → ℂ) → G → ℂ) (θ : L → ℂ) {ρ : G → ℂ} :
    ρ ∈ signedRootBlock η θ ↔ ∃ χ ∈ irrConstituents θ, ρ ∈ signedPair (η χ) := by
  classical
  simp [signedRootBlock]

omit [Group G] in
theorem signedPair_subset_signedRootBlock [Fintype L] (η : (L → ℂ) → G → ℂ) {θ χ : L → ℂ}
    (hχ : χ ∈ irrConstituents θ) : signedPair (η χ) ⊆ signedRootBlock η θ :=
  fun _ hρ => (mem_signedRootBlock η θ).2 ⟨χ, hχ, hρ⟩

omit [Group G] in
theorem signedRootBlock_eq_biUnion [Fintype L] [DecidableEq (G → ℂ)] (η : (L → ℂ) → G → ℂ)
    (θ : L → ℂ) :
    signedRootBlock η θ = (irrConstituentsFinset θ).biUnion fun χ => signedPair (η χ) := by
  refine Finset.ext fun ρ => ?_
  rw [mem_signedRootBlock, Finset.mem_biUnion]
  simp

namespace IsNormalInducedSignedFamily

variable [Fintype L] [Fintype G] {H : Subgroup L} [H.Normal] {τ η : (L → ℂ) → G → ℂ}
  (h : IsNormalInducedSignedFamily H τ η)

include h

theorem root_mem_Irr_of_mem {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) {χ : L → ℂ}
    (hχ : χ ∈ irrConstituents θ) : η χ ∈ Irr G :=
  h.root_mem_Irr _ (irrConstituents_subset_irrDetect H hθ hχ)

theorem map_sub_star_eq_of_mem {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) {χ : L → ℂ}
    (hχ : χ ∈ irrConstituents θ) : τ (χ - star χ) = η χ - star (η χ) :=
  h.map_sub_star_eq _ (irrConstituents_subset_irrDetect H hθ hχ)

theorem star_root_ne {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) {χ : L → ℂ}
    (hχ : χ ∈ irrConstituents θ) : star (η χ) ≠ η χ :=
  h.isAntirealIsometry.star_ne_of_map_sub_star_eq (irrConstituents_subset_irrDetect H hθ hχ)
    (h.root_mem_Irr_of_mem hθ hχ) (h.map_sub_star_eq_of_mem hθ hχ)

theorem disjoint_root_pair {θ θ' : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H))
    (hθ' : θ' ∈ indFam H (nonprincipalIrr H)) {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ)
    (hψ : ψ ∈ irrConstituents θ') (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) :
    Disjoint ({η χ, star (η χ)} : Set (G → ℂ)) {η ψ, star (η ψ)} :=
  h.isAntirealIsometry.disjoint_pair_of_map_sub_star_eq
    (irrConstituents_subset_irrDetect H hθ hχ) (irrConstituents_subset_irrDetect H hθ' hψ)
    h1 h2 (h.root_mem_Irr_of_mem hθ hχ) (h.root_mem_Irr_of_mem hθ' hψ)
    (h.map_sub_star_eq_of_mem hθ hχ) (h.map_sub_star_eq_of_mem hθ' hψ)

theorem ne_star_of_mem_irrConstituents_self {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ)
    (hψ : ψ ∈ irrConstituents θ) : ψ ≠ star χ :=
  ne_star_of_mem_irrConstituents H hθ hθ
    (ne_conj_of_mem_indFam_nonprincipalIrr h.odd_natCard H hθ) hχ hψ

theorem disjoint_signedPair_of_ne {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) (hne : χ ≠ ψ) :
    Disjoint (signedPair (η χ)) (signedPair (η ψ)) :=
  disjoint_signedPair (h.root_mem_Irr_of_mem hθ hχ) (h.root_mem_Irr_of_mem hθ hψ)
    (h.disjoint_root_pair hθ hθ hχ hψ (Ne.symm hne)
      (h.ne_star_of_mem_irrConstituents_self hθ hχ hψ))

theorem pairwiseDisjoint_signedPair {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    (irrConstituentsFinset θ : Set (L → ℂ)).PairwiseDisjoint fun χ => signedPair (η χ) :=
  fun _ hχ _ hψ hne =>
    h.disjoint_signedPair_of_ne hθ (by simpa using hχ) (by simpa using hψ) hne

theorem signedRootBlock_subset_signedIrr {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    (signedRootBlock η θ : Set (G → ℂ)) ⊆ signedIrr G := by
  intro ρ hρ
  obtain ⟨χ, hχ, hρ⟩ := (mem_signedRootBlock η θ).1 (by simpa using hρ)
  exact signedPair_subset_signedIrr (h.root_mem_Irr_of_mem hθ hχ) (by simpa using hρ)

open scoped Classical in
theorem card_signedRootBlock {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    (signedRootBlock η θ).card = 2 * (irrConstituentsFinset θ).card := by
  rw [signedRootBlock_eq_biUnion, Finset.card_biUnion (h.pairwiseDisjoint_signedPair hθ),
    Finset.sum_congr rfl (g := fun _ => 2) fun χ hχ =>
      card_signedPair (h.root_mem_Irr_of_mem hθ (by simpa using hχ)),
    Finset.sum_const, mul_comm, smul_eq_mul]

theorem cfInner_of_mem_signedRootBlock {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {ρ σ : G → ℂ} (hρ : ρ ∈ signedRootBlock η θ) (hσ : σ ∈ signedRootBlock η θ) :
    cfInner ρ σ = if ρ = σ then 1 else 0 := by
  classical
  obtain ⟨χ, hχ, hρ'⟩ := (mem_signedRootBlock η θ).1 hρ
  obtain ⟨ψ, hψ, hσ'⟩ := (mem_signedRootBlock η θ).1 hσ
  by_cases hcp : χ = ψ
  · subst hcp
    exact cfInner_of_mem_signedPair (h.root_mem_Irr_of_mem hθ hχ) (h.star_root_ne hθ hχ) hρ' hσ'
  · have hne : ρ ≠ σ := fun hc =>
      Finset.disjoint_left.1 (h.disjoint_signedPair_of_ne hθ hχ hψ hcp) hρ' (hc ▸ hσ')
    rw [if_neg hne]
    exact cfInner_eq_zero_of_mem_signedPair (h.root_mem_Irr_of_mem hθ hχ)
      (h.root_mem_Irr_of_mem hθ hψ)
      (h.disjoint_root_pair hθ hθ hχ hψ (Ne.symm hcp)
        (h.ne_star_of_mem_irrConstituents_self hθ hχ hψ)) hρ' hσ'

open scoped Classical in
theorem cfInner_coe_signedRootBlock {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H))
    (i j : {v // v ∈ signedRootBlock η θ}) :
    cfInner (i : G → ℂ) (j : G → ℂ) = if i = j then 1 else 0 := by
  rw [h.cfInner_of_mem_signedRootBlock hθ i.2 j.2]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos (by rw [hij])]
  · rw [if_neg hij, if_neg fun hc : (i : G → ℂ) = j => hij (Subtype.ext hc)]

theorem sub_star_eq_sum {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    θ - star θ = ∑ χ ∈ irrConstituentsFinset θ, (χ - star χ) := by
  rw [Finset.sum_sub_distrib, ← star_sum, ← h.eq_sum_irrConstituents θ hθ]

theorem sum_signedRootBlock {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    τ (θ - star θ) = ∑ ρ ∈ signedRootBlock η θ, ρ := by
  classical
  rw [h.sub_star_eq_sum hθ,
    h.isAntirealIsometry.map_sum fun χ hχ =>
      h.isAntirealIsometry.sub_star_mem
        (irrConstituents_subset_irrDetect H hθ (by simpa using hχ)),
    signedRootBlock_eq_biUnion, Finset.sum_biUnion (h.pairwiseDisjoint_signedPair hθ)]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [h.map_sub_star_eq_of_mem hθ (by simpa using hχ),
    sum_signedPair (h.root_mem_Irr_of_mem hθ (by simpa using hχ))]

theorem map_sub_mem_span_signedRootBlock {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) :
    τ (χ - ψ) ∈ Submodule.span ℤ (signedRootBlock η θ : Set (G → ℂ)) := by
  have hspan := h.isAntirealIsometry.map_sub_mem_span
    (irrConstituents_subset_irrDetect H hθ hχ) (irrConstituents_subset_irrDetect H hθ hψ)
    (h.apply_one_eq θ hθ χ hχ ψ hψ) (h.root_mem_Irr_of_mem hθ hχ)
    (h.root_mem_Irr_of_mem hθ hψ) (h.map_sub_star_eq_of_mem hθ hχ)
    (h.map_sub_star_eq_of_mem hθ hψ)
  refine Submodule.span_le.2 ?_ hspan
  have hχs := pair_subset_span_of_signedPair_subset
    (signedPair_subset_signedRootBlock (η := η) hχ)
  have hψs := pair_subset_span_of_signedPair_subset
    (signedPair_subset_signedRootBlock (η := η) hψ)
  intro ρ hρ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact hχs (by simp)
  · exact hχs (by simp)
  · exact hψs (by simp)
  · exact hψs (by simp)

theorem cfInner_eq_zero_of_mem_signedRootBlock {θ θ' : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) (hθ' : θ' ∈ indFam H (nonprincipalIrr H))
    (h1 : θ' ≠ θ) (h2 : θ' ≠ star θ) {ρ σ : G → ℂ} (hρ : ρ ∈ signedRootBlock η θ)
    (hσ : σ ∈ signedRootBlock η θ') : cfInner ρ σ = 0 := by
  obtain ⟨χ, hχ, hρ'⟩ := (mem_signedRootBlock η θ).1 hρ
  obtain ⟨ψ, hψ, hσ'⟩ := (mem_signedRootBlock η θ').1 hσ
  exact cfInner_eq_zero_of_mem_signedPair (h.root_mem_Irr_of_mem hθ hχ)
    (h.root_mem_Irr_of_mem hθ' hψ)
    (h.disjoint_root_pair hθ hθ' hχ hψ (ne_of_mem_irrConstituents H hθ hθ' h1 hχ hψ)
      (ne_star_of_mem_irrConstituents H hθ hθ' h2 hχ hψ)) hρ' hσ'

theorem disjoint_signedRootBlock {θ θ' : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H))
    (hθ' : θ' ∈ indFam H (nonprincipalIrr H)) (h1 : θ' ≠ θ) (h2 : θ' ≠ star θ) :
    Disjoint (signedRootBlock η θ) (signedRootBlock η θ') := by
  rw [Finset.disjoint_left]
  intro ρ hρ hρ'
  have h0 := h.cfInner_eq_zero_of_mem_signedRootBlock hθ hθ' h1 h2 hρ hρ'
  rw [cfInner_self_of_mem_signedIrr
    (h.signedRootBlock_subset_signedIrr hθ (by simpa using hρ))] at h0
  exact one_ne_zero h0

theorem signedRootBlock_spec {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    ((signedRootBlock η θ : Set (G → ℂ)) ⊆ signedIrr G ∧
        (∀ ρ ∈ signedRootBlock η θ, ∀ σ ∈ signedRootBlock η θ,
          cfInner ρ σ = if ρ = σ then 1 else 0) ∧
        (signedRootBlock η θ).card = 2 * (irrConstituentsFinset θ).card) ∧
      τ (θ - star θ) = ∑ ρ ∈ signedRootBlock η θ, ρ ∧
      (∀ χ ∈ irrConstituents θ, ∀ ψ ∈ irrConstituents θ,
        τ (χ - ψ) ∈ Submodule.span ℤ (signedRootBlock η θ : Set (G → ℂ))) ∧
      ∀ θ' ∈ indFam H (nonprincipalIrr H), θ' ≠ θ → θ' ≠ star θ →
        ∀ ρ ∈ signedRootBlock η θ, ∀ σ ∈ signedRootBlock η θ', IsOrthogonal ρ σ := by
  classical
  refine ⟨⟨h.signedRootBlock_subset_signedIrr hθ,
    fun _ hρ _ hσ => h.cfInner_of_mem_signedRootBlock hθ hρ hσ, h.card_signedRootBlock hθ⟩,
    h.sum_signedRootBlock hθ,
    fun _ hχ _ hψ => h.map_sub_mem_span_signedRootBlock hθ hχ hψ,
    fun θ' hθ' h1 h2 _ hρ _ hσ => ?_⟩
  exact isOrthogonal_iff.2 (h.cfInner_eq_zero_of_mem_signedRootBlock hθ hθ' h1 h2 hρ hσ)

end IsNormalInducedSignedFamily

end

end CFSG.FeitThompson
