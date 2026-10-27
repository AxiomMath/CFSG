module

public import CFSG.ClassicalInvolution.Q3.TL3C6
public import CFSG.ClassicalInvolution.Q3.TL3C5

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section General

variable {G : Type} [Group G] [Finite G] {A : Subgroup G → Subgroup G → Prop}

@[expose] def betaOf (A : Subgroup G → Subgroup G → Prop) (Ω : Set (Subgroup G))
    (π : Set (Subgroup G)) : Set (Subgroup G) :=
  {v | v ∈ Ω ∧ ∀ M ∈ π, A v M}

structure Lemma1710 (A : Subgroup G → Subgroup G → Prop) (Ω : Set (Subgroup G))
    (K : Subgroup G) (π : Set (Subgroup G)) : Prop where
  unique : maxOrbs A K = {π}
  trans : ∀ J₁ ∈ π, ∀ J₂ ∈ π, ∃ a ∈ ⨆ M ∈ π, M, conjSub a J₁ = J₂
  stable : ∀ a ∈ (⨆ M ∈ π, M : Subgroup G), ∀ M ∈ π, conjSub a M ∈ π
  block : ∀ g : G, conjSub g '' betaOf A Ω π = betaOf A Ω π ∨
    Disjoint (conjSub g '' betaOf A Ω π) (betaOf A Ω π)
  mem_beta : K ∈ betaOf A Ω π
  union : π = ⋃ g ∈ {g : G | conjSub g K ∈ π}, conjSub g '' betaOf A Ω π
  generate : (⨆ L ∈ Ω, L) = ⊤ → ∀ g : G, conjSub g K ∈ π →
    (⨆ M ∈ π ∪ conjSub g '' π, M) = ⊤

variable {Ω : Set (Subgroup G)} (hF : GraphFam Ω A)
include hF

theorem mem_betaOf_iff {K : Subgroup G} (hK : K ∈ Ω) {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs A K) {v : Subgroup G} : v ∈ betaOf A Ω π ↔ π ∈ maxOrbs A v := by
  constructor
  · rintro ⟨-, hadj⟩
    exact (isMaxOrb_of_adj_all hF hK hπ hadj).1
  · intro h
    obtain ⟨⟨J, hvJ, -⟩, -⟩ := id h
    exact ⟨hF.mem hvJ, fun M hM => adj_of_mem_isMaxOrb hF h hM⟩

omit [Finite G] in
omit [Finite G] in
omit [Finite G] in
theorem conj_betaOf (π : Set (Subgroup G)) (g : G) :
    conjSub g '' betaOf A Ω π = betaOf A Ω (conjSub g '' π) := by
  ext w
  constructor
  · rintro ⟨v, ⟨hvΩ, hadj⟩, rfl⟩
    refine ⟨hF.conjMem v hvΩ g, ?_⟩
    rintro _ ⟨M, hM, rfl⟩
    exact hF.graph.conj g (hadj M hM)
  · rintro ⟨hwΩ, hadj⟩
    refine ⟨conjSub g⁻¹ w, ⟨hF.conjMem w hwΩ g⁻¹, fun M hM => ?_⟩, conjSub_conjSub_inv g w⟩
    have h1 := hF.graph.conj g⁻¹ (hadj (conjSub g M) ⟨M, hM, rfl⟩)
    rwa [conjSub_inv_conjSub] at h1

omit [Finite G] in
theorem transitive_of_maxOrb {K : Subgroup G} {π : Set (Subgroup G)} (hπ : π ∈ maxOrbs A K) :
    ∀ J₁ ∈ π, ∀ J₂ ∈ π, ∃ a ∈ ⨆ M ∈ π, M, conjSub a J₁ = J₂ := by
  intro J₁ hJ₁ J₂ hJ₂
  have hKJ₁ : A K J₁ := adj_of_mem_isMaxOrb hF hπ hJ₁
  have heq : orbOf A K J₁ = π := orbOf_eq_of_mem_isMaxOrb hπ hJ₁
  have := orbOf_subset_gen hF.graph hKJ₁ (show J₂ ∈ orbOf A K J₁ by rw [heq]; exact hJ₂)
  rw [heq] at this
  exact this

omit [Finite G] in
theorem stable_of_maxOrb {K : Subgroup G} {π : Set (Subgroup G)} (hπ : π ∈ maxOrbs A K) :
    ∀ a ∈ (⨆ M ∈ π, M : Subgroup G), ∀ M ∈ π, conjSub a M ∈ π := by
  intro a ha M hM
  have hXL : (⨆ M ∈ π, M : Subgroup G) ≤ nbrGen A K :=
    iSup₂_le fun I hI => le_nbrGen (adj_of_mem_isMaxOrb hF hπ hI)
  have h1 : conjSub a M ∈ orbOf A K M := ⟨a, hXL ha, rfl⟩
  rwa [orbOf_eq_of_mem_isMaxOrb hπ hM] at h1

theorem orbOf_eq_conj_of_maxOrb {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs A K) {J : Subgroup G} (hJ : J ∈ π) {g : G} (hg : conjSub g K = J) :
    orbOf A J K = conjSub g '' π ∧ maxOrbs A J = {conjSub g '' π} := by
  have hKJ : A K J := adj_of_mem_isMaxOrb hF hπ hJ
  have hJΩ : J ∈ Ω := hF.mem (hF.graph.symm hKJ)
  have hQ : orbOf A J K ∈ maxOrbs A J :=
    orbOf_mem_maxOrbs hF hKJ (by rw [orbOf_eq_of_mem_isMaxOrb hπ hJ]; exact hπ)
  have hgπ : conjSub g '' π ∈ maxOrbs A J := by
    rw [← hg]
    exact isMaxOrb_conj hF hπ g
  exact ⟨maxOrb_unique hF hJΩ hQ hgπ, maxOrbs_eq_singleton hF hJΩ hgπ⟩

theorem block_betaOf {K : Subgroup G} (hK : K ∈ Ω) {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs A K) (g : G) :
    conjSub g '' betaOf A Ω π = betaOf A Ω π ∨
      Disjoint (conjSub g '' betaOf A Ω π) (betaOf A Ω π) := by
  by_cases h : (conjSub g '' betaOf A Ω π ∩ betaOf A Ω π).Nonempty
  · left
    obtain ⟨w, hw1, hw2⟩ := h
    rw [conj_betaOf hF] at hw1 ⊢
    have hgπ : conjSub g '' π ∈ maxOrbs A (conjSub g K) := isMaxOrb_conj hF hπ g
    have hgK : conjSub g K ∈ Ω := hF.conjMem K hK g
    have h1 : conjSub g '' π ∈ maxOrbs A w := (mem_betaOf_iff hF hgK hgπ).mp hw1
    have h2 : π ∈ maxOrbs A w := (mem_betaOf_iff hF hK hπ).mp hw2
    have hwΩ : w ∈ Ω := hw2.1
    rw [maxOrb_unique hF hwΩ h1 h2]
  · right
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)

theorem conj_betaOf_subset {K : Subgroup G} (hK : K ∈ Ω) {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs A K) {J : Subgroup G} (hJ : J ∈ π) {g : G} (hg : conjSub g K = J) :
    J ∈ conjSub g '' betaOf A Ω π ∧ conjSub g '' betaOf A Ω π ⊆ π := by
  refine ⟨⟨K, ⟨hK, fun M hM => adj_of_mem_isMaxOrb hF hπ hM⟩, hg⟩, ?_⟩
  obtain ⟨hQeq, -⟩ := orbOf_eq_conj_of_maxOrb hF hπ hJ hg
  have hKJ : A K J := adj_of_mem_isMaxOrb hF hπ hJ
  have hπK : maxOrbs A K = {π} := maxOrbs_eq_singleton hF hK hπ
  rintro _ ⟨v, hv, rfl⟩
  have hv' : π ∈ maxOrbs A v := (mem_betaOf_iff hF hK hπ).mp hv
  have hw : conjSub g '' π ∈ maxOrbs A (conjSub g v) := isMaxOrb_conj hF hv' g
  have hKQ : K ∈ orbOf A J K := mem_orbOf_self J K
  rw [hQeq] at hKQ
  have hwK : A (conjSub g v) K := adj_of_mem_isMaxOrb hF hw hKQ
  have hKw : A K (conjSub g v) := hF.graph.symm hwK
  by_cases hm : orbOf A K (conjSub g v) ∈ maxOrbs A K
  · have := maxOrb_unique hF hK hm hπ
    rw [← this]
    exact mem_orbOf_self K _
  · exfalso
    have hmeq := maxOrbs_eq_of_nonmax hF hKw hm
    have hw' : conjSub g '' π ∈ maxOrbs A K := by rw [← hmeq]; exact hw
    have := maxOrb_unique hF hK hw' hπ
    rw [this] at hKQ
    exact not_mem_of_isMaxOrb hF hπ hKQ

theorem graph_17_10 {K : Subgroup G} (hK : K ∈ Ω) {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs A K) : Lemma1710 A Ω K π where
  unique := maxOrbs_eq_singleton hF hK hπ
  trans := transitive_of_maxOrb hF hπ
  stable := stable_of_maxOrb hF hπ
  block := block_betaOf hF hK hπ
  mem_beta := ⟨hK, fun M hM => adj_of_mem_isMaxOrb hF hπ hM⟩
  union := by
    apply Set.Subset.antisymm
    · intro J hJ
      have hKJ : A K J := adj_of_mem_isMaxOrb hF hπ hJ
      have hJΩ : J ∈ Ω := hF.mem (hF.graph.symm hKJ)
      obtain ⟨g, -, hg⟩ := hF.trans K hK J hJΩ
      refine Set.mem_iUnion₂.mpr ⟨g, show conjSub g K ∈ π by rw [hg]; exact hJ, ?_⟩
      exact (conj_betaOf_subset hF hK hπ hJ hg).1
    · intro M hM
      obtain ⟨g, hg, hMg⟩ := Set.mem_iUnion₂.mp hM
      exact (conj_betaOf_subset hF hK hπ hg rfl).2 hMg
  generate := by
    intro hgen g hg
    have hKJ : A K (conjSub g K) := adj_of_mem_isMaxOrb hF hπ hg
    have hP : orbOf A K (conjSub g K) ∈ maxOrbs A K := by
      rw [orbOf_eq_of_mem_isMaxOrb hπ hg]; exact hπ
    have h1 := le_iSup_of_maxOrb hF hKJ hP
    obtain ⟨hQ, -⟩ := orbOf_eq_conj_of_maxOrb hF hπ hg rfl
    rw [orbOf_eq_of_mem_isMaxOrb hπ hg, hQ] at h1
    refine top_le_iff.mp ?_
    rw [← hgen]
    exact iSup₂_le fun L hL => h1 L hL

omit hF [Finite G] in
theorem exists_adj_of_ne (hF : GraphFam Ω A) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω)
    (hne : K' ≠ K) : ∃ J, A K J := by
  rcases (hF.conn K hK K' hK').cases_head with h | ⟨c, hc, -⟩
  · exact absurd h.symm hne
  · exact ⟨c, hc⟩

theorem graph_17_10_of_ne {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) :
    ∃ π, maxOrbs A K = {π} ∧ Lemma1710 A Ω K π := by
  obtain ⟨J, hJ⟩ := exists_adj_of_ne hF hK hK' hne
  obtain ⟨π, hπ⟩ := exists_isMaxOrb hJ
  exact ⟨π, maxOrbs_eq_singleton hF hK hπ, graph_17_10 hF hK hπ⟩

end General

section Twin

variable {G : Type} [Group G] [Finite G]

structure TwinGraphStd (K₀ : Subgroup G) : Prop where
  hyp : HypOmegaGen (CoreAssembly.conjClass K₀)
  two : ∀ J ∈ CoreAssembly.conjClass K₀, IsPGroup 2 J
  sep : SepHyp (CoreAssembly.conjClass K₀)
  gen : (⨆ g : G, conjSub g K₀) = ⊤
  conn : Disconnected.DConnected (CoreAssembly.conjClass K₀)

variable {K₀ : Subgroup G}

omit [Finite G] in
theorem conjClass_trans (K : Subgroup G) :
    ∀ J ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = J := fun _ ⟨g, hg⟩ => ⟨g, hg⟩

omit [Finite G] in
theorem iSup_conjClass_eq_top (h : (⨆ g : G, conjSub g K₀) = ⊤) :
    (⨆ J ∈ CoreAssembly.conjClass K₀, J) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← h]
  exact iSup_le fun g => le_iSup₂_of_le (conjSub g K₀) ⟨g, rfl⟩ le_rfl

theorem TwinGraphStd.graphFam (hs : TwinGraphStd K₀) :
    GraphFam (CoreAssembly.conjClass K₀) (nbrAdj (CoreAssembly.conjClass K₀)) :=
  TC.graphFam hs.hyp hs.two hs.sep (conjClass_trans K₀) (iSup_conjClass_eq_top hs.gen) hs.conn

theorem twin_17_10 (hs : TwinGraphStd K₀) {K K' : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀)
    (hK' : K' ∈ CoreAssembly.conjClass K₀) (hne : K' ≠ K) :
    ∃ π, maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K = {π} ∧
      Lemma1710 (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) K π :=
  graph_17_10_of_ne hs.graphFam hK hK' hne

end Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
