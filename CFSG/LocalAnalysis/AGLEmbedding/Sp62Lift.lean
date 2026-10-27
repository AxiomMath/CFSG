module

public import CFSG.LocalAnalysis.AGLEmbedding.G28Data

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section LiftSet

variable {G : Type} [Group G] [Finite G]

@[expose] def liftSet (H K : Subgroup G) (V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
    Set (Subgroup G) :=
  {Y | Y ≤ K ∧ K ≤ Subgroup.normalizer (Y : Set G) ∧
    V₀ ≤ (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))}

omit [Finite G] in
theorem commutator_subgroupOf_le {H Y₁ Y₂ : Subgroup G}
    (h₁ : Y₁ ≤ Subgroup.normalizer (Y₂ : Set G)) (h₂ : Y₂ ≤ Subgroup.normalizer (Y₁ : Set G)) :
    ⁅Y₁.subgroupOf H, Y₂.subgroupOf H⁆ ≤ (Y₁ ⊓ Y₂).subgroupOf H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  have hc : ⁅(a : G), (b : G)⁆ ∈ Y₁ ⊓ Y₂ := commutator_le_inf_of_le_normalizer le_rfl h₁ h₂
    (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb))
  simpa [commutatorElement_def] using hc

omit [Finite G] in
theorem inf_mem_liftSet {H K : Subgroup G} {V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hV₀ : ⁅V₀, V₀⁆ = V₀) {Y₁ Y₂ : Subgroup G} (h₁ : Y₁ ∈ liftSet H K V₀)
    (h₂ : Y₂ ∈ liftSet H K V₀) : Y₁ ⊓ Y₂ ∈ liftSet H K V₀ := by
  obtain ⟨hY₁K, hKY₁, hV₁⟩ := h₁
  obtain ⟨hY₂K, hKY₂, hV₂⟩ := h₂
  refine ⟨inf_le_left.trans hY₁K, fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKY₁ hk, hKY₂ hk⟩, ?_⟩
  rw [← hV₀]
  refine (Subgroup.commutator_mono hV₁ hV₂).trans ?_
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (commutator_subgroupOf_le (hY₁K.trans hKY₂) (hY₂K.trans hKY₁))

theorem exists_minimal_liftSet {H K : Subgroup G}
    {V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : K ∈ liftSet H K V₀) :
    ∃ V ∈ liftSet H K V₀, ∀ Y ∈ liftSet H K V₀, Y ≤ V → Y = V := by
  obtain ⟨V, hV, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min (liftSet H K V₀) ⟨K, hK⟩
  exact ⟨V, hV, fun Y hY hYV => by
    by_contra hne
    exact hmin Y hY (lt_of_le_of_ne hYV hne)⟩

end LiftSet

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section MinimalLift

variable {G : Type} [Group G] [Finite G] {H K : Subgroup G}
  {V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {V : Subgroup G}

omit [Finite G] in
theorem le_of_minimal_liftSet (hV₀ : ⁅V₀, V₀⁆ = V₀) (hV : V ∈ liftSet H K V₀)
    (hmin : ∀ Y ∈ liftSet H K V₀, Y ≤ V → Y = V) {Y : Subgroup G} (hY : Y ∈ liftSet H K V₀) :
    V ≤ Y := by
  have := hmin _ (inf_mem_liftSet hV₀ hV hY) inf_le_left
  rw [← this]
  exact inf_le_right

omit [Finite G] in
theorem le_normalizer_commutator {K V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.normalizer ((⁅V, V⁆ : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKV hk)]

omit [Finite G] in
theorem perfect_of_minimal_liftSet (hV₀ : ⁅V₀, V₀⁆ = V₀) (hV : V ∈ liftSet H K V₀)
    (hmin : ∀ Y ∈ liftSet H K V₀, Y ≤ V → Y = V) : ⁅V, V⁆ = V := by
  obtain ⟨hVK, hKV, hV₀V⟩ := hV
  refine hmin _ ⟨(Subgroup.commutator_le_self V).trans hVK, le_normalizer_commutator hKV, ?_⟩
    (Subgroup.commutator_le_self V)
  rw [← hV₀]
  refine (Subgroup.commutator_mono hV₀V hV₀V).trans ?_
  rw [← Subgroup.map_commutator]
  refine Subgroup.map_mono ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  have hc : ⁅(a : G), (b : G)⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator
    (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)
  simpa [commutatorElement_def] using hc

omit [Finite G] in
theorem map_eq_of_minimal_liftSet (hKH : K ≤ H) (hV : V ∈ liftSet H K V₀)
    (hmin : ∀ Y ∈ liftSet H K V₀, Y ≤ V → Y = V)
    (hV₀n : (K.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤
      Subgroup.normalizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3))) :
    (V.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = V₀ := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  obtain ⟨hVK, hKV, hV₀V⟩ := hV
  set Pre := (V₀.comap π).map H.subtype with hPre
  have hmem : V ⊓ Pre ∈ liftSet H K V₀ := by
    refine ⟨inf_le_left.trans hVK, fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKV hk, ?_⟩, ?_⟩
    · exact mem_normalizer_comap_map (hKH hk)
        (hV₀n (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)))
    · intro v hv
      obtain ⟨h, hh, rfl⟩ := hV₀V hv
      exact ⟨h, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hh, ⟨h, hv, rfl⟩⟩, rfl⟩
  have heq := hmin _ hmem inf_le_left
  refine le_antisymm ?_ hV₀V
  rintro _ ⟨x, hx, rfl⟩
  have hxV : (x : G) ∈ V := Subgroup.mem_subgroupOf.mp hx
  rw [← heq] at hxV
  have hxP : (x : G) ∈ Pre := hxV.2
  obtain ⟨h, hh, hhx⟩ := hxP
  have : h = x := Subtype.ext hhx
  rw [← this]
  exact hh

end MinimalLift

end CFSG.AGLEmbedding
