module

public import CFSG.Goldschmidt75.Descent
public import CFSG.Goldschmidt75.WeakClosure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise

universe u

section Defs

variable {G : Type*} [Group G]

@[expose] def rcSet (S P : Subgroup G) : Subgroup G :=
  ⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ P

@[expose] def LocalRc (S P S₀ : Subgroup G) : Prop :=
  ∀ h ∈ normalizer (S₀ : Set G), ∀ x ∈ rcSet S P, h⁻¹ * x * h ∈ P → h⁻¹ * x * h ∈ rcSet S P

@[expose] def rcRel (S P : Subgroup G) (U V : Set G) : Prop :=
  U ⊆ (rcSet S P : Set G) ↔ V ⊆ (rcSet S P : Set G)

theorem rcRel_equivalence (S P : Subgroup G) : Equivalence (rcRel S P) where
  refl _ := Iff.rfl
  symm h := h.symm
  trans h h' := h.trans h'

theorem rcSet_le_centralizer (S P : Subgroup G) :
    rcSet S P ≤ centralizer (S : Set G) :=
  inf_le_left.trans (Subgroup.commutator_le_self _)

theorem rcSet_le (S P : Subgroup G) : rcSet S P ≤ P := inf_le_right

theorem centralizer_le_normalizer_of_le {S S₀ : Subgroup G} (h : S₀ ≤ S) :
    centralizer (S : Set G) ≤ normalizer (S₀ : Set G) :=
  (Subgroup.centralizer_le h).trans (Subgroup.centralizer_le_normalizer (S₀ : Set G))

theorem respects_of_localRc {S P S₀ : Subgroup G} (h : LocalRc S P S₀) :
    Respects (rcRel S P) P S₀ := by
  intro g hg U hU0 hUg
  constructor
  · intro hU x hx
    rw [mem_rconj] at hx
    have hxP : g⁻¹ * (g * x * g⁻¹) * g ∈ P := by
      have := hUg (conj_mem_rconj (g := g) hx); simpa [mul_assoc] using this
    have h1 := h g hg _ (hU hx) hxP
    simpa [mul_assoc] using h1
  · intro hU x hx
    have hxg : g⁻¹ * x * g ∈ rconj g U := conj_mem_rconj hx
    have hxP : g⁻¹⁻¹ * (g⁻¹ * x * g) * g⁻¹ ∈ P := by
      simpa [mul_assoc] using (hU0 hx).1
    have h1 := h g⁻¹ ((normalizer _).inv_mem hg) _ (hU hxg) hxP
    simpa [mul_assoc] using h1

theorem localRc_of_respects {S P S₀ : Subgroup G} (hS₀ : S₀ ≤ S)
    (h : Respects (rcRel S P) P S₀) : LocalRc S P S₀ := by
  intro g hg x hx hxg
  have hU : ({x} : Set G) ⊆ ((P ⊓ normalizer (S₀ : Set G) : Subgroup G) : Set G) :=
    Set.singleton_subset_iff.mpr ⟨rcSet_le S P hx,
      centralizer_le_normalizer_of_le hS₀ (rcSet_le_centralizer S P hx)⟩
  have hconj : rconj g {x} = {g⁻¹ * x * g} := by
    ext z
    simp only [mem_rconj, Set.mem_singleton_iff]
    constructor
    · intro hz; rw [← hz]; group
    · intro hz; rw [hz]; group
  have h1 := (h g hg {x} hU (by rw [hconj]; exact Set.singleton_subset_iff.mpr hxg)).mp
    (Set.singleton_subset_iff.mpr hx)
  rw [hconj] at h1
  exact Set.singleton_subset_iff.mp h1

theorem mem_commutator_subgroupOf {H A : Subgroup G} (hAH : A ≤ H) {x : G}
    (hx : x ∈ ⁅A, A⁆) (hxH : x ∈ H) :
    (⟨x, hxH⟩ : H) ∈ ⁅A.subgroupOf H, A.subgroupOf H⁆ := by
  have e : ⁅A.subgroupOf H, A.subgroupOf H⁆.map H.subtype = ⁅A, A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
  rw [← e] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = ⟨x, hxH⟩ := Subtype.ext hyx
  rwa [← this]

theorem map_commutator_centralizer_le {H S : Subgroup G} (hSH : S ≤ H) :
    (⁅centralizer ((S.subgroupOf H : Subgroup H) : Set H),
        centralizer ((S.subgroupOf H : Subgroup H) : Set H)⁆).map H.subtype ≤
      ⁅centralizer (S : Set G), centralizer (S : Set G)⁆ := by
  rw [Subgroup.map_commutator]
  have h : (centralizer ((S.subgroupOf H : Subgroup H) : Set H)).map H.subtype ≤
      centralizer (S : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_centralizer_subgroupOf_iff hSH).1 hy
  exact Subgroup.commutator_mono h h

theorem subgroupOf_centralizer_le {H S : Subgroup G} (hSH : S ≤ H) :
    (centralizer (S : Set G)).subgroupOf H ≤ centralizer ((S.subgroupOf H : Subgroup H) : Set H) :=
  fun _ hx => (mem_centralizer_subgroupOf_iff hSH).2 hx

theorem mem_normalizer_centralizer {S : Subgroup G} {m : G} (hm : m ∈ normalizer (S : Set G)) :
    m ∈ normalizer (centralizer (S : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hy s hs
    have hs' : m⁻¹ * s * m ∈ S := by
      have := (mem_normalizer_iff.mp ((normalizer _).inv_mem hm) s).mp hs
      simpa using this
    have h1 := hy _ hs'
    calc s * (m * y * m⁻¹) = m * ((m⁻¹ * s * m) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * s * m)) * m⁻¹ := by rw [h1]
      _ = m * y * m⁻¹ * s := by group
  · intro hy s hs
    have hs' : m * s * m⁻¹ ∈ S := (mem_normalizer_iff.mp hm s).mp hs
    have h1 := hy _ hs'
    have h2 : m * (s * y) * m⁻¹ = m * (y * s) * m⁻¹ := by
      calc m * (s * y) * m⁻¹ = m * s * m⁻¹ * (m * y * m⁻¹) := by group
        _ = m * y * m⁻¹ * (m * s * m⁻¹) := h1
        _ = m * (y * s) * m⁻¹ := by group
    have h3 := congrArg (fun z => m⁻¹ * z * m) h2
    simpa [mul_assoc] using h3

theorem conj_mem_rcSet {S P : Subgroup G} {m x : G} (hm : m ∈ normalizer (S : Set G))
    (hx : x ∈ rcSet S P) (hxm : m⁻¹ * x * m ∈ P) : m⁻¹ * x * m ∈ rcSet S P := by
  refine ⟨?_, hxm⟩
  have hC : conjSub m (centralizer (S : Set G)) = centralizer (S : Set G) :=
    conjSub_eq_of_mem_normalizer (mem_normalizer_centralizer hm)
  have h1 : m⁻¹ * x * m ∈ conjSub m ⁅centralizer (S : Set G), centralizer (S : Set G)⁆ :=
    conj_mem_conjSub hx.1
  unfold conjSub at h1 hC
  rwa [Subgroup.map_commutator, hC] at h1

end Defs

@[expose] def RcFor (p : ℕ) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow p G) (S : Subgroup G), S ≤ P → fusionStronglyClosed (S : Set G) P →
    fusionStronglyClosed ((rcSet S P : Subgroup G) : Set G) P

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem rcSet_stronglyClosed_of_local (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P)
    (hstep : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → FullyNormalized p P S₀ →
      (∀ S₁ : Subgroup G, S₁ ≤ S → Nat.card S₀ < Nat.card S₁ → LocalRc S P S₁) →
      LocalRc S P S₀) :
    fusionStronglyClosed ((rcSet S P : Subgroup G) : Set G) P := by
  by_cases hS1 : S = ⊥
  · subst hS1
    intro x hx g hg
    refine ⟨?_, hg⟩
    have hc : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [coe_bot, centralizer_eq_top_iff_subset]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact (center G).one_mem
    have hxc := hx.1
    rw [hc] at hxc ⊢
    have := (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).conj_mem x hxc g⁻¹
    simpa [mul_assoc] using this
  have hdesc := descent P hSP hS hS1 (rcRel_equivalence S P) fun S₀ h1 h2 h3 h4 =>
    respects_of_localRc (hstep S₀ h1 h2 h3 fun S₁ h5 h6 =>
      localRc_of_respects h5 (h4 S₁ h5 h6))
  intro x hx g hg
  have hconj : rconj g {x} = {g⁻¹ * x * g} := by
    ext z
    simp only [mem_rconj, Set.mem_singleton_iff]
    constructor
    · intro hz; rw [← hz]; group
    · intro hz; rw [hz]; group
  have h1 := (hdesc {x} (Set.singleton_subset_iff.mpr (rcSet_le S P hx)) g
    (by rw [hconj]; exact Set.singleton_subset_iff.mpr hg)).mp (Set.singleton_subset_iff.mpr hx)
  rw [hconj] at h1
  exact Set.singleton_subset_iff.mp h1

end CFSG.Goldschmidt75
