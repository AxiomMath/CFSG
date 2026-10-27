module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocal

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def IsMaximalEscapingPair {G : Type} [Group G] (M U : Subgroup G) (u : G)
    (L : Subgroup G) : Prop :=
  u ∈ U ∧ u ≠ 1 ∧ ¬ Subgroup.centralizer ({u} : Set G) ≤ M ∧
    IsComponentIn L (Subgroup.centralizer ({u} : Set G)) ∧
    ∀ j ∈ U, j ≠ 1 → ¬ Subgroup.centralizer ({j} : Set G) ≤ M →
      ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({j} : Set G)) →
        Nat.card K ≤ Nat.card L

namespace BenderBranch

variable {G : Type} [Group G] [Finite G] {T M U : Subgroup G} {z : G}

theorem exists_maximalEscapingPair (hd : UniqueFusionDatum T M U z)
    (hJ : ∃ u ∈ U, u ≠ 1 ∧ ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    ∃ u L, IsMaximalEscapingPair M U u L := by
  classical
  let S : Set (G × Subgroup G) := {p | p.1 ∈ U ∧ p.1 ≠ 1 ∧
    ¬ Subgroup.centralizer ({p.1} : Set G) ≤ M ∧
    IsComponentIn p.2 (Subgroup.centralizer ({p.1} : Set G))}
  obtain ⟨u₀, hu₀, hu₀1, hu₀M⟩ := hJ
  have hne : S.Nonempty := by
    obtain ⟨-, ⟨L', hL'⟩, -⟩ := hd.escaping_centralizer_odd_core_components hu₀ hu₀1 hu₀M
    exact ⟨(u₀, L'.map (Subgroup.centralizer ({u₀} : Set G)).subtype), hu₀, hu₀1, hu₀M,
      isComponentIn_of_isComponent hL'⟩
  obtain ⟨⟨u, L⟩, hp, hmax⟩ := Set.exists_max_image S (fun p => Nat.card p.2) (Set.toFinite S) hne
  exact ⟨u, L, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, fun j hj hj1 hjM K hK =>
    hmax (j, K) ⟨hj, hj1, hjM, hK⟩⟩

theorem not_le_of_isComponentIn (hd : UniqueFusionDatum T M U z) {u : G} (hu : u ∈ U)
    (hu1 : u ≠ 1) (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) {L : Subgroup G}
    (hL : IsComponentIn L (Subgroup.centralizer ({u} : Set G))) : ¬ L ≤ M := by
  obtain ⟨-, -, h⟩ := hd.escaping_centralizer_odd_core_components hu hu1 hH
  obtain ⟨L', hL', rfl⟩ := exists_isComponent_of_isComponentIn hL
  exact h L' hL'

structure PairRecognition (M U L : Subgroup G) : Prop where
  simple : IsSimpleGroup L
  nonabelian : ∃ a b : L, a * b ≠ b * a
  normalizes : U ≤ Subgroup.normalizer (L : Set G)
  card_ge : 4 ≤ Nat.card ↥(U ⊓ L)
  sup_eq : (U ⊓ L) ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) = U
  inf_eq : (U ⊓ L) ⊓ (U ⊓ Subgroup.centralizer (L : Set G)) = ⊥
  le_M : L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) ≤ M
  trivial_on : ∀ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G),
    ∀ c ∈ U ⊓ Subgroup.centralizer (L : Set G), n⁻¹ * c * n = c
  transitive : ∀ a ∈ U ⊓ L, ∀ b ∈ U ⊓ L, a ≠ 1 → b ≠ 1 →
    ∃ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G), n⁻¹ * a * n = b
  free : ∀ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G), ∀ a ∈ U ⊓ L, a ≠ 1 →
    n⁻¹ * a * n = a → ∀ x ∈ U, n⁻¹ * x * n = x
  cyclic : ∃ g ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G),
    ∀ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G), ∃ k : ℕ,
      ∀ x ∈ U, n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k

theorem isPGroup_two (hd : UniqueFusionDatum T M U z) : IsPGroup 2 U := by
  intro x
  exact ⟨1, Subtype.ext (by simpa using hd.elem.2 x x.2)⟩

theorem le_centralizer_of_mem (hd : UniqueFusionDatum T M U z) {u : G} (hu : u ∈ U) :
    U ≤ Subgroup.centralizer ({u} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hd.elem.1.is_comm.comm (⟨x, hx⟩ : U) ⟨u, hu⟩
  exact congrArg Subtype.val this

theorem mul_comm_of_mem (hd : UniqueFusionDatum T M U z) {a b : G} (ha : a ∈ U) (hb : b ∈ U) :
    a * b = b * a :=
  congrArg Subtype.val (hd.elem.1.is_comm.comm (⟨a, ha⟩ : U) ⟨b, hb⟩)

theorem pairRecognition (hrec : LocalComponentRecognition) (hd : UniqueFusionDatum T M U z)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    {L : Subgroup G} (hL : IsComponentIn L (Subgroup.centralizer ({u} : Set G))) :
    PairRecognition M U L := by
  obtain ⟨S, hS, hUS⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge
    (le_centralizer_of_mem hd hu) (isPGroup_two hd)
  obtain ⟨h1, h2, -, h4, -, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    hrec G T M U z hd u hu hu1 hH S hS hUS L hL
  exact ⟨h1, h2, h4, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem conjugate_U_eq (hd : UniqueFusionDatum T M U z) {g : G} (hg : g ∈ M) :
    CFSG.conjugate U g = U :=
  conjugate_eq_iff_mem_normalizer.mpr (hd.normal hg)

omit [Finite G] in
theorem conjugate_M_eq {g : G} (hg : g ∈ M) : CFSG.conjugate M g = M :=
  conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)

theorem conj_mem_U (hd : UniqueFusionDatum T M U z) {g u : G} (hg : g ∈ M) (hu : u ∈ U) :
    g⁻¹ * u * g ∈ U := by
  have h1 : u ∈ CFSG.conjugate U g⁻¹ := by
    rw [conjugate_U_eq hd (M.inv_mem hg)]
    exact hu
  simpa using mem_conjugate_iff.mp h1

theorem _root_.CFSG.QuasithinUnique.IsMaximalEscapingPair.conj
    (hd : UniqueFusionDatum T M U z) {u : G} {L : Subgroup G}
    (h : IsMaximalEscapingPair M U u L) {g : G} (hg : g ∈ M) :
    IsMaximalEscapingPair M U (g⁻¹ * u * g) (CFSG.conjugate L g) := by
  obtain ⟨hu, hu1, huM, hL, hmax⟩ := h
  refine ⟨conj_mem_U hd hg hu, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hu1
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h1]
    group
  · intro hle
    apply huM
    have h1 : CFSG.conjugate (Subgroup.centralizer ({u} : Set G)) g =
        Subgroup.centralizer ({g⁻¹ * u * g} : Set G) := conjugate_centralizer_singleton u g
    intro x hx
    have h2 : x ∈ CFSG.conjugate (CFSG.conjugate (Subgroup.centralizer ({u} : Set G)) g) g⁻¹ := by
      rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
      exact hx
    have h3 := conjugate_mono
      (h1 ▸ hle : CFSG.conjugate (Subgroup.centralizer ({u} : Set G)) g ≤ M) g⁻¹ h2
    rwa [conjugate_M_eq (M.inv_mem hg)] at h3
  · have := isComponentIn_map (MulAut.conj g⁻¹) hL
    rw [← conjugate_centralizer_singleton]
    exact this
  · intro j hj hj1 hjM K hK
    have := hmax j hj hj1 hjM K hK
    rwa [card_conjugate]

theorem propagation_aux (hrec : LocalComponentRecognition)
    (hemb : ComponentEmbeddingUnderInvolution) (hd : UniqueFusionDatum T M U z) {u : G}
    {L : Subgroup G} (h : IsMaximalEscapingPair M U u L) {v : G}
    (hv : v ∈ U ⊓ Subgroup.centralizer (L : Set G)) (hv1 : v ≠ 1) :
    ¬ Subgroup.centralizer ({v} : Set G) ≤ M ∧
      IsComponentIn L (Subgroup.centralizer ({v} : Set G)) := by
  obtain ⟨hu, hu1, huM, hL, hmax⟩ := h
  obtain ⟨hvU, hvC⟩ := Subgroup.mem_inf.mp hv
  have hLv : L ≤ Subgroup.centralizer ({v} : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hvC l hl
  have hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ M := fun hle =>
    not_le_of_isComponentIn hd hu hu1 huM hL (hLv.trans hle)
  refine ⟨hvM, ?_⟩
  have hodd := (hd.escaping_centralizer_odd_core_components hvU hv1 hvM).1
  have hnorm : ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({v} : Set G)) →
      U ≤ Subgroup.normalizer (K : Set G) := fun K hK =>
    (pairRecognition hrec hd hvU hv1 hvM hK).normalizes
  have hLvu : IsComponentIn L
      (Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) :=
    isComponentIn_of_le hL (le_inf hLv hL.1) inf_le_right
  obtain ⟨K, hK, hLK⟩ := hemb G T M U z hd v hvU hv1 hodd hnorm u hu L hLvu
  have hcard := hmax v hvU hv1 hvM K hK
  have hKL : L = K := Subgroup.eq_of_le_of_card_ge hLK hcard
  rwa [hKL]

omit [Finite G] in
theorem inf_centralizer_ne_U {L : Subgroup G} (hr : PairRecognition M U L) :
    U ⊓ Subgroup.centralizer (L : Set G) ≠ U := fun hCU => by
  have h1 := hr.inf_eq
  rw [hCU, inf_eq_left.mpr inf_le_left] at h1
  have := hr.card_ge
  rw [h1, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem inf_centralizer_ne_bot {u : G} {L : Subgroup G} (h : IsMaximalEscapingPair M U u L) :
    U ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := fun hbot => by
  have huC : u ∈ U ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨h.1, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.2.2.2.1.1 hl)⟩
  rw [hbot, Subgroup.mem_bot] at huC
  exact h.2.1 huC

end BenderBranch

end CFSG.QuasithinUnique
