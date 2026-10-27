module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelCard

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.ChengHeld.M1b (evalE)

namespace Chart2Aux

section Generic

variable {G : Type} [Group G]

theorem map_top_subtype (S : Subgroup G) : (⊤ : Subgroup ↥S).map S.subtype = S := by
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem map_center (S : Subgroup G) :
    (center ↥S).map S.subtype = S ⊓ centralizer (S : Set G) := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, fun b hb => congrArg Subtype.val ((Subgroup.mem_center_iff.1 hs) ⟨b, hb⟩)⟩
  · rintro ⟨ha, hc⟩
    refine ⟨⟨a, ha⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 hc g g.2

theorem map_commutator_top (S : Subgroup G) :
    (⁅(⊤ : Subgroup ↥S), ⊤⁆ : Subgroup ↥S).map S.subtype = ⁅S, S⁆ := by
  rw [Subgroup.map_commutator, map_top_subtype]

theorem comm_map (S : Subgroup G) {K : Subgroup ↥S} (h : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) :
    ∀ a ∈ K.map S.subtype, ∀ b ∈ K.map S.subtype, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

theorem sq_map (S : Subgroup G) {K : Subgroup ↥S} (h : ∀ a ∈ K, a * a = 1) :
    ∀ a ∈ K.map S.subtype, a * a = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_mul, h a ha, map_one]

theorem ncard_invol (S : Subgroup G) :
    {s : G | s ∈ S ∧ s ≠ 1 ∧ s * s = 1}.ncard = {a : ↥S | a ≠ 1 ∧ a * a = 1}.ncard := by
  rw [← Set.ncard_image_of_injective _ S.subtype_injective]
  congr 1
  ext s
  constructor
  · rintro ⟨hs, h1, h2⟩
    exact ⟨⟨s, hs⟩, ⟨fun h => h1 (congrArg Subtype.val h), Subtype.ext h2⟩, rfl⟩
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨a.2, fun h => h1 (Subtype.ext h), congrArg Subtype.val h2⟩

theorem card_subgroupOf {S E : Subgroup G} (hE : E ≤ S) :
    Nat.card (E.subgroupOf S) = Nat.card E :=
  Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv

theorem comm_subgroupOf (S : Subgroup G) {E : Subgroup G}
    (h : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∀ a ∈ E.subgroupOf S, ∀ b ∈ E.subgroupOf S, a * b = b * a :=
  fun a ha b hb => Subtype.ext (h a (mem_subgroupOf.1 ha) b (mem_subgroupOf.1 hb))

theorem sq_subgroupOf (S : Subgroup G) {E : Subgroup G} (h : ∀ a ∈ E, a * a = 1) :
    ∀ a ∈ E.subgroupOf S, a * a = 1 :=
  fun a ha => Subtype.ext (h a (mem_subgroupOf.1 ha))

theorem elemAb_le (S : Subgroup G) {n : ℕ}
    (h : ∀ E : Subgroup ↥S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) →
      Nat.card E ≤ n) :
    ∀ E : Subgroup G, E ≤ S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E ≤ n := by
  intro E hE hc hs
  rw [← card_subgroupOf hE]
  exact h _ (comm_subgroupOf S hc) (sq_subgroupOf S hs)

theorem elemAb_eq (S : Subgroup G) {n : ℕ} {R₁ R₂ : Subgroup ↥S}
    (h : ∀ E : Subgroup ↥S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) →
      Nat.card E = n → E = R₁ ∨ E = R₂) :
    ∀ E : Subgroup G, E ≤ S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = n → E = R₁.map S.subtype ∨ E = R₂.map S.subtype := by
  intro E hE hc hs hn
  rw [← card_subgroupOf hE] at hn
  rw [← map_subgroupOf_eq_of_le hE]
  exact (h _ (comm_subgroupOf S hc) (sq_subgroupOf S hs) hn).imp
    (congrArg (map S.subtype)) (congrArg (map S.subtype))

theorem no_root (S : Subgroup G) {x : ↥S} (h : ∀ s : ↥S, s ^ 2 ≠ x) :
    ∀ s ∈ S, s ^ 2 ≠ (x : G) := by
  intro s hs hsq
  refine h ⟨s, hs⟩ (Subtype.ext ?_)
  rw [SubgroupClass.coe_pow]
  exact hsq

theorem root (S : Subgroup G) {x : ↥S} (h : ∃ s : ↥S, s ^ 2 = x) :
    ∃ s ∈ S, s ^ 2 = (x : G) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, s.2, by rw [← SubgroupClass.coe_pow, hs]⟩

end Generic

section Charts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem map_sD (c : Chart2 d) : (sD c.fam).map d.S.subtype = c.D := by
  rw [sD, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_sR1 (c : Chart2 d) : (sR1 c.fam).map d.S.subtype = c.R1 := by
  rw [sR1, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_sR2 (c : Chart2 d) : (sR2 c.fam).map d.S.subtype = c.R2 := by
  rw [sR2, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

theorem center_derived (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    d.S ⊓ centralizer (d.S : Set G) = c.D ∧ ⁅d.S, d.S⁆ = c.D := by
  refine ⟨?_, ?_⟩
  · rw [← map_center, hS.center, map_sD]
  · rw [← map_commutator_top, hS.commutator, map_sD]

theorem cards (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    Nat.card c.D = 8 ∧ Nat.card c.R1 = 32 ∧ Nat.card c.R2 = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_sD, card_map_of_injective d.S.subtype_injective, hS.card_D]
  · rw [← map_sR1, card_map_of_injective d.S.subtype_injective, hS.card_R1]
  · rw [← map_sR2, card_map_of_injective d.S.subtype_injective, hS.card_R2]

theorem elemAb_R (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    (∀ a ∈ c.R1, ∀ b ∈ c.R1, a * b = b * a) ∧ (∀ a ∈ c.R1, a * a = 1) ∧
      (∀ a ∈ c.R2, ∀ b ∈ c.R2, a * b = b * a) ∧ (∀ a ∈ c.R2, a * a = 1) ∧
      c.R1 ⊓ c.R2 = c.D := by
  rw [← map_sR1, ← map_sR2]
  refine ⟨comm_map d.S hS.R1_comm, sq_map d.S hS.R1_sq, comm_map d.S hS.R2_comm,
    sq_map d.S hS.R2_sq, ?_⟩
  rw [← map_inf_eq _ _ _ d.S.subtype_injective, hS.inf_R, map_sD]

theorem invols (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    {s : G | s ∈ d.S ∧ s ≠ 1 ∧ s * s = 1}.ncard = 55 ∧
      ∀ s ∈ d.S, s * s = 1 → s ∈ c.R1 ∨ s ∈ c.R2 := by
  refine ⟨by rw [ncard_invol, hS.involutions], ?_⟩
  intro s hs h2
  rw [← map_sR1, ← map_sR2]
  exact (hS.involutions_mem ⟨s, hs⟩ (Subtype.ext h2)).imp (fun h => ⟨_, h, rfl⟩)
    (fun h => ⟨_, h, rfl⟩)

theorem elemAbs (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    (∀ E : Subgroup G, E ≤ d.S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 32) ∧
    (∀ E : Subgroup G, E ≤ d.S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = c.R1 ∨ E = c.R2) := by
  refine ⟨elemAb_le d.S hS.elemAb_le, ?_⟩
  rw [← map_sR1, ← map_sR2]
  exact elemAb_eq d.S hS.elemAb_32

theorem roots (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    (∀ s ∈ d.S, s ^ 2 ≠ d.q) ∧ (∃ s ∈ d.S, s ^ 2 = c.pi) ∧ (∃ s ∈ d.S, s ^ 2 = d.q * c.pi) ∧
      (∃ s ∈ d.S, s ^ 2 = c.tau) ∧ (∃ s ∈ d.S, s ^ 2 = d.q * c.tau) :=
  ⟨no_root d.S hS.no_root_q, root d.S hS.root_pi, root d.S hS.root_qpi, root d.S hS.root_tau,
    root d.S hS.root_qtau⟩

theorem squares (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam) :
    (c.mu * c.lam * c.xi) ^ 2 = c.pi ∧ (c.mu * c.ze) ^ 2 = d.q * c.pi := by
  have h1 := congrArg Subtype.val hS.sq_mlx
  have h2 := congrArg Subtype.val hS.sq_mz
  rw [SubgroupClass.coe_pow] at h1 h2
  exact ⟨h1, h2⟩

end Charts

end Chart2Aux

section Charts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem Chart2.sFacts_of (c : Chart2 d) (hS : Struct2Facts ↥d.S c.fam)
    (hcard : Nat.card ↥d.S = 128) : c.SFacts := by
  obtain ⟨hZ, hD⟩ := Chart2Aux.center_derived c hS
  obtain ⟨hcD, hc1, hc2⟩ := Chart2Aux.cards c hS
  obtain ⟨h1c, h1s, h2c, h2s, hinf⟩ := Chart2Aux.elemAb_R c hS
  obtain ⟨hinv, hinvm⟩ := Chart2Aux.invols c hS
  obtain ⟨hle, h32⟩ := Chart2Aux.elemAbs c hS
  obtain ⟨hq, hpi, hqpi, htau, hqtau⟩ := Chart2Aux.roots c hS
  obtain ⟨hmlx, hmz⟩ := Chart2Aux.squares c hS
  exact ⟨hcard, hZ, hD, hcD, hc1, hc2, h1c, h1s, h2c, h2s, hinf, hinv, hinvm, hle, h32, hq, hpi,
    hqpi, htau, hqtau, hmlx, hmz⟩

end Charts

end CFSG.OddStandard.ChengHeld
