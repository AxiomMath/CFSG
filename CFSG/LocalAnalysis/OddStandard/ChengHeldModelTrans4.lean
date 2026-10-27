module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelCard

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.ChengHeld.M1b (evalE)

namespace SFacts4Aux

variable {G : Type} [Group G]

theorem map_top_subtype (S : Subgroup G) : (⊤ : Subgroup ↥S).map S.subtype = S := by
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem coe_mem_map (S : Subgroup G) (K : Subgroup ↥S) (a : ↥S) :
    (a : G) ∈ K.map S.subtype ↔ a ∈ K :=
  mem_map_iff_mem S.subtype_injective

theorem map_inf_centralizer (S : Subgroup G) (K L : Subgroup ↥S) :
    (K ⊓ centralizer (L : Set ↥S)).map S.subtype =
      K.map S.subtype ⊓ centralizer ((L.map S.subtype : Subgroup G) : Set G) := by
  ext a
  simp only [mem_inf, mem_map, mem_centralizer_iff, coe_map, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨h, ⟨hK, hL⟩, rfl⟩
    refine ⟨⟨h, hK, rfl⟩, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, hL l hl]
  · rintro ⟨⟨h, hK, rfl⟩, hc⟩
    refine ⟨h, ⟨hK, fun l hl => S.subtype_injective ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc _ ⟨l, hl, rfl⟩

theorem map_center (S : Subgroup G) :
    (center ↥S).map S.subtype = S ⊓ centralizer (S : Set G) := by
  rw [← centralizer_univ, ← coe_top, ← top_inf_eq (centralizer _), map_inf_centralizer,
    map_top_subtype]

theorem card_map (S : Subgroup G) (K : Subgroup ↥S) : Nat.card (K.map S.subtype) = Nat.card K :=
  card_map_of_injective S.subtype_injective

theorem comm_map_iff (S : Subgroup G) (K : Subgroup ↥S) :
    (∀ a ∈ K.map S.subtype, ∀ b ∈ K.map S.subtype, a * b = b * a) ↔
      ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
  constructor
  · intro h a ha b hb
    refine S.subtype_injective ?_
    rw [map_mul, map_mul]
    exact h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h a ha b hb]

theorem ncard_eq (S : Subgroup G) (P : G → Prop) (Q : ↥S → Prop) (hPS : ∀ s, P s → s ∈ S)
    (hPQ : ∀ a : ↥S, P a ↔ Q a) : {s : G | P s}.ncard = {a : ↥S | Q a}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext s
  constructor
  · intro hs
    exact ⟨⟨s, hPS s hs⟩, (hPQ _).1 hs, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (hPQ a).2 ha

theorem ncard_map (S : Subgroup G) (K Z : Subgroup ↥S) (P : G → Prop) (Q : ↥S → Prop)
    (hPQ : ∀ a : ↥S, P a ↔ Q a) :
    {s : G | s ∈ K.map S.subtype ∧ s ∉ Z.map S.subtype ∧ P s}.ncard =
      {a : ↥S | a ∈ K ∧ a ∉ Z ∧ Q a}.ncard := by
  refine ncard_eq S _ _ ?_ ?_
  · rintro s ⟨⟨a, -, rfl⟩, -⟩
    exact a.2
  · intro a
    rw [coe_mem_map, coe_mem_map, hPQ]

end SFacts4Aux

section Charts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

namespace SFacts4Aux

open Chart4

variable {α : ℕ}

theorem map_sD (c : Chart4 d α) : (sD c.fam).map d.S.subtype = c.D := by
  rw [sD, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_sR1 (c : Chart4 d α) : (sR1 c.fam).map d.S.subtype = c.R1 := by
  rw [sR1, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_sR2 (c : Chart4 d α) : (sR2 c.fam).map d.S.subtype = c.R2 := by
  rw [sR2, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_sV (c : Chart4 d α) : (sV c.fam).map d.S.subtype = c.V := by
  rw [sV, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    Chart4.V, c.q_eq]
  rfl

theorem map_sW (c : Chart4 d α) : (sW c.fam).map d.S.subtype = c.W := by
  rw [sW, ← top_inf_eq (centralizer _), map_inf_centralizer, map_top_subtype, map_sV]
  rfl

theorem map_zt (c : Chart4 d α) : (zpowers (c.fam 0)).map d.S.subtype = zpowers c.t := by
  rw [MonoidHom.map_zpowers]
  rfl

end SFacts4Aux

open SFacts4Aux

theorem Chart4.sFacts_sub {α : ℕ} (c : Chart4 d α) (hS : Struct4Facts α ↥d.S c.fam) :
    d.S ⊓ centralizer (d.S : Set G) = zpowers c.t ∧ ⁅d.S, d.S⁆ = c.D ∧
      Nat.card c.D = 16 ∧ Nat.card c.R1 = 64 ∧ Nat.card c.R2 = 64 ∧ c.R1 ⊓ c.R2 = c.D ∧
      c.R1 ⊓ centralizer (c.R1 : Set G) = zpowers c.t ∧
      c.R2 ⊓ centralizer (c.R2 : Set G) = zpowers c.t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_center, hS.center, map_zt]
  · rw [← map_sD, ← hS.commutator, map_commutator, map_top_subtype]
  · rw [← map_sD, card_map, hS.card_D]
  · rw [← map_sR1, card_map, hS.card_R1]
  · rw [← map_sR2, card_map, hS.card_R2]
  · rw [← map_sR1, ← map_sR2, ← map_sD, ← hS.inf_R, Subgroup.map_inf _ _ _ d.S.subtype_injective]
  · rw [← map_sR1, ← map_inf_centralizer, hS.center_R1, map_zt]
  · rw [← map_sR2, ← map_inf_centralizer, hS.center_R2, map_zt]

theorem Chart4.sFacts_count {α : ℕ} (c : Chart4 d α) (hS : Struct4Facts α ↥d.S c.fam) :
    {s : G | s ∈ d.S ∧ s ≠ 1 ∧ s * s = 1}.ncard = 55 ∧
      (∀ s ∈ d.S, s * s = 1 → s ∈ c.R1 ∨ s ∈ c.R2) ∧
      {s : G | s ∈ c.R1 ∧ s ∉ zpowers c.t ∧ s * s = 1}.ncard = 30 ∧
      {s : G | s ∈ c.R1 ∧ s ∉ zpowers c.t ∧ orderOf s = 4}.ncard = 30 ∧
      {s : G | s ∈ c.R2 ∧ s ∉ zpowers c.t ∧ s * s = 1}.ncard = 30 ∧
      {s : G | s ∈ c.R2 ∧ s ∉ zpowers c.t ∧ orderOf s = 4}.ncard = 30 := by
  have hsq : ∀ a : ↥d.S, (a : G) * a = 1 ↔ a * a = 1 := fun a => by
    rw [← Subgroup.coe_mul, OneMemClass.coe_eq_one]
  have hord : ∀ a : ↥d.S, orderOf (a : G) = 4 ↔ orderOf a = 4 := fun a => by
    rw [Subgroup.orderOf_coe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hS.involutions]
    refine ncard_eq d.S _ _ (fun s hs => hs.1) fun a => ?_
    rw [hsq, Ne, OneMemClass.coe_eq_one]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  · intro s hs h
    rw [← map_sR1, ← map_sR2]
    rcases hS.involutions_mem ⟨s, hs⟩ (Subtype.ext h) with h1 | h2
    · exact Or.inl ⟨_, h1, rfl⟩
    · exact Or.inr ⟨_, h2, rfl⟩
  · rw [← map_sR1, ← map_zt, ncard_map d.S _ _ _ _ hsq, hS.R1_invol]
  · rw [← map_sR1, ← map_zt, ncard_map d.S _ _ _ _ hord, hS.R1_ord4]
  · rw [← map_sR2, ← map_zt, ncard_map d.S _ _ _ _ hsq, hS.R2_invol]
  · rw [← map_sR2, ← map_zt, ncard_map d.S _ _ _ _ hord, hS.R2_ord4]

theorem Chart4.sFacts_V {α : ℕ} (c : Chart4 d α) (hS : Struct4Facts α ↥d.S c.fam) :
    (∀ s ∈ d.S, s ^ 2 ≠ c.t ∧ s ^ 2 ≠ c.t⁻¹) ∧
      (∀ E : Subgroup G, E ≤ d.S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
        (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 8) ∧
      (∀ a ∈ c.V, ∀ b ∈ c.V, a * b = b * a) ∧ (∀ a ∈ c.V, a * a = 1) ∧
      Nat.card c.V = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨h1, h2⟩ := hS.no_root ⟨s, hs⟩
    exact ⟨fun h => h1 (Subtype.ext h), fun h => h2 (Subtype.ext h)⟩
  · intro E hE hcomm hsq
    have h := hS.elemAb_le (E.subgroupOf d.S)
      (fun a ha b hb => Subtype.ext (hcomm _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb)))
      (fun a ha => Subtype.ext (hsq _ (mem_subgroupOf.1 ha)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv] at h
  · rw [← map_sV, comm_map_iff]
    exact hS.V_comm
  · rw [← map_sV]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hS.V_sq a ha, map_one]
  · rw [← map_sV, card_map, hS.card_V]

theorem Chart4.sFacts_W {α : ℕ} (c : Chart4 d α) (hS : Struct4Facts α ↥d.S c.fam) :
    Nat.card c.W = 64 ∧ ((∀ a ∈ c.W, ∀ b ∈ c.W, a * b = b * a) ↔ α = 0) ∧
      (∀ a ∈ c.W, a * a = 1 → a ∈ c.V) ∧ (∀ a ∈ c.W, orderOf a ≠ 8) ∧
      (α = 1 → c.W ⊓ centralizer (c.W : Set G) = closure {c.t, c.pi, c.t * c.tau}) ∧
      (α = 1 → ⁅c.W, c.W⁆ = zpowers (c.t ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_sW, card_map, hS.card_W]
  · rw [← map_sW, comm_map_iff]
    exact hS.W_comm_iff
  · rw [← map_sW, ← map_sV]
    rintro _ ⟨a, ha, rfl⟩ h
    refine ⟨a, hS.W_invol a ha (d.S.subtype_injective ?_), rfl⟩
    rw [map_mul, map_one]
    exact h
  · rw [← map_sW]
    rintro _ ⟨a, ha, rfl⟩
    rw [orderOf_injective _ d.S.subtype_injective]
    exact hS.W_ord8 a ha
  · intro h1
    rw [← map_sW, ← map_inf_centralizer, hS.W_center h1, MonoidHom.map_closure,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rfl
  · intro h1
    rw [← map_sW, ← map_commutator, hS.W_commutator h1, MonoidHom.map_zpowers]
    rfl

theorem Chart4.sFacts_words {α : ℕ} (c : Chart4 d α) (hS : Struct4Facts α ↥d.S c.fam) :
    (c.mu * c.lam * c.xi * c.tau) ^ 2 = c.pi ∧
      (cm (c.mu * c.lam * c.xi) (c.mu * c.ze * c.xi) = 1 ↔ α = 0) := by
  refine ⟨congrArg Subtype.val hS.sq_mlxt, ?_⟩
  rw [← hS.comm_mlx]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem Chart4.sFacts_of {α : ℕ} (c : Chart4 d α) (hS : Struct4Facts α ↥d.S c.fam)
    (hcard : Nat.card ↥d.S = 256) : c.SFacts := by
  obtain ⟨hZ, hD', hD, hR1, hR2, hR, hZ1, hZ2⟩ := c.sFacts_sub hS
  obtain ⟨hI, hIm, hI1, hO1, hI2, hO2⟩ := c.sFacts_count hS
  obtain ⟨hr, hE, hVc, hVs, hV⟩ := c.sFacts_V hS
  obtain ⟨hW, hWc, hWi, hW8, hWZ, hWD⟩ := c.sFacts_W hS
  obtain ⟨hsq, hcm⟩ := c.sFacts_words hS
  exact ⟨hcard, c.orderOf_t, hZ, hD', hD, hR1, hR2, hR, hZ1, hZ2, hI, hIm, hI1, hO1, hI2, hO2,
    hr, hE, hVc, hVs, hV, hW, hWc, hWi, hW8, hWZ, hWD, hsq, hcm⟩

end Charts

end CFSG.OddStandard.ChengHeld
