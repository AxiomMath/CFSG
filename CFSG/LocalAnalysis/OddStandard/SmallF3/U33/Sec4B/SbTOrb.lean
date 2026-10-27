module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

private theorem card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
    Nat.card (Set.range fun c : H => σ c * F * (σ c)⁻¹) =
      ((centralizer ({F} : Set P)).comap σ).index := by
  refine card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, mem_centralizer_singleton_iff, map_mul, map_inv]
  constructor
  · intro h
    calc (σ a)⁻¹ * σ b * F = (σ a)⁻¹ * (σ b * F * (σ b)⁻¹) * σ b := by group
      _ = (σ a)⁻¹ * (σ a * F * (σ a)⁻¹) * σ b := by rw [h]
      _ = F * ((σ a)⁻¹ * σ b) := by group
  · intro h
    calc σ a * F * (σ a)⁻¹ = σ a * (F * ((σ a)⁻¹ * σ b)) * (σ b)⁻¹ := by group
      _ = σ a * ((σ a)⁻¹ * σ b * F) * (σ b)⁻¹ := by rw [h]
      _ = σ b * F * (σ b)⁻¹ := by group

theorem card_eq_ncard_conjIn_mul (K : Subgroup G) (x : G) :
    Nat.card K = (conjIn K x).ncard * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
  have hrange : conjIn K x = Set.range (fun c : K => (c : G) * x * (c : G)⁻¹) := by
    ext u
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
  have h1 : Nat.card ↥(Set.range fun c : K => (c : G) * x * (c : G)⁻¹) =
      ((centralizer ({x} : Set G)).comap K.subtype).index := card_conj_orbit K.subtype x
  have h2 := Subgroup.card_mul_index ((centralizer ({x} : Set G)).comap K.subtype)
  have h3 : Nat.card ↥((centralizer ({x} : Set G)).comap K.subtype) =
      Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
    have e := Subgroup.inf_subgroupOf_left (centralizer ({x} : Set G)) K
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : K ⊓ centralizer ({x} : Set G) ≤ K)).toEquiv, e]
    rfl
  rw [hrange, ← _root_.Nat.card_coe_set_eq (Set.range fun c : K => (c : G) * x * (c : G)⁻¹),
    h1, ← h2, ← h3]
  exact mul_comm _ _

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
