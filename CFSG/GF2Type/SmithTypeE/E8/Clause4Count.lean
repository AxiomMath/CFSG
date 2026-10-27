module

public import CFSG.LargeExtraspecial.S3Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.LargeExtraspecial

theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
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

theorem card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
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

theorem card_le_mul_card_orbit {G : Type*} [Group G] [Finite G] (H : Subgroup G) (x : G) {n : ℕ}
    (hn : Nat.card (Set.range fun h : H => (h : G) * x * (h : G)⁻¹) ≤ n) :
    Nat.card H ≤ n * Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have h1 := card_conj_orbit H.subtype x
  have h2 := Subgroup.card_mul_index ((centralizer ({x} : Set G)).comap H.subtype)
  have h3 : Nat.card ((centralizer ({x} : Set G)).comap H.subtype) =
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have e := Subgroup.inf_subgroupOf_left (centralizer ({x} : Set G)) H
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : H ⊓ centralizer ({x} : Set G) ≤ H)).toEquiv, e]
    rfl
  have h4 : ((centralizer ({x} : Set G)).comap H.subtype).index ≤ n := by
    rw [← h1]
    exact hn
  rw [← h3, ← h2]
  calc Nat.card ((centralizer ({x} : Set G)).comap H.subtype) *
        ((centralizer ({x} : Set G)).comap H.subtype).index
      ≤ Nat.card ((centralizer ({x} : Set G)).comap H.subtype) * n := Nat.mul_le_mul_left _ h4
    _ = n * Nat.card ((centralizer ({x} : Set G)).comap H.subtype) := mul_comm _ _

variable {G : Type} [Group G] [Finite G]

theorem card_QG_le_two_mul (S : Setting G) {v : G} (hv : v ∈ S.QG) :
    Nat.card S.QG ≤ 2 * Nat.card (S.QG ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  refine card_le_mul_card_orbit S.QG v ?_
  have hsub : (Set.range fun h : S.QG => (h : G) * v * (h : G)⁻¹) ⊆ {v, S.z * v} := by
    rintro _ ⟨q, rfl⟩
    rcases S.commutator_eq_one_or_z q.2 hv with h | h
    · left
      calc (q : G) * v * (q : G)⁻¹ = (q : G) * v * (q : G)⁻¹ * v⁻¹ * v := by group
        _ = v := by rw [h, one_mul]
    · right
      calc (q : G) * v * (q : G)⁻¹ = (q : G) * v * (q : G)⁻¹ * v⁻¹ * v := by group
        _ = S.z * v := by rw [h]
  calc Nat.card (Set.range fun h : S.QG => (h : G) * v * (h : G)⁻¹)
      = (Set.range fun h : S.QG => (h : G) * v * (h : G)⁻¹).ncard := Nat.card_coe_set_eq _
    _ ≤ ({v, S.z * v} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      refine (Set.ncard_insert_le v {S.z * v}).trans ?_
      rw [Set.ncard_singleton]

theorem card_QG_le_of_orbit (S : Setting G) {v x : G} (hv : v ∈ S.QG) {n : ℕ}
    (hn : Nat.card (Set.range fun y : ↥(S.QG ⊓ centralizer ({v} : Set G)) =>
      (y : G) * x * (y : G)⁻¹) ≤ n) :
    Nat.card S.QG ≤ 2 * n * Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have h1 := card_QG_le_two_mul S hv
  have h2 := card_le_mul_card_orbit (S.QG ⊓ centralizer ({v} : Set G)) x hn
  have h3 : Nat.card ((S.QG ⊓ centralizer ({v} : Set G)) ⊓ centralizer ({x} : Set G) :
      Subgroup G) ≤ Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
  calc Nat.card S.QG ≤ 2 * Nat.card (S.QG ⊓ centralizer ({v} : Set G) : Subgroup G) := h1
    _ ≤ 2 * (n * Nat.card ((S.QG ⊓ centralizer ({v} : Set G)) ⊓ centralizer ({x} : Set G) :
        Subgroup G)) := Nat.mul_le_mul_left _ h2
    _ ≤ 2 * (n * Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = 2 * n * Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) := by ring

end CFSG.GF2Type.SmithTypeE.E8
