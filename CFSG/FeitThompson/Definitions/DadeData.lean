module

public import Mathlib.GroupTheory.Complement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

structure IsDadeData [Finite G] (L : Subgroup G) (A : Set G) (H : G → Subgroup G) : Prop where
  subset_sdiff : A ⊆ (L : Set G) \ {1}
  conj_mem : ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃x : G⦄, x ∈ L → x * a * x⁻¹ ∈ A
  fusion : ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃b : G⦄, b ∈ A → IsConj a b → ∃ x ∈ L, x * a * x⁻¹ = b
  le_centralizer : ∀ ⦃a : G⦄, a ∈ A → H a ≤ Subgroup.centralizer {a}
  normal_subgroupOf : ∀ ⦃a : G⦄, a ∈ A → ((H a).subgroupOf (Subgroup.centralizer {a})).Normal
  inf_eq_bot : ∀ ⦃a : G⦄, a ∈ A → H a ⊓ (L ⊓ Subgroup.centralizer {a}) = ⊥
  mul_eq : ∀ ⦃a : G⦄, a ∈ A →
    (H a : Set G) * (↑(L ⊓ Subgroup.centralizer {a}) : Set G) = (Subgroup.centralizer {a} : Set G)
  coprime_card : ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃b : G⦄, b ∈ A →
    Nat.Coprime (Nat.card ↥(H a)) (Nat.card ↥(L ⊓ Subgroup.centralizer {b}))

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a b : G}

theorem mem_of_mem (hD : IsDadeData L A H) (ha : a ∈ A) : a ∈ L := (hD.subset_sdiff ha).1

theorem subset (hD : IsDadeData L A H) : A ⊆ (L : Set G) := fun _ ha => hD.mem_of_mem ha

theorem ne_one (hD : IsDadeData L A H) (ha : a ∈ A) : a ≠ 1 := by
  simpa using (hD.subset_sdiff ha).2

theorem one_notMem (hD : IsDadeData L A H) : (1 : G) ∉ A := fun h => hD.ne_one h rfl

theorem conj_mem_H (hD : IsDadeData L A H) (ha : a ∈ A) {x h : G}
    (hx : x ∈ Subgroup.centralizer ({a} : Set G)) (hh : h ∈ H a) : x * h * x⁻¹ ∈ H a :=
  (Subgroup.normal_subgroupOf_iff (hD.le_centralizer ha)).1 (hD.normal_subgroupOf ha) h x hh hx

theorem isComplement' (hD : IsDadeData L A H) (ha : a ∈ A) :
    Subgroup.IsComplement' ((H a).subgroupOf (Subgroup.centralizer ({a} : Set G)))
      ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
        (Subgroup.centralizer ({a} : Set G))) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    have hx : (x : G) ∈ H a ⊓ (L ⊓ Subgroup.centralizer ({a} : Set G)) :=
      ⟨Subgroup.mem_subgroupOf.1 hx1, Subgroup.mem_subgroupOf.1 hx2⟩
    rw [hD.inf_eq_bot ha] at hx
    exact Subtype.ext (by simpa using hx)
  · refine Set.eq_univ_of_forall fun x => ?_
    have hx : (x : G) ∈ (H a : Set G) * (↑(L ⊓ Subgroup.centralizer ({a} : Set G)) : Set G) := by
      rw [hD.mul_eq ha]; exact x.2
    obtain ⟨h, hh, k, hk, hxk⟩ := hx
    exact ⟨⟨h, hD.le_centralizer ha hh⟩, Subgroup.mem_subgroupOf.2 hh,
      ⟨k, hk.2⟩, Subgroup.mem_subgroupOf.2 hk, Subtype.ext hxk⟩

theorem card_mul_card (hD : IsDadeData L A H) (ha : a ∈ A) :
    Nat.card ↥(H a) * Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set G)) := by
  have h := (hD.isComplement' ha).card_mul_card
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hD.le_centralizer ha)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      L ⊓ Subgroup.centralizer ({a} : Set G) ≤ _)).toEquiv] at h

theorem sup_eq (hD : IsDadeData L A H) (ha : a ∈ A) :
    H a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) = Subgroup.centralizer ({a} : Set G) := by
  refine le_antisymm (sup_le (hD.le_centralizer ha) inf_le_right) fun x hx => ?_
  have hx' : x ∈ (H a : Set G) * (↑(L ⊓ Subgroup.centralizer ({a} : Set G)) : Set G) := by
    rw [hD.mul_eq ha]; exact hx
  obtain ⟨h, hh, k, hk, rfl⟩ := hx'
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)

theorem inf_eq_bot_left (hD : IsDadeData L A H) (ha : a ∈ A) : H a ⊓ L = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx' : x ∈ H a ⊓ (L ⊓ Subgroup.centralizer ({a} : Set G)) :=
    ⟨hx.1, hx.2, hD.le_centralizer ha hx.1⟩
  rw [hD.inf_eq_bot ha] at hx'
  exact hx'

theorem isConj_iff (hD : IsDadeData L A H) (ha : a ∈ A) (hb : b ∈ A) :
    IsConj a b ↔ ∃ x ∈ L, x * a * x⁻¹ = b :=
  ⟨hD.fusion ha hb, fun ⟨x, _, hx⟩ => _root_.isConj_iff.2 ⟨x, hx⟩⟩

end IsDadeData

theorem isDadeData_empty [Finite G] (L : Subgroup G) (H : G → Subgroup G) :
    IsDadeData L ∅ H where
  subset_sdiff := Set.empty_subset _
  conj_mem := by simp
  fusion := by simp
  le_centralizer := by simp
  normal_subgroupOf := by simp
  inf_eq_bot := by simp
  mul_eq := by simp
  coprime_card := by simp

end CFSG.FeitThompson
