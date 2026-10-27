module

public import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

def dadeInter (H : G → Subgroup G) (B : Set G) : Subgroup G := ⨅ b ∈ B, H b

variable {H : G → Subgroup G} {B C : Set G} {a b x : G}

theorem mem_dadeInter_iff : x ∈ dadeInter H B ↔ ∀ b ∈ B, x ∈ H b := by
  simp [dadeInter, Subgroup.mem_iInf]

theorem dadeInter_le (hb : b ∈ B) : dadeInter H B ≤ H b := fun _ hx => mem_dadeInter_iff.1 hx b hb

theorem le_dadeInter {K : Subgroup G} (h : ∀ b ∈ B, K ≤ H b) : K ≤ dadeInter H B :=
  fun _ hx => mem_dadeInter_iff.2 fun b hb => h b hb hx

@[simp] theorem dadeInter_empty (H : G → Subgroup G) : dadeInter H (∅ : Set G) = ⊤ := by
  ext x; simp [mem_dadeInter_iff]

@[simp] theorem dadeInter_singleton (H : G → Subgroup G) (a : G) : dadeInter H {a} = H a := by
  ext x; simp [mem_dadeInter_iff]

theorem dadeInter_insert (H : G → Subgroup G) (a : G) (B : Set G) :
    dadeInter H (insert a B) = H a ⊓ dadeInter H B := by
  ext x; simp [mem_dadeInter_iff]

theorem dadeInter_union (H : G → Subgroup G) (B C : Set G) :
    dadeInter H (B ∪ C) = dadeInter H B ⊓ dadeInter H C := by
  ext x; simp [mem_dadeInter_iff, or_imp, forall_and]

theorem dadeInter_anti (h : B ⊆ C) : dadeInter H C ≤ dadeInter H B :=
  le_dadeInter fun _ hb => dadeInter_le (h hb)

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G}

theorem isPiNumber_compl_card_dadeInter (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty) :
    IsPiNumber (dadePrimes L A)ᶜ (Nat.card ↥(dadeInter H B)) := by
  obtain ⟨b, hb⟩ := hB
  exact (hD.isPiNumber_compl_card_H (hBA hb)).of_dvd
    (Subgroup.card_dvd_of_le (dadeInter_le hb)) Nat.card_pos.ne'

theorem dadeInter_le_centralizer (hD : IsDadeData L A H) (hBA : B ⊆ A) (hb : b ∈ B) :
    dadeInter H B ≤ Subgroup.centralizer ({b} : Set G) :=
  (dadeInter_le hb).trans (hD.le_centralizer (hBA hb))

theorem dadeInter_insert_eq_inf_centralizer (hD : IsDadeData L A H) (ha : a ∈ A) (hBA : B ⊆ A)
    (hB : B.Nonempty) :
    dadeInter H (insert a B) = dadeInter H B ⊓ Subgroup.centralizer ({a} : Set G) := by
  rw [dadeInter_insert]
  refine le_antisymm (le_inf inf_le_right (inf_le_left.trans (hD.le_centralizer ha)))
    (le_inf ?_ inf_le_left)
  refine hD.le_H_of_isPiNumber_compl ha inf_le_right ?_
  exact (hD.isPiNumber_compl_card_dadeInter hBA hB).of_dvd
    (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne'

theorem dadeInter_inf_H (hD : IsDadeData L A H) (ha : a ∈ A) (hBA : B ⊆ A) (hB : B.Nonempty) :
    dadeInter H B ⊓ H a = dadeInter H B ⊓ Subgroup.centralizer ({a} : Set G) := by
  rw [inf_comm (a := dadeInter H B), ← dadeInter_insert]
  exact hD.dadeInter_insert_eq_inf_centralizer ha hBA hB

end IsDadeData

end CFSG.FeitThompson
