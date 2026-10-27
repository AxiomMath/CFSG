module

public import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
public import CFSG.FeitThompson.Representations.CanonicalPiSetComponent
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
public import CFSG.FeitThompson.Definitions.DadeCosetPacket

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {G : Type*} [Group G]

theorem coprimeComponent_isPiNumber {π : Set ℕ} {n : ℕ} (hn : n ≠ 0) (h : IsPiNumber π n) :
    CoprimeComponent.IsPiNumber π n :=
  CoprimeComponent.isPiNumber_iff_forall_prime.2
    ⟨Nat.pos_of_ne_zero hn, fun p hp hpn => (isPiNumber_iff_of_ne_zero hn).1 h p hp hpn⟩

theorem self_mem_centralizer (a : G) : a ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a b : G}

theorem isPiNumber_orderOf (hD : IsDadeData L A H) (ha : a ∈ A) :
    CoprimeComponent.IsPiNumber (dadePrimes L A) (orderOf a) := by
  refine coprimeComponent_isPiNumber (orderOf_pos a).ne' ?_
  refine (isPiNumber_card_inf_centralizer (L := L) ha).of_dvd ?_ Nat.card_pos.ne'
  exact Subgroup.orderOf_dvd_natCard _ ⟨hD.mem_of_mem ha, self_mem_centralizer a⟩

theorem isPiPrimeNumber_orderOf_mem_H (hD : IsDadeData L A H) (ha : a ∈ A) {u : G}
    (hu : u ∈ H a) : CoprimeComponent.IsPiPrimeNumber (dadePrimes L A) (orderOf u) :=
  CoprimeComponent.isPiPrimeNumber_iff.2
    (coprimeComponent_isPiNumber (orderOf_pos u).ne'
      ((hD.isPiNumber_compl_card_H ha).of_dvd (Subgroup.orderOf_dvd_natCard _ hu)
        Nat.card_pos.ne'))

@[simp]
theorem piComponent_self (hD : IsDadeData L A H) (ha : a ∈ A) :
    CoprimeComponent.piComponent (dadePrimes L A) a = a :=
  CoprimeComponent.piComponent_eq_self_of_isPiNumber (hD.isPiNumber_orderOf ha)

theorem piComponent_of_mem_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) {x : G}
    (hx : x ∈ dadeCoset H a) :
    CoprimeComponent.piComponent (dadePrimes L A) x = a := by
  rw [hD.dadeCoset_eq_smul ha, Set.mem_smul_set] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [smul_eq_mul]
  exact CoprimeComponent.piComponent_eq_of_commute ((hD.le_centralizer ha hu) a rfl)
    (hD.isPiNumber_orderOf ha) (hD.isPiPrimeNumber_orderOf_mem_H ha hu)

theorem isConj_piComponent_of_mem_dadeSupport (hD : IsDadeData L A H) (ha : a ∈ A) {x : G}
    (hx : x ∈ dadeSupport H a) :
    IsConj a (CoprimeComponent.piComponent (dadePrimes L A) x) := by
  obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 hx
  obtain ⟨c, hcx⟩ := _root_.isConj_iff.1 hc
  refine _root_.isConj_iff.2 ⟨c, ?_⟩
  rw [← hcx, CoprimeComponent.piComponent_conj, hD.piComponent_of_mem_dadeCoset ha hy]

theorem dadeCoset_conj (hD : IsDadeData L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    dadeCoset H (l * a * l⁻¹) = (fun x => l * x * l⁻¹) '' dadeCoset H a := by
  ext x
  simp only [Set.mem_image, mem_dadeCoset_iff, hD.conj_smul_H ha hl, mem_conj_smul_iff]
  constructor
  · intro h
    refine ⟨l⁻¹ * x * l, ?_, by group⟩
    have e : l⁻¹ * (x * (l * a * l⁻¹)⁻¹) * l = l⁻¹ * x * l * a⁻¹ := by group
    rwa [e] at h
  · rintro ⟨y, hy, rfl⟩
    have e : l⁻¹ * (l * y * l⁻¹ * (l * a * l⁻¹)⁻¹) * l = y * a⁻¹ := by group
    rwa [e]

theorem dadeSupport_conj (hD : IsDadeData L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    dadeSupport H (l * a * l⁻¹) = dadeSupport H a := by
  ext x
  simp only [mem_dadeSupport_iff, hD.dadeCoset_conj ha hl, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hc⟩
    exact ⟨z, hz, (_root_.isConj_iff.2 ⟨l, rfl⟩).trans hc⟩
  · rintro ⟨y, hy, hc⟩
    exact ⟨l * y * l⁻¹, ⟨y, hy, rfl⟩, (_root_.isConj_iff.2 ⟨l⁻¹, by group⟩).trans hc⟩

theorem exists_conj_of_dadeSupport_inter_nonempty (hD : IsDadeData L A H) (ha : a ∈ A)
    (hb : b ∈ A) (h : (dadeSupport H a ∩ dadeSupport H b).Nonempty) :
    ∃ l ∈ L, l * a * l⁻¹ = b := by
  obtain ⟨x, hxa, hxb⟩ := h
  exact hD.fusion ha hb ((hD.isConj_piComponent_of_mem_dadeSupport ha hxa).trans
    (hD.isConj_piComponent_of_mem_dadeSupport hb hxb).symm)

theorem dadeSupport_eq_iff_exists_conj (hD : IsDadeData L A H) (ha : a ∈ A) (hb : b ∈ A) :
    dadeSupport H a = dadeSupport H b ↔ ∃ l ∈ L, l * a * l⁻¹ = b := by
  refine ⟨fun h => hD.exists_conj_of_dadeSupport_inter_nonempty ha hb
      ⟨a, self_mem_dadeSupport H a, h ▸ self_mem_dadeSupport H a⟩, ?_⟩
  rintro ⟨l, hl, rfl⟩
  exact (hD.dadeSupport_conj ha hl).symm

theorem dadeSupport_disjoint_of_forall (hD : IsDadeData L A H) (ha : a ∈ A) (hb : b ∈ A)
    (h : ∀ l ∈ L, l * a * l⁻¹ ≠ b) : Disjoint (dadeSupport H a) (dadeSupport H b) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  refine Set.not_nonempty_iff_eq_empty.1 fun hne => ?_
  obtain ⟨l, hl, hlab⟩ := hD.exists_conj_of_dadeSupport_inter_nonempty ha hb hne
  exact h l hl hlab

theorem dadeSupport_eq_or_disjoint (hD : IsDadeData L A H) (ha : a ∈ A) (hb : b ∈ A) :
    dadeSupport H a = dadeSupport H b ∨ Disjoint (dadeSupport H a) (dadeSupport H b) := by
  by_cases h : ∃ l ∈ L, l * a * l⁻¹ = b
  · exact Or.inl ((hD.dadeSupport_eq_iff_exists_conj ha hb).2 h)
  · push Not at h
    exact Or.inr (hD.dadeSupport_disjoint_of_forall ha hb h)

end IsDadeData

end

end CFSG.FeitThompson
