module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem nonempty_mulEquiv_map_mk_of_isPGroup {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup G} (hP : IsPGroup p P) :
    Nonempty (↥P ≃* ↥(P.map (QuotientGroup.mk' N))) := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcop : (Nat.card P).Coprime (Nat.card N) :=
    hk ▸ Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN)
  have hinj : Function.Injective ((QuotientGroup.mk' N).subgroupMap P) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap, QuotientGroup.ker_mk',
      eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ P ⊓ N := ⟨x.2, Subgroup.mem_subgroupOf.1 hx⟩
    rw [Subgroup.inf_eq_bot_of_coprime hcop, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, (QuotientGroup.mk' N).subgroupMap_surjective P⟩⟩

theorem card_center_map_mk_of_isPGroup {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup G} (hP : IsPGroup p P) :
    Nat.card (center ↥(P.map (QuotientGroup.mk' N))) = Nat.card (center ↥P) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_map_mk_of_isPGroup hN hP
  exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm

theorem exists_isElemAbelian_card_sq_of_mem_of_orderOf {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hB : IsPGroup p B) (hBr : 2 ≤ CFSG.Open.pRank p B) {y : G} (hy : y ∈ B)
    (hyp : orderOf y = p) :
    ∃ E : Subgroup G, E ≤ B ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ y ∈ E := by
  obtain ⟨E, hyE, hEB, hE, hEc⟩ := exists_isElemAbelian_card_sq_of_le_of_card_prime hB hBr
    ((Subgroup.zpowers_le).2 hy) (by rw [Nat.card_zpowers, hyp])
  exact ⟨E, hEB, hE, hEc, hyE (Subgroup.mem_zpowers y)⟩

end CFSG.GroupTheory
