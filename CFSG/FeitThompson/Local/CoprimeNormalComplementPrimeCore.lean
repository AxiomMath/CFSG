module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {p : ℕ}

theorem isPGroup_zpowers_iff_exists_orderOf_eq_pow (hp : p.Prime) {x : G} :
    IsPGroup p (zpowers x) ↔ ∃ k, orderOf x = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h => ?_, fun ⟨k, hk⟩ => IsPGroup.of_card (by rw [Nat.card_zpowers, hk])⟩
  obtain ⟨k, hk⟩ := h.exists_orderOf_eq_pow ⟨x, mem_zpowers x⟩
  exact ⟨k, (Subgroup.orderOf_coe (⟨x, mem_zpowers x⟩ : zpowers x)).trans hk⟩

theorem exists_orderOf_eq_pow_of_mem_isPGroup (hp : p.Prime) {P : Subgroup G}
    (hP : IsPGroup p P) {x : G} (hx : x ∈ P) : ∃ k, orderOf x = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow ⟨x, hx⟩
  exact ⟨k, (Subgroup.orderOf_coe (⟨x, hx⟩ : P)).trans hk⟩

theorem factorization_eq_of_coprime_of_index_eq_pow [Finite G] (hp : p.Prime) {N : Subgroup G}
    (hcop : (Nat.card N).Coprime p) {n : ℕ} (hN : N.index = p ^ n) :
    (Nat.card G).factorization p = n := by
  have hnd : ¬ p ∣ Nat.card N := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h)
  have hG : Nat.card G = p ^ n * Nat.card N := by rw [← hN, Subgroup.index_mul_card]
  rw [hG, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') Nat.card_pos.ne']
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]

theorem natCard_eq_index_of_coprime [Finite G] (hp : p.Prime) {N : Subgroup G}
    (hcop : (Nat.card N).Coprime p) {n : ℕ} (hN : N.index = p ^ n) {S : Subgroup G}
    (hS : Nat.card S = p ^ (Nat.card G).factorization p) : Nat.card S = N.index := by
  rw [hS, factorization_eq_of_coprime_of_index_eq_pow hp hcop hN, hN]

theorem isComplement'_of_coprime [Finite G] (hp : p.Prime) {N : Subgroup G}
    (hcop : (Nat.card N).Coprime p) {n : ℕ} (hN : N.index = p ^ n) {S : Subgroup G}
    (hS : Nat.card S = p ^ (Nat.card G).factorization p) : N.IsComplement' S := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [natCard_eq_index_of_coprime hp hcop hN hS, mul_comm, Subgroup.index_mul_card]
  · exact Subgroup.disjoint_of_coprime_natCard
      (by rw [natCard_eq_index_of_coprime hp hcop hN hS, hN]; exact hcop.pow_right n)

theorem normal_inf_centralizer_of_sup_eq_top {N : Subgroup G} [N.Normal] {H : Subgroup G}
    (hNH : N ⊔ H = ⊤) : (H ⊓ centralizer (N : Set G)).Normal := by
  constructor
  intro t ht g
  have hg : g ∈ ((N : Set G) * (H : Set G)) := by
    rw [← Subgroup.normal_mul N H, hNH]; trivial
  obtain ⟨a, ha, s, hs, rfl⟩ := hg
  have hst : s * t * s⁻¹ ∈ H ⊓ centralizer (N : Set G) :=
    ⟨H.mul_mem (H.mul_mem hs ht.1) (H.inv_mem hs),
      (Subgroup.normal_centralizer (H := N)).conj_mem t ht.2 s⟩
  have hcomm : a * (s * t * s⁻¹) = s * t * s⁻¹ * a :=
    Subgroup.mem_centralizer_iff.1 hst.2 a ha
  have key : a * s * t * (a * s)⁻¹ = s * t * s⁻¹ := by
    calc a * s * t * (a * s)⁻¹ = a * (s * t * s⁻¹) * a⁻¹ := by group
      _ = s * t * s⁻¹ * a * a⁻¹ := by rw [hcomm]
      _ = s * t * s⁻¹ := by group
  rw [key]
  exact hst

theorem mem_pCore_of_mem_centralizer_of_orderOf_eq_pow [Finite G] (hp : p.Prime)
    {N : Subgroup G} [N.Normal] (hcop : (Nat.card N).Coprime p)
    (hquot : IsPGroup p (G ⧸ N)) {x : G} (hx : ∃ k, orderOf x = p ^ k)
    (hxC : x ∈ centralizer (N : Set G)) : x ∈ pCore p G := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := ((isPGroup_zpowers_iff_exists_orderOf_eq_pow hp).2 hx).exists_le_sylow
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hquot
  have hN : N.index = p ^ n := by rw [Subgroup.index_eq_card, hn]
  have hsup : N ⊔ (S : Subgroup G) = ⊤ :=
    (isComplement'_of_coprime hp hcop hN S.card_eq_multiplicity).sup_eq_top
  exact le_pCore hp (normal_inf_centralizer_of_sup_eq_top hsup)
    (S.isPGroup'.to_le inf_le_left) ⟨hS (mem_zpowers x), hxC⟩

theorem mem_pCore_of_mem_centralizer_of_isPGroup_zpowers [Finite G] (hp : p.Prime)
    {N : Subgroup G} [N.Normal] (hcop : (Nat.card N).Coprime p)
    (hquot : IsPGroup p (G ⧸ N)) {x : G} (hx : IsPGroup p (zpowers x))
    (hxC : x ∈ centralizer (N : Set G)) : x ∈ pCore p G :=
  mem_pCore_of_mem_centralizer_of_orderOf_eq_pow hp hcop hquot
    ((isPGroup_zpowers_iff_exists_orderOf_eq_pow hp).1 hx) hxC

theorem le_pCore_of_le_centralizer [Finite G] (hp : p.Prime) {N : Subgroup G} [N.Normal]
    (hcop : (Nat.card N).Coprime p) (hquot : IsPGroup p (G ⧸ N)) {P : Subgroup G}
    (hP : IsPGroup p P) (hPC : P ≤ centralizer (N : Set G)) : P ≤ pCore p G := fun _ hx =>
  mem_pCore_of_mem_centralizer_of_orderOf_eq_pow hp hcop hquot
    (exists_orderOf_eq_pow_of_mem_isPGroup hp hP hx) (hPC hx)

end

end CFSG.FeitThompson
