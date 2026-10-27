module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalTightEmbedding

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge

theorem two_group_centralizer_enlargement {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {P Q R : Subgroup S} [hPn : P.Normal] (hPQ : ¬ P ≤ Q) (hRn : (R.subgroupOf Q).Normal)
    (hRT : R ≤ P ⊓ Q) (hidx : R.relIndex (P ⊓ Q) = 2) (hT : 8 ≤ Nat.card ↥(P ⊓ Q)) :
    ∃ w ∈ P, w ∈ normalizer (Q : Set S) ∧ w ∉ Q ∧ w ^ 2 ∈ P ⊓ Q ∧
      ∃ z : S, orderOf z = 2 ∧ z ∈ R ⊓ conjugate R w ∧
        Q ⊔ zpowers w ≤ centralizer ({z} : Set S) ∧ Q < centralizer ({z} : Set S) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRQ : R ≤ Q := hRT.trans inf_le_right
  have hRconj : ∀ q ∈ Q, ∀ x ∈ R, q * x * q⁻¹ ∈ R := fun q hq x hx =>
    mem_subgroupOf.mp (hRn.conj_mem ⟨x, hRQ hx⟩ (mem_subgroupOf.mpr hx) ⟨q, hq⟩)
  set U := P ⊔ Q with hU
  set Q' := Q.subgroupOf U with hQ'
  have hQ'top : Q' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hPQ ?_
    rw [hQ', subgroupOf_eq_top] at h
    exact le_sup_left.trans h
  have : Group.IsNilpotent U := (hS.to_subgroup U).isNilpotent
  obtain ⟨n₀, hn₀N, hn₀Q⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hQ'top)
  have hex : ∃ j : ℕ, n₀ ^ (2 ^ j) ∈ Q' := by
    obtain ⟨k, hk⟩ := (hS.to_subgroup U) n₀
    exact ⟨k, hk ▸ one_mem _⟩
  have hj₀ : Nat.find hex ≠ 0 := by
    intro h
    have h1 := Nat.find_spec hex
    rw [h, pow_zero, pow_one] at h1
    exact hn₀Q h1
  have hnQ' : n₀ ^ (2 ^ (Nat.find hex - 1)) ∉ Q' := Nat.find_min hex (by omega)
  have hn2 : (n₀ ^ (2 ^ (Nat.find hex - 1))) ^ 2 ∈ Q' := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj₀)]
    exact Nat.find_spec hex
  have hnN : n₀ ^ (2 ^ (Nat.find hex - 1)) ∈ normalizer (Q' : Set U) := pow_mem hn₀N _
  obtain ⟨n, hn⟩ : ∃ n, n = n₀ ^ (2 ^ (Nat.find hex - 1)) := ⟨_, rfl⟩
  rw [← hn] at hnQ' hn2 hnN
  have hconjU : ∀ g ∈ normalizer (Q' : Set U), ∀ x ∈ Q, (g : S) * x * (g : S)⁻¹ ∈ Q :=
    fun g hg x hx => mem_subgroupOf.mp
      ((mem_normalizer_iff.mp hg ⟨x, le_sup_right (a := P) hx⟩).mp (mem_subgroupOf.mpr hx))
  have hnQ1 := hconjU n hnN
  have hnQ2 : ∀ x ∈ Q, (n : S)⁻¹ * x * (n : S) ∈ Q := fun x hx => by
    simpa using hconjU n⁻¹ (inv_mem hnN) x hx
  have hnPQ : (n : S) ∈ (P : Set S) * (Q : Set S) := by
    rw [← normal_mul P Q]
    exact n.2
  obtain ⟨w, hwP, q, hqQ, hwq⟩ := Set.mem_mul.mp hnPQ
  have hw : w = (n : S) * q⁻¹ := by rw [← hwq, mul_inv_cancel_right]
  have hwconj : ∀ x ∈ Q, w * x * w⁻¹ ∈ Q := by
    intro x hx
    have e : w * x * w⁻¹ = (n : S) * (q⁻¹ * x * q) * (n : S)⁻¹ := by
      rw [hw]
      group
    rw [e]
    exact hnQ1 _ (mul_mem (mul_mem (inv_mem hqQ) hx) hqQ)
  have hwN : w ∈ normalizer (Q : Set S) := mem_normalizer_of_conj_mem hwconj
  have hwQ : w ∉ Q := by
    intro hwQ
    apply hnQ'
    rw [mem_subgroupOf, ← hwq]
    exact mul_mem hwQ hqQ
  have hw2Q : w ^ 2 ∈ Q := by
    have e : w ^ 2 = (n : S) ^ 2 * ((n : S)⁻¹ * q⁻¹ * (n : S)) * q⁻¹ := by
      rw [hw, pow_two, pow_two]
      group
    rw [e]
    refine mul_mem (mul_mem ?_ (hnQ2 _ (inv_mem hqQ))) (inv_mem hqQ)
    simpa using mem_subgroupOf.mp hn2
  set T := P ⊓ Q with hTdef
  have hwT' : ∀ x ∈ T, w⁻¹ * x * w ∈ T := by
    intro x hx
    obtain ⟨hxP, hxQ⟩ := mem_inf.mp hx
    have h1 : w⁻¹ * x * w⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hwN) x).mp hxQ
    rw [inv_inv] at h1
    exact mem_inf.mpr ⟨by simpa using hPn.conj_mem x hxP w⁻¹, h1⟩
  have hRwT : conjugate R w ≤ T := by
    intro x hx
    have h2 := hwT' _ (hRT (mem_conjugate_iff.mp hx))
    have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    rwa [e] at h2
  have hRcard : Nat.card T = 2 * Nat.card R := by
    have h := relIndex_mul_card R T
    rw [hidx, inf_eq_left.mpr hRT] at h
    exact h.symm
  have hRwcard : Nat.card (conjugate R w) = Nat.card R :=
    card_map_of_injective (MulAut.conj w⁻¹).injective
  have hRwidx : (conjugate R w).relIndex T = 2 := by
    have h := relIndex_mul_card (conjugate R w) T
    rw [inf_eq_left.mpr hRwT, hRwcard, hRcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  set K := R ⊓ conjugate R w with hK
  have hKT : K ≤ T := inf_le_left.trans hRT
  have hKidx : K.relIndex T ≤ 4 := by
    have h := relIndex_inf_le (H := R) (K := conjugate R w) (L := T)
    rwa [hidx, hRwidx] at h
  have hKcard : 2 ≤ Nat.card K := by
    have h := relIndex_mul_card K T
    rw [inf_eq_left.mpr hKT] at h
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h8 : 8 ≤ K.relIndex T * Nat.card K := h ▸ hT
    by_contra hlt
    have h1 : Nat.card K = 1 := by omega
    rw [h1, mul_one] at h8
    omega
  have hQK : ∀ q ∈ Q, ∀ x ∈ K, q * x * q⁻¹ ∈ K := by
    intro q hq x hx
    obtain ⟨hxR, hxRw⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨hRconj q hq x hxR, mem_conjugate_iff.mpr ?_⟩
    have e : w * (q * x * q⁻¹) * w⁻¹ =
        (w * q * w⁻¹) * (w * x * w⁻¹) * (w * q * w⁻¹)⁻¹ := by group
    rw [e]
    exact hRconj _ (hwconj q hq) _ (mem_conjugate_iff.mp hxRw)
  have hwK : ∀ x ∈ K, w * x * w⁻¹ ∈ K := by
    intro x hx
    obtain ⟨hxR, hxRw⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨mem_conjugate_iff.mp hxRw, mem_conjugate_iff.mpr ?_⟩
    have e : w * (w * x * w⁻¹) * w⁻¹ = w ^ 2 * x * (w ^ 2)⁻¹ := by
      rw [pow_two]
      group
    rw [e]
    exact hRconj _ hw2Q x hxR
  set H := Q ⊔ zpowers w with hH
  have hKH : K ≤ H := (inf_le_left.trans hRQ).trans le_sup_left
  have hHN : H ≤ normalizer (K : Set S) :=
    sup_le (fun q hq => mem_normalizer_of_conj_mem (hQK q hq))
      (zpowers_le.mpr (mem_normalizer_of_conj_mem hwK))
  have hK'n : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  have : Group.IsNilpotent H := (hS.to_subgroup H).isNilpotent
  have hK'ne : K.subgroupOf H ≠ ⊥ := by
    intro h
    have h1 := congrArg (map H.subtype) h
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hKH, Subgroup.map_bot] at h1
    rw [h1, card_bot] at hKcard
    omega
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hK'ne
  have hX2 : 2 ∣ Nat.card ↥(K.subgroupOf H ⊓ center H) := by
    have hXp : IsPGroup 2 ↥(K.subgroupOf H ⊓ center H) :=
      (hS.to_subgroup H).to_subgroup _
    have hnt : Nontrivial ↥(K.subgroupOf H ⊓ center H) := (nontrivial_iff_ne_bot _).mpr hX
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hX2
  have hzK : ((x : H) : S) ∈ K := mem_subgroupOf.mp (mem_inf.mp x.2).1
  have hHC : H ≤ centralizer ({((x : H) : S)} : Set S) := fun h hh =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp x.2).2 ⟨h, hh⟩))
  refine ⟨w, hwP, hwN, hwQ, mem_inf.mpr ⟨pow_mem hwP 2, hw2Q⟩, (x : H), ?_, hzK, hHC, ?_⟩
  · rw [orderOf_coe, orderOf_coe, hx]
  · refine lt_of_le_of_ne (le_sup_left.trans hHC) fun h => hwQ ?_
    rw [h]
    exact hHC (mem_sup_right (mem_zpowers w))

end CFSG.ComponentClassification.SmallLocal
