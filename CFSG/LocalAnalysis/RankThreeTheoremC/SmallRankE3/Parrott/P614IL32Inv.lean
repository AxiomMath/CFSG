module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Parab
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Point
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IIndex

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC

theorem sq_eq_one_of_l₀ {V : Subgroup GL32} (hcard : Nat.card V = 4)
    (hl : L32Insp.l₀ ∈ normalizer (V : Set GL32)) : ∀ g ∈ V, g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a ∈ V, ∀ c ∈ V, a * c = c * a := by
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := V)
      (by rw [hcard]; norm_num)
    exact fun a ha c hc => congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  let W : Subgroup GL32 :=
    { carrier := {g | g ∈ V ∧ g ^ 2 = 1}
      one_mem' := ⟨one_mem V, one_pow 2⟩
      mul_mem' := fun {a c} ha hc => ⟨mul_mem ha.1 hc.1, by
        rw [(show Commute a c from hcomm a ha.1 c hc.1).mul_pow, ha.2, hc.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hWV : W ≤ V := fun g hg => hg.1
  by_contra hne
  push Not at hne
  obtain ⟨g₀, hg₀V, hg₀⟩ := hne
  have hWne : W ≠ V := fun he => hg₀ (he ▸ hg₀V : g₀ ∈ W).2
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hcard]; norm_num)
  have hwW : (w : GL32) ∈ W := ⟨w.2, by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    simpa using congrArg Subtype.val this⟩
  have hw1 : (w : GL32) ≠ 1 := fun h1 => by
    rw [show w = 1 from Subtype.ext h1, orderOf_one] at hw
    omega
  have hWd : Nat.card W ∣ 4 := hcard ▸ card_dvd_of_le hWV
  have hW4 : Nat.card W ≠ 4 := fun h4 => hWne (eq_of_le_of_card_ge hWV (by rw [h4, hcard]))
  have hW1 : Nat.card W ≠ 1 := fun h1 => hw1 (by
    rw [Subgroup.card_eq_one] at h1
    have : (w : GL32) ∈ (⊥ : Subgroup GL32) := h1 ▸ hwW
    simpa using this)
  have hW2 : Nat.card W = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hWd
    interval_cases h : Nat.card W <;> simp_all
  have hWw : W = zpowers (w : GL32) := by
    refine (eq_of_le_of_card_ge (zpowers_le.2 hwW) ?_).symm
    rw [hW2, Nat.card_zpowers, Subgroup.orderOf_coe, hw]
  have hlw : L32Insp.l₀ * w * L32Insp.l₀⁻¹ ∈ W := by
    refine ⟨(mem_normalizer_iff.1 hl w).1 w.2, ?_⟩
    rw [conj_pow, hwW.2]
    group
  rw [hWw] at hlw
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hlw
  have hw2 : (w : GL32) ^ 2 = 1 := hwW.2
  have hk' : L32Insp.l₀ * w * L32Insp.l₀⁻¹ = w := by
    have hwo : orderOf (w : GL32) = 2 := orderOf_eq_prime hw2 hw1
    have hpar : (w : GL32) ^ k = 1 ∨ (w : GL32) ^ k = w := by
      rw [← zpow_mod_orderOf, hwo]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h0
      · left
        rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h0, zpow_zero]
      · right
        rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h0, zpow_one]
    rcases hpar with h1 | h1
    · rw [h1] at hk
      exact absurd (conj_eq_one_iff.1 hk.symm) hw1
    · rw [← hk, h1]
  have hc : (w : GL32) * L32Insp.l₀ = L32Insp.l₀ * w := by
    calc (w : GL32) * L32Insp.l₀ = L32Insp.l₀ * w * L32Insp.l₀⁻¹ * L32Insp.l₀ := by rw [hk']
      _ = L32Insp.l₀ * w := by group
  exact hw1 (L32Insp.eq_one_of_commute_l₀ hc hw2)

theorem exists_inverting_of_four {V : Subgroup GL32} {l : GL32} (hl : orderOf l = 3)
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 4) (hlV : l ∈ normalizer (V : Set GL32)) :
    ∃ τ : GL32, τ ∈ normalizer (V : Set GL32) ∧ τ * l * τ⁻¹ = l⁻¹ := by
  have hl3 : l ^ 3 = 1 := by
    have := pow_orderOf_eq_one l
    rwa [hl] at this
  obtain ⟨g, hg⟩ := L32Insp.exists_conj_mem_zpowers hl3
  set V' : Subgroup GL32 := V.map (MulAut.conj g).toMonoidHom
  have hcard' : Nat.card V' = 4 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hcard]
  have hmemV' : ∀ v, v ∈ V' ↔ g⁻¹ * v * g ∈ V := by
    intro v
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [mul_assoc] using hu
    · intro hv
      exact ⟨g⁻¹ * v * g, hv, by simp [mul_assoc]⟩
  have hgl : g * l * g⁻¹ ∈ normalizer (V' : Set GL32) := by
    rw [mem_normalizer_iff]
    intro v
    rw [hmemV', hmemV']
    have e : g⁻¹ * (g * l * g⁻¹ * v * (g * l * g⁻¹)⁻¹) * g = l * (g⁻¹ * v * g) * l⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.1 hlV _
  have hord : orderOf (g * l * g⁻¹) = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective l).trans hl
  have hz : zpowers (g * l * g⁻¹) = zpowers L32Insp.l₀ := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hg)
    rw [Nat.card_zpowers, Nat.card_zpowers, L32Insp.orderOf_l₀, hord]
  have hl₀ : L32Insp.l₀ ∈ normalizer (V' : Set GL32) :=
    (zpowers_le.2 hgl) (hz ▸ mem_zpowers L32Insp.l₀)
  have hsq := sq_eq_one_of_l₀ hcard' hl₀
  obtain ⟨Q, hP⟩ := L32Insp.exists_pair hsq hcard' hl₀
  obtain ⟨P', hP'⟩ := L32Insp.exists_pair hP.sq hP.card hP.l₀_mem
  have hP'eq : P' = V' := by
    have h8 : ∀ g ∈ P', g ^ 8 = 1 := fun g hg => by
      rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hP'.sq g hg, one_pow]
    rcases hP.split P' h8 hP'.l₀_mem with hle | hle
    · exact eq_of_le_of_card_ge hle (by rw [hP'.card, hcard'])
    · have hPQ : P' = Q := eq_of_le_of_card_ge hle (by rw [hP'.card, hP.card])
      exact absurd (hPQ ▸ le_normalizer) hP'.not_le
  have htL : L32Insp.tL ∈ normalizer (V' : Set GL32) := hP'eq ▸ hP'.tL_mem
  refine ⟨g⁻¹ * L32Insp.tL * g, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro v
    have h1 := mem_normalizer_iff.1 htL (g * v * g⁻¹)
    rw [hmemV', hmemV'] at h1
    have e1 : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    have e2 : g⁻¹ * (L32Insp.tL * (g * v * g⁻¹) * L32Insp.tL⁻¹) * g =
        g⁻¹ * L32Insp.tL * g * v * (g⁻¹ * L32Insp.tL * g)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hg
    have hinv : L32Insp.tL * (g * l * g⁻¹) * L32Insp.tL⁻¹ = (g * l * g⁻¹)⁻¹ := by
      rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, L32Insp.tL_conj_l₀, inv_zpow]
    calc g⁻¹ * L32Insp.tL * g * l * (g⁻¹ * L32Insp.tL * g)⁻¹
        = g⁻¹ * (L32Insp.tL * (g * l * g⁻¹) * L32Insp.tL⁻¹) * g := by group
      _ = g⁻¹ * (g * l * g⁻¹)⁻¹ * g := by rw [hinv]
      _ = l⁻¹ := by group

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_of_coprime {Q : Subgroup G} {z q : G} (hz3 : z ^ 3 = 1)
    (hzQ : z ∈ normalizer (Q : Set G)) (hQ : ¬ 3 ∣ Nat.card Q) (hq : q ∈ Q)
    (hw : (q * z⁻¹) ^ 3 = 1) : ∃ p ∈ Q, q * (z⁻¹ * p * z) = p := by
  have hconj : ∀ p ∈ Q, z⁻¹ * p * z ∈ Q := fun p hp => by
    have := (mem_normalizer_iff.1 (inv_mem hzQ) p).1 hp
    simpa using this
  let φ : Q → Q := fun p => ⟨q * (z⁻¹ * p * z), Q.mul_mem hq (hconj p p.2)⟩
  have hz3' : z * z * z = 1 := by rw [← pow_three']; exact hz3
  have hw' : q * z⁻¹ * (q * z⁻¹) * (q * z⁻¹) = 1 := by rw [← pow_three']; exact hw
  have hφ : ∀ p, φ (φ (φ p)) = p := fun p => by
    apply Subtype.ext
    show q * (z⁻¹ * (q * (z⁻¹ * (q * (z⁻¹ * p * z)) * z)) * z) = p
    have e : q * (z⁻¹ * (q * (z⁻¹ * (q * (z⁻¹ * (p : G) * z)) * z)) * z) =
        (q * z⁻¹ * (q * z⁻¹) * (q * z⁻¹)) * p * (z * z * z) := by group
    rw [e, hw', hz3']
    group
  have hmod := card_modEq_three_of_iterate φ hφ
  have hne : Nonempty {p // φ p = p} := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : Nat.card {p // φ p = p} = 0 := Nat.card_of_isEmpty
    rw [h0] at hmod
    exact hQ (Nat.modEq_zero_iff_dvd.1 hmod)
  obtain ⟨⟨p, hp⟩⟩ := hne
  exact ⟨p, p.2, congrArg Subtype.val hp⟩

theorem conj_pow_odd_eq_inv {t z : G} (ht : t * z * t⁻¹ = z⁻¹) {m : ℕ} (hm : Odd m) :
    t ^ m * z * (t ^ m)⁻¹ = z⁻¹ := by
  have hc2 : Commute (t * t) z := by
    have e2 : (t * t) * z * (t * t)⁻¹ = z := by
      have e : (t * t) * z * (t * t)⁻¹ = t * (t * z * t⁻¹) * t⁻¹ := by group
      rw [e, ht, ← conj_inv, ht, inv_inv]
    show t * t * z = z * (t * t)
    calc t * t * z = (t * t) * z * (t * t)⁻¹ * (t * t) := by group
      _ = z * (t * t) := by rw [e2]
  obtain ⟨j, rfl⟩ := hm
  have hcj : Commute ((t * t) ^ j) z := hc2.pow_left j
  have e : t ^ (2 * j + 1) = (t * t) ^ j * t := by rw [pow_succ, pow_mul, sq]
  rw [e]
  calc (t * t) ^ j * t * z * ((t * t) ^ j * t)⁻¹ =
        (t * t) ^ j * (t * z * t⁻¹) * ((t * t) ^ j)⁻¹ := by group
    _ = (t * t) ^ j * z⁻¹ * ((t * t) ^ j)⁻¹ := by rw [ht]
    _ = z⁻¹ := by rw [(hcj.inv_right).eq]; group

variable {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

theorem L32Data.exists_t (h : L32Data M B H S K z b f) :
    ∃ t : G, t ∈ K ⊔ pCoreOf 2 H ∧ t ∈ normalizer (S : Set G) ∧ t * z * t⁻¹ = z⁻¹ ∧
      t * b = b * t ∧ ∃ n : ℕ, t ^ 2 ^ n = 1 := by
  set O := pCoreOf 2 H
  have hz3 : z ^ 3 = 1 := by rw [← h.z_order]; exact pow_orderOf_eq_one z
  have hb3 : b ^ 3 = 1 := h.B_exp b h.b_mem
  have hzb : z * b = b * z := h.B_comm z h.z_mem_B b h.b_mem
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h.isPGroup_core
    rw [hn]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hzO : z ∈ normalizer (O : Set G) := h.H_le (h.K_le h.z_mem_K)
  have hbO : b ∈ normalizer (O : Set G) := h.H_le (h.B_le h.b_mem)
  obtain ⟨τ, hτV, hτl⟩ :=
    exists_inverting_of_four h.orderOf_l h.isPGroup_V h.card_V h.l_mem_normalizer
  obtain ⟨k₀, hk₀⟩ := h.f_surj τ
  have hk₀S : (k₀ : G) ∈ normalizer (S : Set G) := h.mem_normalizer_of (hk₀ ▸ hτV)
  have hk₀z : (k₀ : G) * z * (k₀ : G)⁻¹ * z ∈ O := by
    have h1 : f (k₀ * ⟨z, h.z_mem_K⟩ * k₀⁻¹ * ⟨z, h.z_mem_K⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hk₀, hτl, inv_mul_cancel]
    exact (h.f_ker _).1 h1
  have hc : b * k₀ * b⁻¹ * (k₀ : G)⁻¹ ∈ O :=
    h.b_cent (commutator_mem_commutator (mem_zpowers b) k₀.2)
  obtain ⟨o, ho, hob⟩ := exists_mul_mem_centralizer_of_coprime hb3 hbO
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hO3) hc
  set t₁ := o * (k₀ : G)
  have ht₁X : t₁ ∈ K ⊔ O := mul_mem (mem_sup_right ho) (mem_sup_left k₀.2)
  have ht₁S : t₁ ∈ normalizer (S : Set G) := mul_mem (le_normalizer (h.core_le ho)) hk₀S
  set q := t₁ * z * t₁⁻¹ * z
  have hqO : q ∈ O := by
    have e : q = o * ((k₀ : G) * z * (k₀ : G)⁻¹ * z) * (z⁻¹ * o⁻¹ * z) := by
      simp only [q, t₁]
      group
    rw [e]
    refine O.mul_mem (O.mul_mem ho hk₀z) ?_
    have := (mem_normalizer_iff.1 (inv_mem hzO) o⁻¹).1 (O.inv_mem ho)
    simpa using this
  have hqb : q ∈ centralizer ({b} : Set G) := by
    have hzc : z ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.2 hzb
    exact mul_mem (mul_mem (mul_mem hob hzc) (inv_mem hob)) hzc
  set Q := O ⊓ centralizer ({b} : Set G)
  have hzQ : z ∈ normalizer (Q : Set G) := by
    have hzc : z ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.2 hzb
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hzO, le_normalizer hzc⟩
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun hd => hO3 (hd.trans (card_dvd_of_le inf_le_left))
  have hw : (q * z⁻¹) ^ 3 = 1 := by
    have e : q * z⁻¹ = t₁ * z * t₁⁻¹ := by simp only [q]; group
    rw [e, conj_pow, hz3]
    group
  obtain ⟨p, hpQ, hp⟩ := exists_fixed_of_coprime hz3 hzQ hQ3 ⟨hqO, hqb⟩ hw
  set t₂ := p⁻¹ * t₁
  have ht₂z : t₂ * z * t₂⁻¹ = z⁻¹ := by
    have e1 : t₁ * z * t₁⁻¹ = q * z⁻¹ := by simp only [q]; group
    have e2 : q * z⁻¹ * p = p * z⁻¹ := by
      calc q * z⁻¹ * p = q * (z⁻¹ * p * z) * z⁻¹ := by group
        _ = p * z⁻¹ := by rw [hp]
    calc t₂ * z * t₂⁻¹ = p⁻¹ * (t₁ * z * t₁⁻¹) * p := by simp only [t₂]; group
      _ = p⁻¹ * (q * z⁻¹ * p) := by rw [e1]; group
      _ = z⁻¹ := by rw [e2]; group
  have ht₂X : t₂ ∈ K ⊔ O := mul_mem (mem_sup_right (O.inv_mem hpQ.1)) ht₁X
  have ht₂S : t₂ ∈ normalizer (S : Set G) :=
    mul_mem (le_normalizer (h.core_le (O.inv_mem hpQ.1))) ht₁S
  have ht₂b : t₂ ∈ centralizer ({b} : Set G) := mul_mem (inv_mem hpQ.2) hob
  have hn0 : orderOf t₂ ≠ 0 := (orderOf_pos t₂).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  refine ⟨t₂ ^ m, pow_mem ht₂X m, pow_mem ht₂S m, conj_pow_odd_eq_inv ht₂z hm,
    mem_centralizer_singleton_iff.1 (pow_mem ht₂b m), a, ?_⟩
  rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]

theorem L32Data.sylow_of_t (h : L32Data M B H S K z b f) {t : G}
    (htX : t ∈ K ⊔ pCoreOf 2 H) (htS : t ∈ normalizer (S : Set G)) (htz : t * z * t⁻¹ = z⁻¹)
    {n : ℕ} (htn : t ^ 2 ^ n = 1) :
    S ≤ zpowers t ⊔ S ∧ zpowers t ⊔ S ≤ K ⊔ pCoreOf 2 H ∧ IsPGroup 2 ↥(zpowers t ⊔ S) ∧
      ¬ 2 ∣ ((zpowers t ⊔ S).subgroupOf (K ⊔ pCoreOf 2 H)).index := by
  set R := zpowers t ⊔ S
  have ht2 : IsPGroup 2 (zpowers t) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htn, one_zpow]
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_right' ht2 h.isPGroup_S (zpowers_le.2 htS)
  have hSR : S ≤ R := le_sup_right
  have hRX : R ≤ K ⊔ pCoreOf 2 H := sup_le (zpowers_le.2 htX) h.S_le
  have htnS : t ∉ S := by
    intro htS'
    have h1 : t * z * t⁻¹ * z⁻¹ ∈ S := by
      have e : t * z * t⁻¹ * z⁻¹ = t * (z * t⁻¹ * z⁻¹) := by group
      rw [e]
      exact S.mul_mem htS' ((mem_normalizer_iff.1 (h.B_le_normalizer_S h.z_mem_B) _).1
        (S.inv_mem htS'))
    rw [htz] at h1
    have hz3 : z ^ 3 = 1 := by rw [← h.z_order]; exact pow_orderOf_eq_one z
    have hzS : z ∈ S := by
      have e : z = (z⁻¹ * z⁻¹)⁻¹ * (z⁻¹ * z⁻¹)⁻¹ * (z ^ 3)⁻¹ := by group
      rw [e, hz3, inv_one, mul_one]
      exact S.mul_mem (S.inv_mem h1) (S.inv_mem h1)
    have hzO : z ∉ S := by
      intro hz
      obtain ⟨k, hk⟩ := h.isPGroup_S ⟨z, hz⟩
      have h2 : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h3 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
      rw [h.z_order] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    exact hzO hzS
  refine ⟨hSR, hRX, hR2, ?_⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hR2
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 h.isPGroup_core
  have hS : Nat.card S = 2 ^ (c + 2) := by rw [h.card_S, hc]; ring
  have hlt : Nat.card S < Nat.card R :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hSR fun he => htnS (he ▸ mem_sup_left (mem_zpowers t)))
  have hdvd : Nat.card S ∣ Nat.card R := card_dvd_of_le hSR
  rw [hS, hr] at hdvd hlt
  have hr1 : c + 2 ≤ r := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hr2 : c + 2 ≠ r := fun he => by rw [he] at hlt; omega
  have hRXd : Nat.card R ∣ Nat.card (K ⊔ pCoreOf 2 H : Subgroup G) := card_dvd_of_le hRX
  rw [h.card_X, hc, hr, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, ← mul_assoc, ← pow_add] at hRXd
  have hr3 : r ≤ c + 3 := by
    have hcop : Nat.Coprime (2 ^ r) 21 := Nat.Coprime.pow_left r (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hRXd)
  have hreq : r = c + 3 := by omega
  have hidx : R.relIndex (K ⊔ pCoreOf 2 H) = 21 := by
    have := relIndex_mul_card R (K ⊔ pCoreOf 2 H)
    rw [inf_eq_left.2 hRX, h.card_X, hc, hr, hreq] at this
    have hpos : 0 < 2 ^ (c + 3) := by positivity
    have : R.relIndex (K ⊔ pCoreOf 2 H) * 2 ^ (c + 3) = 21 * 2 ^ (c + 3) := by
      rw [this]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  change ¬ 2 ∣ R.relIndex (K ⊔ pCoreOf 2 H)
  rw [hidx]
  decide

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
