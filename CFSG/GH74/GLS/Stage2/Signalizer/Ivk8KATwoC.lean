module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Facts
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out
public import Certificates.Certificate2022

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out CFSG.GH74.GLS.Stage2.Signalizer.Odd87

local notation "Perm42" => Equiv.Perm (Fin 42)

section Abstract

theorem exists_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p ↥P) (hP1 : P ≠ ⊥) : ∃ y ∈ P, orderOf y = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card ↥P := by
    rcases hP.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq P h) hP1
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hcard
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem not_isPGroup_of_dvd {K : Type*} [Group K] [Finite K] {q r p : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hqr : q ≠ r) (hqd : q ∣ Nat.card K) (hrd : r ∣ Nat.card K) (hp : p.Prime) :
    ¬ IsPGroup p K := by
  intro hK
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hK
  rw [hn] at hqd hrd
  have h1 : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  have h2 : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrd)
  exact hqr (h1.trans h2.symm)

theorem simple_odd_normalizer {K : Type*} [Group K] [Finite K] (hK : IsSimpleGroup K)
    (hodd : ∃ c : K, c ≠ 1 ∧ Odd (orderOf c)) {p : ℕ} (hnot : ¬ IsPGroup p K)
    (X : Subgroup K) (hX : IsPGroup p ↥X)
    (hnorm : ∀ c : K, Odd (orderOf c) → c ∈ normalizer (X : Set K)) : X = ⊥ := by
  have htop : normalizer (X : Set K) = ⊤ := by
    have hle : Subgroup.normalClosure {c : K | Odd (orderOf c)} ≤ normalizer (X : Set K) := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      obtain ⟨c, rfl⟩ := isConj_iff.1 hax
      apply hnorm
      have : orderOf (c * a * c⁻¹) = orderOf a := MulEquiv.orderOf_eq (MulAut.conj c) a
      rw [this]
      exact ha
    rcases hK.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure {c : K | Odd (orderOf c)}) with h | h
    · exfalso
      obtain ⟨c, hc1, hco⟩ := hodd
      have : c ∈ Subgroup.normalClosure {c : K | Odd (orderOf c)} :=
        Subgroup.subset_normalClosure hco
      rw [h] at this
      exact hc1 (Subgroup.mem_bot.1 this)
    · rw [h] at hle
      exact top_le_iff.1 hle
  have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases hK.eq_bot_or_eq_top_of_normal X with h | h
  · exact h
  · exfalso
    apply hnot
    rw [h] at hX
    exact hX.of_equiv Subgroup.topEquiv

end Abstract

structure PCfg (r : Perm42) (p : ℕ) (P : Subgroup Perm42) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  le_R : P ≤ R
  pgroup : IsPGroup p ↥P
  ne_bot : P ≠ ⊥
  comm : ∀ e ∈ P, e * r = r * e
  norm : ∀ s ∈ S, r * s = s * r → Odd (orderOf s) → s ∈ normalizer (P : Set Perm42)

theorem eq_three_of_dvd_twelve {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 12) : p = 3 := by
  have h12 : p ∣ 2 ^ 2 * 3 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h12 with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1

theorem eq_three_of_dvd_seventytwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 72) :
    p = 3 := by
  have h72 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h72 with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1)

theorem inf_S_eq_bot_of_simple {r : Perm42} {C : Subgroup Perm42}
    (hCdef : ∀ d : Perm42, d ∈ C ↔ r * d = d * r ∧ d ∈ S) (hC : IsSimpleGroup ↥C)
    (hodd : ∃ c : ↥C, c ≠ 1 ∧ Odd (orderOf c)) (hnot : ∀ q : ℕ, q.Prime → ¬ IsPGroup q ↥C)
    {p : ℕ} {P : Subgroup Perm42} (h : PCfg r p P) : P ⊓ S = ⊥ := by
  let X : Subgroup ↥C := P.subgroupOf C
  have hXp : IsPGroup p ↥X := by
    intro g
    obtain ⟨k, hk⟩ := h.pgroup (⟨(g.1 : Perm42), g.2⟩ : ↥P)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥P => (z : Perm42)) hk
    simpa using this
  have hXn : X = ⊥ := by
    refine simple_odd_normalizer hC hodd (hnot p h.prime) X hXp fun c hc => ?_
    have hcd := (hCdef c.1).1 c.2
    have hoc : Odd (orderOf (c.1 : Perm42)) := by
      rw [Subgroup.orderOf_coe]
      exact hc
    have hn := h.norm c.1 hcd.2 hcd.1 hoc
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro x
    exact hn x.1
  rw [eq_bot_iff]
  intro x ⟨hxP, hxS⟩
  have hxC : x ∈ C := (hCdef x).2 ⟨(h.comm x hxP).symm, hxS⟩
  have : (⟨x, hxC⟩ : ↥C) ∈ X := hxP
  rw [hXn, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

section Model


theorem card_quot_SR : Nat.card (↥R ⧸ S.subgroupOf R) = 12 := by
  have h1 := (S.subgroupOf R).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card ↥(S.subgroupOf R) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_R).toEquiv
  have h3 : Nat.card ↥R = 241920 := card_R
  have h4 : Nat.card ↥S = 20160 := card_S
  rw [h2, h3, h4] at h1
  omega

theorem dvd_twelve_of_orderOf {y : Perm42} (hy : y ∈ R) (hyS : y ∉ S) {p : ℕ} (hp : p.Prime)
    (hord : orderOf y = p) : p ∣ 12 := by
  have : (S.subgroupOf R).Normal := S_normal
  let π : ↥R →* ↥R ⧸ S.subgroupOf R := QuotientGroup.mk' (S.subgroupOf R)
  let y' : ↥R := ⟨y, hy⟩
  have hy'ord : orderOf y' = p := by rw [← Subgroup.orderOf_coe y']; exact hord
  have hpow : (π y') ^ p = 1 := by rw [← map_pow, ← hy'ord, pow_orderOf_eq_one, map_one]
  have hne : π y' ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hyS h
  have hdvd : orderOf (π y') ∣ p := orderOf_dvd_of_pow_eq_one hpow
  have hord' : orderOf (π y') = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have := orderOf_dvd_natCard (π y')
  rwa [hord', card_quot_SR] at this

theorem inv_mod_S {r : Perm42} (hr : r ∈ R) (h4 : r * g₄ * r⁻¹ = g₄⁻¹) {y : Perm42} (hy : y ∈ R)
    (hy3 : y ^ 3 = 1) : r * y * r⁻¹ * y ∈ S := by
  have hyN := odd_mem_NN hy hy3
  obtain ⟨s, hs, h, hh, rfl⟩ := mem_NN_iff.mp hyN
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hconj : r * g₄ ^ k * r⁻¹ = (g₄ ^ k)⁻¹ := by
    rw [← conj_zpow, h4, inv_zpow]
  have e : r * (s * g₄ ^ k) * r⁻¹ * (s * g₄ ^ k) =
      (r * s * r⁻¹) * ((g₄ ^ k)⁻¹ * s * ((g₄ ^ k)⁻¹)⁻¹) := by
    rw [inv_inv]
    calc r * (s * g₄ ^ k) * r⁻¹ * (s * g₄ ^ k)
        = (r * s * r⁻¹) * (r * g₄ ^ k * r⁻¹) * s * g₄ ^ k := by group
      _ = (r * s * r⁻¹) * ((g₄ ^ k)⁻¹ * s * g₄ ^ k) := by rw [hconj]; group
  rw [e]
  have hgk : (g₄ ^ k)⁻¹ ∈ R := Subgroup.inv_mem _ (Subgroup.zpow_mem _ g₄_mem_R k)
  exact Subgroup.mul_mem _ (conj_mem_S hr hs) (conj_mem_S hgk hs)

theorem false_of_inverting {r : Perm42} (hr : r ∈ R) (h4 : r * g₄ * r⁻¹ = g₄⁻¹) {y : Perm42}
    (hy : y ∈ R) (hyS : y ∉ S) (hy3 : y ^ 3 = 1) (hcomm : y * r = r * y) : False := by
  have h := inv_mod_S hr h4 hy hy3
  have e : r * y * r⁻¹ * y = y * y := by
    have : r * y * r⁻¹ = y := by rw [← hcomm]; group
    rw [this]
  rw [e] at h
  apply hyS
  have : y = (y * y)⁻¹ := by
    have h3 : y * y * y = 1 := by rw [← pow_three']; exact hy3
    exact eq_inv_of_mul_eq_one_right h3
  rw [this]
  exact Subgroup.inv_mem _ h

theorem false_of_r₂ {p : ℕ} {P : Subgroup Perm42} (h : PCfg r₂ p P) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : ∃ c : ↥C₂, c ≠ 1 ∧ Odd (orderOf c) := by
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C₂) 3 (by rw [card_C₂]; norm_num)
    exact ⟨c, fun h1 => by rw [h1, orderOf_one] at hc; omega, by rw [hc]; exact ⟨1, rfl⟩⟩
  have hnot : ∀ q : ℕ, q.Prime → ¬ IsPGroup q ↥C₂ := fun q hq =>
    not_isPGroup_of_dvd Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [card_C₂]; norm_num) (by rw [card_C₂]; norm_num) hq
  have hP0 : P ⊓ S = ⊥ :=
    inf_S_eq_bot_of_simple (r := r₂) (C := C₂)
      (fun d => by simp [C₂, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, eq_comm])
      isSimpleGroup_C₂ hodd hnot h
  obtain ⟨y, hyP, hyo⟩ := exists_orderOf_eq_prime h.prime h.pgroup h.ne_bot
  have hyR := h.le_R hyP
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyo; exact h.prime.one_lt.ne hyo
  have hyS : y ∉ S := fun hS => by
    have hmem : y ∈ P ⊓ S := ⟨hyP, hS⟩
    rw [hP0] at hmem
    exact hy1 (Subgroup.mem_bot.1 hmem)
  have hp3 : p = 3 := eq_three_of_dvd_twelve h.prime h.odd
    (dvd_twelve_of_orderOf hyR hyS h.prime hyo)
  have hy3 : y ^ 3 = 1 := by rw [← hp3, ← hyo]; exact pow_orderOf_eq_one y
  exact false_of_inverting g₅_mem_R g₅_conj_g₄ hyR hyS hy3 (h.comm y hyP)

theorem false_of_r₃ {p : ℕ} {P : Subgroup Perm42} (h : PCfg r₃ p P) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : ∃ c : ↥C₃, c ≠ 1 ∧ Odd (orderOf c) := by
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C₃) 3 (by rw [card_C₃]; norm_num)
    exact ⟨c, fun h1 => by rw [h1, orderOf_one] at hc; omega, by rw [hc]; exact ⟨1, rfl⟩⟩
  have hnot : ∀ q : ℕ, q.Prime → ¬ IsPGroup q ↥C₃ := fun q hq =>
    not_isPGroup_of_dvd Nat.prime_three Nat.prime_five (by norm_num)
      (by rw [card_C₃]; norm_num) (by rw [card_C₃]; norm_num) hq
  have hP0 : P ⊓ S = ⊥ :=
    inf_S_eq_bot_of_simple (r := r₃) (C := C₃)
      (fun d => by simp [C₃, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, eq_comm])
      isSimpleGroup_C₃ hodd hnot h
  obtain ⟨y, hyP, hyo⟩ := exists_orderOf_eq_prime h.prime h.pgroup h.ne_bot
  have hyR := h.le_R hyP
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyo; exact h.prime.one_lt.ne hyo
  have hyS : y ∉ S := fun hS => by
    have hmem : y ∈ P ⊓ S := ⟨hyP, hS⟩
    rw [hP0] at hmem
    exact hy1 (Subgroup.mem_bot.1 hmem)
  have hp3 : p = 3 := eq_three_of_dvd_twelve h.prime h.odd
    (dvd_twelve_of_orderOf hyR hyS h.prime hyo)
  have hy3 : y ^ 3 = 1 := by rw [← hp3, ← hyo]; exact pow_orderOf_eq_one y
  exact false_of_inverting g₆_mem_R g₆_conj_g₄ hyR hyS hy3 (h.comm y hyP)

theorem cyclic_of_r₁ {p : ℕ} {P : Subgroup Perm42} (h : PCfg r₁ p P) : IsCyclic ↥P := by
  have hP0 : P ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxP, hxS⟩
    have hxC : x ∈ C₁ := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      (h.comm x hxP), hxS⟩
    have hd64 : orderOf x ∣ 64 := by
      have := orderOf_dvd_natCard (⟨x, hxC⟩ : ↥C₁)
      rwa [Subgroup.orderOf_mk, card_C₁] at this
    obtain ⟨k, hk⟩ := h.pgroup (⟨x, hxP⟩ : ↥P)
    have hdk : orderOf x ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (p ^ k) (2 ^ 6) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes h.prime Nat.prime_two).2 h.odd)
    have hd64' : orderOf x ∣ 2 ^ 6 := by norm_num; exact hd64
    have : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdk hcop) hd64'
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 this)
  obtain ⟨y, hyP, hyo⟩ := exists_orderOf_eq_prime h.prime h.pgroup h.ne_bot
  have hyR := h.le_R hyP
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyo; exact h.prime.one_lt.ne hyo
  have hyS : y ∉ S := fun hS => by
    have hmem : y ∈ P ⊓ S := ⟨hyP, hS⟩
    rw [hP0] at hmem
    exact hy1 (Subgroup.mem_bot.1 hmem)
  have hp3 : p = 3 := eq_three_of_dvd_twelve h.prime h.odd
    (dvd_twelve_of_orderOf hyR hyS h.prime hyo)
  have : (S.subgroupOf R).Normal := S_normal
  let f : ↥P →* ↥R ⧸ S.subgroupOf R :=
    (QuotientGroup.mk' (S.subgroupOf R)).comp (Subgroup.inclusion h.le_R)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (Subgroup.inclusion h.le_R x : ↥R) ∈ S.subgroupOf R :=
      (QuotientGroup.eq_one_iff _).1 hx
    have hxS : (x : Perm42) ∈ S := hx'
    have : (x : Perm42) ∈ P ⊓ S := ⟨x.2, hxS⟩
    rw [hP0, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hdvd : Nat.card ↥P ∣ 12 := by
    rw [← card_quot_SR]
    exact Subgroup.card_dvd_of_injective f hf
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h.pgroup
  have hn1 : n ≠ 0 := by
    rintro rfl
    exact h.ne_bot (Subgroup.eq_bot_of_card_eq P (by simpa using hn))
  rw [hn, hp3] at hdvd
  have hn2 : n = 1 := by
    by_contra hne
    have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have h12 := h9.trans hdvd
    exact absurd h12 (by norm_num)
  have hcard : Nat.card ↥P = 3 := by rw [hn, hp3, hn2]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_of_prime_card hcard

theorem prime_eq_three_of_r₄ {p : ℕ} {P : Subgroup Perm42} (h : PCfg r₄ p P) : p = 3 := by
  obtain ⟨y, hyP, hyo⟩ := exists_orderOf_eq_prime h.prime h.pgroup h.ne_bot
  have hyR := h.le_R hyP
  by_cases hyS : y ∈ S
  · have hyC : y ∈ C₄ := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      (h.comm y hyP), hyS⟩
    have hd : p ∣ 72 := by
      have := orderOf_dvd_natCard (⟨y, hyC⟩ : ↥C₄)
      rwa [Subgroup.orderOf_mk, hyo, card_C₄] at this
    exact eq_three_of_dvd_seventytwo h.prime h.odd hd
  · exact eq_three_of_dvd_twelve h.prime h.odd (dvd_twelve_of_orderOf hyR hyS h.prime hyo)

theorem comm_r₁ : ∀ x ∈ R, x * r₁ * x⁻¹ * r₁⁻¹ ∈ S := fun _ hx =>
  Subgroup.mul_mem _ (conj_mem_S hx r₁_mem_S) (Subgroup.inv_mem _ r₁_mem_S)

theorem comm_r₄ : ∀ x ∈ R, x * r₄ * x⁻¹ * r₄⁻¹ ∈ S := by
  have hr : r₄ ∈ R := r₄_mem_R
  have h4 : r₄ * g₄ * r₄⁻¹ = g₄ := by
    calc r₄ * g₄ * r₄⁻¹ = g₅ * (g₆ * g₄ * g₆⁻¹) * g₅⁻¹ := by
          show (g₅ * g₆) * g₄ * (g₅ * g₆)⁻¹ = _
          group
      _ = g₅ * g₄⁻¹ * g₅⁻¹ := by rw [g₆_conj_g₄]
      _ = (g₅ * g₄ * g₅⁻¹)⁻¹ := by group
      _ = g₄ := by rw [g₅_conj_g₄, inv_inv]
  intro x hx
  have hx' : x ∈ Subgroup.closure ({g₁, g₂, g₃, g₄, g₅, g₆} : Set Perm42) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hS3 : ∀ z ∈ S, z * r₄ * z⁻¹ * r₄⁻¹ ∈ S := fun z hz => by
      have e : z * r₄ * z⁻¹ * r₄⁻¹ = z * (r₄ * z⁻¹ * r₄⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hz (conj_mem_S hr (Subgroup.inv_mem _ hz))
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS3 _ g₁_mem_S
    · exact hS3 _ g₂_mem_S
    · exact hS3 _ g₃_mem_S
    · have : g₄ * r₄ * g₄⁻¹ * r₄⁻¹ = 1 := by
        have h' : g₄ * r₄ = r₄ * g₄ := by
          calc g₄ * r₄ = (r₄ * g₄ * r₄⁻¹) * r₄ := by rw [h4]
            _ = r₄ * g₄ := by group
        rw [h']; group
      rw [this]; exact Subgroup.one_mem _
    · have : g₅ * r₄ * g₅⁻¹ * r₄⁻¹ = 1 := by
        have h' : g₅ * r₄ = r₄ * g₅ := by
          simp only [r₄]
          calc g₅ * (g₅ * g₆) = g₅ * (g₆ * g₅) := by rw [g₅_comm_g₆]
            _ = (g₅ * g₆) * g₅ := by group
        rw [h']; group
      rw [this]; exact Subgroup.one_mem _
    · have : g₆ * r₄ * g₆⁻¹ * r₄⁻¹ = 1 := by
        have h' : g₆ * r₄ = r₄ * g₆ := by
          simp only [r₄]
          calc g₆ * (g₅ * g₆) = (g₆ * g₅) * g₆ := by group
            _ = (g₅ * g₆) * g₆ := by rw [← g₅_comm_g₆]
        rw [h']; group
      rw [this]; exact Subgroup.one_mem _
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxR : x ∈ R := hx
    have : x * y * r₄ * (x * y)⁻¹ * r₄⁻¹ =
        (x * (y * r₄ * y⁻¹ * r₄⁻¹) * x⁻¹) * (x * r₄ * x⁻¹ * r₄⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (conj_mem_S hxR ihy) ihx
  | inv x hx ihx =>
    have hxR : x ∈ R := hx
    have hxi : x⁻¹ ∈ R := Subgroup.inv_mem _ hxR
    have : x⁻¹ * r₄ * x⁻¹⁻¹ * r₄⁻¹ = x⁻¹ * (x * r₄ * x⁻¹ * r₄⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [this]
    exact conj_mem_S hxi (Subgroup.inv_mem _ ihx)

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
