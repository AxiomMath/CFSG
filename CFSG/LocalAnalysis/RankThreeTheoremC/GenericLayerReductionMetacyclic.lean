module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedEscapeAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Finset

theorem exists_sum_pow_succ_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ} (hr : r % p = 1) :
    ∃ u : ℕ, (∑ i ∈ Finset.range p, r ^ (i + 1)) = p * u ∧ ¬ p ∣ u := by
  have hp0 : 0 < p := hp.pos
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · obtain ⟨m, hm⟩ := h; exact ⟨m, hm⟩
  obtain ⟨t, hrt⟩ : ∃ t, r = 1 + p * t := ⟨r / p, by have := Nat.mod_add_div r p; omega⟩
  have hp2' : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    have h2 := ZMod.natCast_self (p ^ 2)
    push_cast at h2
    exact h2
  have hx : ((p : ZMod (p ^ 2)) * t) ^ 2 = 0 := by
    calc ((p : ZMod (p ^ 2)) * t) ^ 2 = (p : ZMod (p ^ 2)) ^ 2 * t ^ 2 := by ring
      _ = 0 := by rw [hp2', zero_mul]
  have hr' : (r : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) * t := by rw [hrt]; push_cast; ring
  have hpow : ∀ i : ℕ, ((r : ZMod (p ^ 2)) ^ i) = 1 + i * ((p : ZMod (p ^ 2)) * t) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e1 : (r : ZMod (p ^ 2)) ^ (i + 1) = (r : ZMod (p ^ 2)) ^ i * r := by ring
      rw [e1, ih, hr']
      push_cast
      linear_combination (i : ZMod (p ^ 2)) * hx
  have hsum : ∑ i ∈ Finset.range p, (i + 1) = (m + 1) * p := by
    have h1 := Finset.sum_range_id_mul_two (p + 1)
    rw [Finset.sum_range_succ] at h1
    have h2 : ∑ i ∈ Finset.range p, (i + 1) = ∑ i ∈ Finset.range p, i + p := by
      rw [Finset.sum_add_distrib]; simp
    rw [h2]
    subst hm
    simp only [Nat.add_sub_cancel] at h1
    nlinarith
  have key : ((∑ i ∈ Finset.range p, r ^ (i + 1) : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by
    push_cast
    simp_rw [hpow]
    push_cast
    have hs : (∑ i ∈ Finset.range p, ((i : ZMod (p ^ 2)) + 1)) =
        (((m + 1) * p : ℕ) : ZMod (p ^ 2)) := by
      rw [← hsum]; push_cast; rfl
    calc ∑ i ∈ Finset.range p, (1 + ((i : ZMod (p ^ 2)) + 1) * ((p : ZMod (p ^ 2)) * t))
        = (p : ZMod (p ^ 2)) + (∑ i ∈ Finset.range p, ((i : ZMod (p ^ 2)) + 1)) *
            ((p : ZMod (p ^ 2)) * t) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]; simp
      _ = (p : ZMod (p ^ 2)) := by
          rw [hs]
          push_cast
          have e2 : ((m : ZMod (p ^ 2)) + 1) * p * (p * t) =
              (m + 1) * t * (p : ZMod (p ^ 2)) ^ 2 := by
            ring
          rw [e2, hp2']; ring
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp key
  have hpp : p < p ^ 2 := by nlinarith [hp.two_le]
  have hmod' : (∑ i ∈ Finset.range p, r ^ (i + 1)) % p ^ 2 = p := by
    rw [hmod]; exact Nat.mod_eq_of_lt hpp
  set S := ∑ i ∈ Finset.range p, r ^ (i + 1) with hS
  refine ⟨1 + p * (S / p ^ 2), ?_, ?_⟩
  · have := Nat.mod_add_div S (p ^ 2)
    rw [hmod'] at this
    nlinarith [this]
  · intro hdvd
    have : p ∣ 1 := by
      have h2 : p ∣ p * (S / p ^ 2) := dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem pow_eq_one_of_mul_pow_eq_one {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal] (hN : IsCyclic N) (hNp : IsPGroup p N)
    {e n : A} (hn : n ∈ N) (he : e ^ p = 1) (hen : (e * n) ^ p = 1) : n ^ p = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hN.exists_generator
  set a : A := (g : A) with ha
  have haN : a ∈ N := g.2
  have hNa : ∀ y ∈ N, ∃ k : ℕ, a ^ k = y := by
    intro y hy
    have h1 : (⟨y, hy⟩ : N) ∈ Subgroup.zpowers g := hg ⟨y, hy⟩
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr h1
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨t, ht⟩ : ∃ t, orderOf a = p ^ t := by
    obtain ⟨t, ht⟩ := (IsPGroup.iff_orderOf.mp hNp) g
    exact ⟨t, by rw [← ht, ha, Subgroup.orderOf_coe]⟩
  obtain ⟨r, hr0⟩ := hNa _ (‹N.Normal›.conj_mem a haN e)
  have hr : e * a * e⁻¹ = a ^ r := hr0.symm
  have hconj : ∀ i : ℕ, e ^ i * a * (e ^ i)⁻¹ = a ^ (r ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc e ^ (i + 1) * a * (e ^ (i + 1))⁻¹ = e * (e ^ i * a * (e ^ i)⁻¹) * e⁻¹ := by group
        _ = e * a ^ (r ^ i) * e⁻¹ := by rw [ih]
        _ = (e * a * e⁻¹) ^ (r ^ i) := (conj_pow).symm
        _ = a ^ (r ^ (i + 1)) := by rw [hr, ← pow_mul, pow_succ, mul_comm]
  have hconj' : ∀ i j : ℕ, e ^ i * a ^ j = a ^ (r ^ i * j) * e ^ i := by
    intro i j
    have : e ^ i * a ^ j * (e ^ i)⁻¹ = a ^ (r ^ i * j) := by
      rw [← conj_pow, hconj i, ← pow_mul]
    calc e ^ i * a ^ j = (e ^ i * a ^ j * (e ^ i)⁻¹) * e ^ i := by group
      _ = a ^ (r ^ i * j) * e ^ i := by rw [this]
  have hform : ∀ j k : ℕ, (e * a ^ j) ^ k =
      a ^ (j * ∑ i ∈ Finset.range k, r ^ (i + 1)) * e ^ k := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (e * a ^ j) ^ (k + 1) = (e * a ^ j) ^ k * (e * a ^ j) := pow_succ _ _
        _ = a ^ (j * ∑ i ∈ Finset.range k, r ^ (i + 1)) * (e ^ k * e * a ^ j) := by
          rw [ih]; group
        _ = a ^ (j * ∑ i ∈ Finset.range k, r ^ (i + 1)) * (e ^ (k + 1) * a ^ j) := by
          rw [← pow_succ]
        _ = a ^ (j * ∑ i ∈ Finset.range k, r ^ (i + 1)) *
            (a ^ (r ^ (k + 1) * j) * e ^ (k + 1)) := by
          rw [hconj']
        _ = a ^ (j * ∑ i ∈ Finset.range (k + 1), r ^ (i + 1)) * e ^ (k + 1) := by
          rw [← mul_assoc, ← pow_add, Finset.sum_range_succ]
          congr 2
          ring
  obtain ⟨j, rfl⟩ := hNa n hn
  rw [hform, he, mul_one] at hen
  by_cases ht0 : t = 0
  · rw [ht0, pow_zero, orderOf_eq_one_iff] at ht
    rw [ht]; simp
  have hpt : 0 < t := Nat.pos_of_ne_zero ht0
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    have : 1 < p ^ t := Nat.one_lt_pow ht0 hp.one_lt
    omega
  have h1 : a ^ (r ^ p) = a ^ 1 := by
    have := hconj p
    rw [he] at this
    simpa using this.symm
  have hmod : r ^ p ≡ 1 [MOD p ^ t] := by
    rw [← ht]; exact pow_eq_pow_iff_modEq.mp h1
  have hmodp : r ^ p ≡ 1 [MOD p] := hmod.of_dvd (dvd_pow_self p ht0)
  have hr1 : r % p = 1 := by
    have h2 : ((r : ZMod p)) ^ p = (r : ZMod p) := ZMod.pow_card _
    have h3 : ((r ^ p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodp
    push_cast at h3
    rw [h3] at h2
    have h4 : ((r : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact h2.symm
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h4
    rwa [Nat.mod_eq_of_lt hp.one_lt] at this
  obtain ⟨u, hSu, hu⟩ := exists_sum_pow_succ_eq hp hp2 hr1
  rw [hSu] at hen
  have hdvd : p ^ t ∣ j * (p * u) := by rw [← ht]; exact orderOf_dvd_of_pow_eq_one hen
  have hdvd2 : p ^ (t - 1) ∣ j * u := by
    have e1 : p ^ t = p * p ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e1] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos (by
      have : j * (p * u) = p * (j * u) := by ring
      rwa [this] at hdvd)
  have hcop : Nat.Coprime (p ^ (t - 1)) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
  obtain ⟨c, hc⟩ := hcop.dvd_of_dvd_mul_right hdvd2
  have hjp : j * p = p ^ t * c := by
    have e1 : p ^ t = p ^ (t - 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [hc, e1]; ring
  rw [← pow_mul, hjp, pow_mul, ← ht, pow_orderOf_eq_one, one_pow]

theorem mem_of_pow_eq_one_of_card_eq {B : Type*} [Group B] [Finite B] [IsCyclic B] {p : ℕ}
    (hp : 0 < p) (U : Subgroup B) (hU : Nat.card U = p) {b : B} (hb : b ^ p = 1) : b ∈ U := by
  classical
  have : Fintype B := Fintype.ofFinite B
  have hle := IsCyclic.card_pow_eq_one_le (α := B) hp
  set s : Finset B := Finset.univ.filter (fun a => a ^ p = 1) with hs
  set t : Finset B := Finset.univ.filter (fun a => a ∈ U) with ht
  have hts : t ⊆ s := by
    intro a ha
    simp only [ht, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    have := pow_card_eq_one' (G := U) (x := ⟨a, ha⟩)
    rw [hU] at this
    exact congrArg Subtype.val this
  have hcard : t.card = p := by
    rw [← hU, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
  have heq : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
  have : b ∈ s := by simp [hs, hb]
  rw [← heq] at this
  simpa [ht] using this

theorem mem_of_pow_eq_one_of_isCyclic_quotient {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsPGroup p A) (N : Subgroup A) [N.Normal]
    (hN : IsCyclic N) (hq : IsCyclic (A ⧸ N)) (E : Subgroup A) (hE : ∀ x ∈ E, x ^ p = 1)
    (hEc : p ^ 2 ≤ Nat.card E) {x : A} (hx : x ^ p = 1) : x ∈ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  let φ : E →* A ⧸ N := q.comp E.subtype
  have hNp : IsPGroup p N := hA.to_subgroup N
  have hmem : ∀ e : φ.ker, ((e : E) : A) ∈ N := by
    intro e
    exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp e.2)
  have hker : Nat.card φ.ker ≤ p := by
    let f : φ.ker →* N := ((E.subtype.comp φ.ker.subtype).codRestrict N hmem)
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (((f a : N) : A)) = (((f b : N) : A)) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have : IsCyclic φ.ker := isCyclic_of_injective f hf
    exact CFSG.AGLEmbedding.card_le_of_isCyclic_of_forall_pow_eq_one hp0 fun a =>
      Subtype.ext (Subtype.ext (hE _ a.1.2))
  have hrange : Nat.card φ.range ≤ p := by
    refine CFSG.AGLEmbedding.card_le_of_isCyclic_of_forall_pow_eq_one hp0 fun a => ?_
    obtain ⟨e, he⟩ := a.2
    have : a = ⟨φ e, ⟨e, rfl⟩⟩ := Subtype.ext he.symm
    rw [this]
    apply Subtype.ext
    simp only [Subgroup.coe_pow, ← map_pow, OneMemClass.coe_one]
    rw [show e ^ p = 1 from Subtype.ext (hE _ e.2), map_one]
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hEc' : Nat.card E = p ^ 2 :=
    le_antisymm (hmul ▸ (Nat.mul_le_mul hker hrange).trans_eq (sq p).symm) hEc
  rw [hEc'] at hmul
  have hk : Nat.card φ.ker = p ∧ Nat.card φ.range = p := by
    constructor <;> nlinarith [hp.two_le]
  obtain ⟨e₀, he₀, hne⟩ : ∃ e₀ ∈ E, q e₀ ≠ 1 := by
    by_contra hno
    push Not at hno
    have htop : φ.ker = ⊤ := by
      ext e
      simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
      exact hno e e.2
    rw [htop, Subgroup.card_top, hEc'] at hk
    have := hk.1
    nlinarith [hp.two_le]
  have hb₀ : (q e₀) ^ p = 1 := by rw [← map_pow, hE e₀ he₀, map_one]
  have hU : Nat.card (Subgroup.zpowers (q e₀)) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb₀ hne]
  have hqx : q x ∈ Subgroup.zpowers (q e₀) := by
    refine mem_of_pow_eq_one_of_card_eq hp0 _ hU ?_
    rw [← map_pow, hx, map_one]
  obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hqx
  have hek : e₀ ^ k ∈ E := E.zpow_mem he₀ k
  set e : A := e₀ ^ k with he
  have hn : e⁻¹ * x ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    show q (e⁻¹ * x) = 1
    rw [map_mul, map_inv, he, map_zpow, hk', inv_mul_cancel]
  have hxe : x = e * (e⁻¹ * x) := by group
  have hnp : (e⁻¹ * x) ^ p = 1 := by
    refine pow_eq_one_of_mul_pow_eq_one hp hp2 N hN hNp hn (hE e hek) ?_
    rw [← hxe]; exact hx
  have hcardEN : Nat.card ↥(E ⊓ N) = p := by
    have : Nat.card φ.ker = Nat.card ↥(E ⊓ N) := Nat.card_congr
      { toFun := fun e => ⟨(e.1 : A), e.1.2, hmem e⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          show q y.1 = 1
          exact (QuotientGroup.eq_one_iff _).mpr y.2.2⟩
        left_inv := fun e => rfl
        right_inv := fun y => rfl }
    rw [← this]; exact hk.1
  have hU' : Nat.card ((E ⊓ N).subgroupOf N) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hcardEN]
  have hnE : (⟨e⁻¹ * x, hn⟩ : N) ∈ (E ⊓ N).subgroupOf N :=
    mem_of_pow_eq_one_of_card_eq hp0 _ hU' (Subtype.ext hnp)
  rw [hxe]
  exact E.mul_mem hek (Subgroup.mem_subgroupOf.mp hnE).1

end CFSG.LocalAnalysis.RankThreeTheoremC
