module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ExpAux1
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section General

variable {X : Type*} [Group X]

theorem zje_isPGroup_zpowers {p : ℕ} {x : X} (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    IsPGroup p (zpowers x) := by
  obtain ⟨k, hk⟩ := hx
  exact IsPGroup.of_card_dvd_pow (n := k) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk)

theorem zje_isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup X} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem zje_exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K Q : Subgroup X} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ S : Subgroup X, IsSylowOf p S K ∧ Q ≤ S := by
  obtain ⟨T, hT⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun y hy => ⟨⟨y, hQK hy⟩, hT hy, rfl⟩⟩

theorem zje_mem_of_isSylowOf_centralizer {p : ℕ} [Fact p.Prime] [Finite X] {D : Subgroup X}
    (hsyl : IsSylowOf p D (centralizer (D : Set X))) {y : X}
    (hy : y ∈ centralizer (D : Set X)) (hyp : ∃ k : ℕ, y ^ p ^ k = 1) : y ∈ D := by
  obtain ⟨S, hS, hyS⟩ := zje_exists_isSylowOf_ge (zpowers_le.mpr hy) (zje_isPGroup_zpowers hyp)
  obtain ⟨c, hcK, hconj⟩ := hsyl.exists_mem_conj hS
  have hd : c⁻¹ * y * c ∈ D := (hconj y).1 (hyS (mem_zpowers y))
  have h1 := mem_centralizer_iff.1 hcK _ hd
  have h2 : y = c⁻¹ * y * c := by
    calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
      _ = (c⁻¹ * y * c) * c * c⁻¹ := by rw [← h1]
      _ = c⁻¹ * y * c := by group
  rwa [h2]

theorem zje_conj_mem_centralizer {D : Subgroup X} {e : X} (he : e ∈ normalizer (D : Set X))
    {c : X} (hc : c ∈ centralizer (D : Set X)) : e * c * e⁻¹ ∈ centralizer (D : Set X) := by
  rw [mem_centralizer_iff]
  intro u hu
  have hu' : e⁻¹ * u * e ∈ D := by
    simpa using (mem_normalizer_iff.1 (inv_mem he) u).1 hu
  have h1 := mem_centralizer_iff.1 hc _ hu'
  calc u * (e * c * e⁻¹) = e * ((e⁻¹ * u * e) * c) * e⁻¹ := by group
    _ = e * (c * (e⁻¹ * u * e)) * e⁻¹ := by rw [h1]
    _ = e * c * e⁻¹ * u := by group

theorem zje_pow_mul_eq {a b z : X} (hzb : Commute z b) (hba : b * a = z * (a * b)) (m : ℕ) :
    b ^ m * a = z ^ m * (a * b ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hzbm : Commute (z ^ m) (b ^ m) := (hzb.pow_left m).pow_right m
    calc b ^ (m + 1) * a = b ^ m * (b * a) := by rw [pow_succ, mul_assoc]
      _ = b ^ m * (z * (a * b)) := by rw [hba]
      _ = z * (b ^ m * a) * b := by
          rw [← mul_assoc, ← (hzb.pow_right m).eq]
          simp only [mul_assoc]
      _ = z * (z ^ m * (a * b ^ m)) * b := by rw [ih]
      _ = z ^ (m + 1) * (a * b ^ (m + 1)) := by
          rw [pow_succ' z m, pow_succ b m]
          simp only [mul_assoc]

theorem zje_mul_pow {a b z : X} (hza : Commute z a) (hzb : Commute z b)
    (hba : b * a = z * (a * b)) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n * z ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzab : Commute (z ^ n.choose 2) (a * b) := (hza.mul_right hzb).pow_left _
    have hzan : Commute (z ^ n) (a ^ n) := (hza.pow_right n).pow_left n
    have hzn : Commute (z ^ n) (a ^ (n + 1) * b ^ (n + 1)) :=
      ((hza.pow_right _).mul_right (hzb.pow_right _)).pow_left n
    calc (a * b) ^ (n + 1) = a ^ n * b ^ n * z ^ n.choose 2 * (a * b) := by rw [pow_succ, ih]
      _ = a ^ n * b ^ n * (a * b) * z ^ n.choose 2 := by
          rw [mul_assoc (a ^ n * b ^ n), hzab.eq, ← mul_assoc]
      _ = a ^ n * (b ^ n * a) * b * z ^ n.choose 2 := by simp only [mul_assoc]
      _ = a ^ n * (z ^ n * (a * b ^ n)) * b * z ^ n.choose 2 := by
          rw [zje_pow_mul_eq hzb hba n]
      _ = z ^ n * (a ^ n * a) * (b ^ n * b) * z ^ n.choose 2 := by
          rw [show a ^ n * (z ^ n * (a * b ^ n)) * b = (a ^ n * z ^ n) * a * b ^ n * b by
            simp only [mul_assoc], ← hzan.eq]
          simp only [mul_assoc]
      _ = z ^ n * (a ^ (n + 1) * b ^ (n + 1)) * z ^ n.choose 2 := by
          rw [← pow_succ, ← pow_succ]
          simp only [mul_assoc]
      _ = a ^ (n + 1) * b ^ (n + 1) * z ^ (n + n.choose 2) := by
          rw [hzn.eq, pow_add z n (n.choose 2)]
          simp only [mul_assoc]
      _ = a ^ (n + 1) * b ^ (n + 1) * z ^ (n + 1).choose 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]

variable [Finite X]

theorem zje_exists_fixed {p : ℕ} [Fact p.Prime] {D : Subgroup X} (hD : IsPGroup p D)
    (hDne : D ≠ ⊥) {x : X} (hxN : x ∈ normalizer (D : Set X)) (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    ∃ w ∈ D, w ≠ 1 ∧ x * w = w * x := by
  have hxle : zpowers x ≤ normalizer (D : Set X) := zpowers_le.mpr hxN
  have hR : IsPGroup p (D ⊔ zpowers x : Subgroup X) :=
    hD.to_sup_of_normal_left' (zje_isPGroup_zpowers hx) hxle
  have hDR : D ≤ D ⊔ zpowers x := le_sup_left
  have hxR : x ∈ D ⊔ zpowers x := Subgroup.mem_sup_right (mem_zpowers x)
  have : Group.IsNilpotent ↥(D ⊔ zpowers x) := hR.isNilpotent
  have hnorm : (D.subgroupOf (D ⊔ zpowers x)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDR).2 (sup_le Subgroup.le_normalizer hxle)
  have hne : D.subgroupOf (D ⊔ zpowers x) ≠ ⊥ := by
    obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨d, hDR hd⟩, hd⟩, fun h => hd1 ?_⟩
    exact Subtype.ext (congrArg (fun a : ↥(D ⊔ zpowers x) => (a : X)) (congrArg Subtype.val h))
  obtain ⟨⟨w, hwH, hwZ⟩, hw1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(w : X), hwH, fun h => hw1 (Subtype.ext (Subtype.ext h)), ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨x, hxR⟩)

end General

section Main

variable {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {D : Subgroup X}

theorem zje_exp_of_inverting (hp2 : p ≠ 2) (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2)
    (hC : ∀ y ∈ centralizer (D : Set X), (∃ k : ℕ, y ^ p ^ k = 1) → y ∈ D) {g : X}
    (hgN : g ∈ normalizer (D : Set X)) (hg : ∀ d ∈ D, g * d * g⁻¹ = d⁻¹) :
    NormalizerExponent p D := by
  have hp : p.Prime := Fact.out
  have hp3 : 2 < p := by have := hp.two_le; omega
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hxN hxk
  by_cases hxC : x ∈ centralizer (D : Set X)
  · exact hD.2 x (hC x hxC hxk)
  obtain ⟨k, hk⟩ := hxk
  have hDne : D ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hDc
    have := hp.one_lt
    nlinarith
  obtain ⟨w, hwD, hw1, hxw⟩ :=
    zje_exists_fixed (zje_isPGroup_of_isElemAbelian hD) hDne hxN ⟨k, hk⟩
  have hwp : w ^ p = 1 := hD.2 w hwD
  have hnotle : ¬ D ≤ zpowers w := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hwp hw1, hDc] at h1
    have := hp.one_lt
    nlinarith
  obtain ⟨d, hdD, hdw⟩ := IsConcreteLE.not_le_iff_exists.1 hnotle
  obtain ⟨b, hb0, hxd⟩ := zje_transvection_form hD hDc hwD hw1 ⟨k, hk⟩ hxN hxw hxC hdD hdw
  have hxw' : x * w * x⁻¹ = w := by rw [hxw, mul_inv_cancel_right]
  have hform : ∀ u ∈ D, ∃ t : ℕ, x * u * x⁻¹ = u * w ^ t := by
    intro u hu
    obtain ⟨s, r, rfl⟩ := exists_pow_mul_pow_of_mem_plane hD hDc hwD hw1 hdD hdw hu
    refine ⟨b * s, ?_⟩
    have hdw' : Commute d (w ^ b) :=
      (show Commute d w from hcomm d hdD w hwD).pow_right b
    calc x * (d ^ s * w ^ r) * x⁻¹ = (x * d * x⁻¹) ^ s * (x * w * x⁻¹) ^ r := by
          rw [conj_pow, conj_pow]; group
      _ = (d * w ^ b) ^ s * w ^ r := by rw [hxd, hxw']
      _ = d ^ s * (w ^ b) ^ s * w ^ r := by rw [hdw'.mul_pow]
      _ = d ^ s * w ^ r * w ^ (b * s) := by rw [← pow_mul]; group
  have hxpC : x ^ p ∈ centralizer (D : Set X) := by
    rw [mem_centralizer_iff]
    intro u hu
    obtain ⟨t, ht⟩ := hform u hu
    have h1 := transvection_conj_pow_eq hxw ht p
    rw [pow_mul, hwp, one_pow, mul_one] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hxpD : x ^ p ∈ D :=
    hC _ hxpC ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
  have hgd : ∀ u ∈ D, g⁻¹ * u * g = u⁻¹ := by
    intro u hu
    have h := hg u⁻¹ (inv_mem hu)
    rw [inv_inv] at h
    calc g⁻¹ * u * g = g⁻¹ * (g * u⁻¹ * g⁻¹) * g := by rw [h]
      _ = u⁻¹ := by group
  obtain ⟨x', hx'⟩ : ∃ x' : X, x' = g * x * g⁻¹ := ⟨_, rfl⟩
  have hyC : x⁻¹ * x' ∈ centralizer (D : Set X) := by
    rw [mem_centralizer_iff]
    intro u hu
    have hu₁ : g⁻¹ * u * g = u⁻¹ := hgd u hu
    have hxu : x * u * x⁻¹ ∈ D := (mem_normalizer_iff.1 hxN u).1 hu
    have hgxu : g * (x * u * x⁻¹) * g⁻¹ = (x * u * x⁻¹)⁻¹ := hg _ hxu
    have key : x⁻¹ * (g * (x * (g⁻¹ * u * g) * x⁻¹) * g⁻¹) * x = u := by
      rw [hu₁]
      have e1 : x * u⁻¹ * x⁻¹ = (x * u * x⁻¹)⁻¹ := by group
      rw [e1]
      have e2 : g * (x * u * x⁻¹)⁻¹ * g⁻¹ = (g * (x * u * x⁻¹) * g⁻¹)⁻¹ := by group
      rw [e2, hgxu, inv_inv]
      group
    have key' : (x⁻¹ * x') * u * (x⁻¹ * x')⁻¹ = u := by
      calc (x⁻¹ * x') * u * (x⁻¹ * x')⁻¹
          = x⁻¹ * (g * (x * (g⁻¹ * u * g) * x⁻¹) * g⁻¹) * x := by rw [hx']; group
        _ = u := key
    exact (mul_inv_eq_iff_eq_mul.1 key').symm
  have hx'k : ∃ k : ℕ, x' ^ p ^ k = 1 := ⟨k, by rw [hx', conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hx'p : x' ^ p = (x ^ p)⁻¹ := by rw [hx', conj_pow]; exact hg _ hxpD
  have hxz : zpowers x ≤ normalizer ((centralizer (D : Set X) : Subgroup X) : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    refine ⟨fun hh => zje_conj_mem_centralizer hxN hh, fun hh => ?_⟩
    have := zje_conj_mem_centralizer (inv_mem hxN) hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [e] at this
  have hmulE := coe_mul_of_right_le_normalizer_left (centralizer (D : Set X)) (zpowers x) hxz
  have hxE : zpowers x ≤ centralizer (D : Set X) ⊔ zpowers x := le_sup_right
  have hx'E : zpowers x' ≤ centralizer (D : Set X) ⊔ zpowers x := by
    rw [zpowers_le]
    have : x' = x * (x⁻¹ * x') := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right (mem_zpowers x)) (Subgroup.mem_sup_left hyC)
  obtain ⟨S₁, hS₁, hxS₁⟩ := zje_exists_isSylowOf_ge hxE (zje_isPGroup_zpowers ⟨k, hk⟩)
  obtain ⟨S₂, hS₂, hx'S₂⟩ := zje_exists_isSylowOf_ge hx'E (zje_isPGroup_zpowers hx'k)
  obtain ⟨e, heE, hconj⟩ := hS₁.exists_mem_conj hS₂
  have heE' : e ∈ ((centralizer (D : Set X) : Subgroup X) : Set X) * (zpowers x : Set X) := by
    rw [← hmulE]
    exact heE
  obtain ⟨c, hcC, s, hs, rfl⟩ := Set.mem_mul.1 heE'
  have hsS₁ : s ∈ S₁ := hxS₁ hs
  have hxS : x ∈ S₁ := hxS₁ (mem_zpowers x)
  have h1 : (c * s)⁻¹ * x' * (c * s) ∈ S₁ := (hconj x').1 (hx'S₂ (mem_zpowers x'))
  have hx'' : c⁻¹ * x' * c ∈ S₁ := by
    have : c⁻¹ * x' * c = s * ((c * s)⁻¹ * x' * (c * s)) * s⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hsS₁ h1) (inv_mem hsS₁)
  obtain ⟨u, hu_def⟩ : ∃ u : X, u = x⁻¹ * (c⁻¹ * x' * c) := ⟨_, rfl⟩
  have huS : u ∈ S₁ := by rw [hu_def]; exact mul_mem (inv_mem hxS) hx''
  have huC : u ∈ centralizer (D : Set X) := by
    have e3 : u = (x⁻¹ * c⁻¹ * x) * ((x⁻¹ * x') * c) := by rw [hu_def]; group
    rw [e3]
    refine mul_mem ?_ (mul_mem hyC hcC)
    have := zje_conj_mem_centralizer (inv_mem hxN) (inv_mem hcC)
    have e4 : x⁻¹ * c⁻¹ * x⁻¹⁻¹ = x⁻¹ * c⁻¹ * x := by rw [inv_inv]
    rwa [e4] at this
  have huD : u ∈ D := by
    refine hC _ huC ?_
    obtain ⟨k', hk'⟩ := hS₁.isPGroup ⟨u, huS⟩
    exact ⟨k', by simpa using congrArg Subtype.val hk'⟩
  have hu' : c⁻¹ * x' * c = x * u := by rw [hu_def]; group
  have h3 : (c⁻¹ * x' * c) ^ p = (x ^ p)⁻¹ := by
    have hconjpow : (c⁻¹ * x' * c) ^ p = c⁻¹ * x' ^ p * c := by
      simpa using (conj_pow (a := c⁻¹) (b := x') (i := p))
    rw [hconjpow, hx'p]
    have h4 := mem_centralizer_iff.1 hcC _ (inv_mem hxpD)
    calc c⁻¹ * (x ^ p)⁻¹ * c = c⁻¹ * ((x ^ p)⁻¹ * c) := by group
      _ = c⁻¹ * (c * (x ^ p)⁻¹) := by rw [h4]
      _ = (x ^ p)⁻¹ := by group
  have h5 : (x * u) ^ p = x ^ p := by
    obtain ⟨t, ht⟩ := hform u huD
    have huw : u * w ^ t = w ^ t * u := hcomm u huD _ (pow_mem hwD t)
    have ht' : x * u * x⁻¹ = w ^ t * u := by rw [ht, huw]
    have hxu : x * u = w ^ t * u * x := mul_inv_eq_iff_eq_mul.1 ht'
    have hrel : u * x = (w ^ t)⁻¹ * (x * u) := by rw [hxu]; group
    have hxwt : Commute x (w ^ t) := (show Commute x w from hxw).pow_right t
    have hza : Commute (w ^ t)⁻¹ x := hxwt.inv_right.symm
    have hzb : Commute (w ^ t)⁻¹ u := (show Commute u (w ^ t) from huw).inv_right.symm
    have hwtp : (w ^ t) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hwp, one_pow]
    have h7 : ((w ^ t)⁻¹) ^ p.choose 2 = 1 := by
      obtain ⟨m, hm⟩ := hp.dvd_choose_self (by norm_num : 2 ≠ 0) hp3
      rw [hm, pow_mul, inv_pow, hwtp, inv_one, one_pow]
    rw [zje_mul_pow hza hzb hrel p, hD.2 u huD, h7, mul_one, mul_one]
  have h8 : (x ^ p)⁻¹ = x ^ p := by rw [← h3, hu', h5]
  have h9 : (x ^ p) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← h8]
    exact inv_mul_cancel _
  have h10 : (x ^ p) ^ p = 1 := hD.2 _ hxpD
  have h11 : orderOf (x ^ p) = 1 := by
    have h12 : orderOf (x ^ p) ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h9) (orderOf_dvd_of_pow_eq_one h10)
    rw [((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)).gcd_eq_one] at h12
    exact Nat.dvd_one.1 h12
  exact orderOf_eq_one_iff.1 h11

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC
