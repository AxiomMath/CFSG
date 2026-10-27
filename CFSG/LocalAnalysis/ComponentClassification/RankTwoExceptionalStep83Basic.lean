module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Bar

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Step83Proof

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoStandard

section Lift

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem commute_of_odd_of_mk_commute {x a : A} (hx : x * x = 1)
    (hc : (a : A ⧸ center A) * (x : A ⧸ center A) = (x : A ⧸ center A) * (a : A ⧸ center A))
    (hodd : Odd (orderOf a)) : a * x = x * a := by
  set w := a * x * a⁻¹ * x⁻¹ with hw
  have hwZ : w ∈ center A := by
    rw [← QuotientGroup.eq_one_iff, hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc]
    group
  have hcomm : ∀ b : A, w * b = b * w := fun b => (mem_center_iff.mp hwZ b).symm
  have h1 : a * x * a⁻¹ = w * x := by rw [hw]; group
  have hpow : ∀ n : ℕ, a ^ n * x * (a ^ n)⁻¹ = w ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have haw : a * w ^ n = w ^ n * a := ((Commute.pow_left (hcomm a) n).eq).symm
      calc a ^ (n + 1) * x * (a ^ (n + 1))⁻¹ = a * (a ^ n * x * (a ^ n)⁻¹) * a⁻¹ := by group
        _ = a * w ^ n * x * a⁻¹ := by rw [ih]; group
        _ = w ^ n * (a * x * a⁻¹) := by rw [haw]; group
        _ = w ^ (n + 1) * x := by rw [h1]; group
  have hwo : w ^ orderOf a = 1 := by
    have h := hpow (orderOf a)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    exact mul_eq_right.mp h.symm
  have hw2 : w ^ 2 = 1 := by
    have h3 : (a * x * a⁻¹) * (a * x * a⁻¹) = 1 := by
      calc (a * x * a⁻¹) * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
        _ = 1 := by rw [hx]; group
    rw [h1] at h3
    have h4 : (w * x) * (w * x) = w * w * (x * x) := by
      calc (w * x) * (w * x) = w * (x * w) * x := by group
        _ = w * (w * x) * x := by rw [hcomm x]
        _ = w * w * (x * x) := by group
    rw [h4, hx, mul_one] at h3
    rw [sq]
    exact h3
  have hw1 : w = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hw2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · have h5 := orderOf_dvd_of_pow_eq_one hwo
      rw [h] at h5
      exact absurd (even_iff_two_dvd.mpr h5) (Nat.not_even_iff_odd.mpr hodd)
  calc a * x = w * x * a := by rw [hw]; group
    _ = x * a := by rw [hw1, one_mul]

theorem exists_odd_lift {x : A} (hx : x * x = 1) {c : A ⧸ center A}
    (hc : c * (x : A ⧸ center A) = (x : A ⧸ center A) * c) (hodd : Odd (orderOf c)) :
    ∃ a : A, a * x = x * a ∧ Odd (orderOf a) ∧ (a : A ⧸ center A) = c := by
  obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨b, -, hb, hbc⟩ := Lemma39.exists_odd_preimage (QuotientGroup.mk' (center A)) a₀ hodd
  have hbc' : (b : A ⧸ center A) = (a₀ : A ⧸ center A) := hbc
  refine ⟨b, commute_of_odd_of_mk_commute hx ?_ hb, hb, hbc'⟩
  rw [hbc']
  exact hc

theorem oUpperTwo_centralizer_le {x y : A} (hx : x * x = 1)
    (h : ∀ a : A, a * x = x * a → Odd (orderOf a) → a * y = y * a) :
    oUpperTwo (centralizer ({(x : A ⧸ center A)} : Set (A ⧸ center A))) ≤
      centralizer ({(y : A ⧸ center A)} : Set (A ⧸ center A)) := by
  refine (closure_le _).mpr ?_
  rintro c ⟨hc, hodd⟩
  rw [mem_centralizer_singleton_iff] at hc
  obtain ⟨a, hax, hao, rfl⟩ := exists_odd_lift hx hc hodd
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, h a hax hao]

end Lift

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

namespace Sec3

variable (hc : Sec3 A R T g)
include hc

theorem commute_of_mem_R {a r : G} (ha : a ∈ A) (hr : r ∈ R) : Commute a r :=
  mem_centralizer_iff.mp (hc.sylowR.le hr) a ha

theorem commute_T_R {t r : G} (ht : t ∈ T) (hr : r ∈ R) : t * r = r * t :=
  (mem_centralizer_iff.mp (hc.le_centralizer ht) r hr).symm

theorem inf_centralizer_eq_bot : T ⊓ centralizer (A : Set G) = ⊥ := by
  have hKte := tightlyEmbedded_centralizer hc.hyp.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hc.not_mem
  exact two_subgroup_inf_conjugate_eq_bot _ T hKte hc.sylowT.isPGroup g hgK hc.sylowT.le

theorem aPart_mul_self (h32 : Lemma32) {t p : G} (ht : t ∈ T) (hρ : t⁻¹ * p ∈ R) : p * p = 1 := by
  set r := t⁻¹ * p with hr
  have hp : p = t * r := by rw [hr]; group
  have htr : t * r = r * t := commute_T_R hc ht hρ
  have ht2 : t * t = 1 := by rw [← sq]; exact (hc.elemT h32).2 t ht
  have hr2 : r * r = 1 := by rw [← sq]; exact (hc.elemR h32).2 r hρ
  rw [hp]
  calc t * r * (t * r) = t * (r * t) * r := by group
    _ = t * (t * r) * r := by rw [htr]
    _ = (t * t) * (r * r) := by group
    _ = 1 := by rw [ht2, hr2, one_mul]

theorem aPart_commute (h32 : Lemma32) {t p s : G} (ht : t ∈ T) (hρ : t⁻¹ * p ∈ R) (hs : s ∈ T) :
    p * s = s * p := by
  have hp : p = t * (t⁻¹ * p) := by group
  have hts : t * s = s * t := (hc.elemT h32).1.is_comm.comm ⟨t, ht⟩ ⟨s, hs⟩ |> congrArg Subtype.val
  have hrs : (t⁻¹ * p) * s = s * (t⁻¹ * p) := (commute_T_R hc hs hρ).symm
  rw [hp]
  calc t * (t⁻¹ * p) * s = t * ((t⁻¹ * p) * s) := by group
    _ = t * (s * (t⁻¹ * p)) := by rw [hrs]
    _ = (t * s) * (t⁻¹ * p) := by group
    _ = (s * t) * (t⁻¹ * p) := by rw [hts]
    _ = s * (t * (t⁻¹ * p)) := by group

theorem inf_centralizer_eq {t p : G} (hρ : t⁻¹ * p ∈ R) :
    A ⊓ centralizer ({t} : Set G) = A ⊓ centralizer ({p} : Set G) := by
  ext a
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun ha => ?_
  have hr : Commute a (t⁻¹ * p) := commute_of_mem_R hc ha hρ
  constructor
  · intro h
    have h2 := (show Commute a t from h).mul_right hr
    rwa [mul_inv_cancel_left] at h2
  · intro h
    have h2 := (show Commute a p from h).mul_right hr.inv_right
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h2

theorem eq_of_mk_aPart_eq {s t p q : G} (hs : s ∈ T) (ht : t ∈ T) (hp : p ∈ A) (hq : q ∈ A)
    (hρs : s⁻¹ * p ∈ R) (hρt : t⁻¹ * q ∈ R)
    (h : ((⟨p, hp⟩ : A) : A ⧸ center A) = ((⟨q, hq⟩ : A) : A ⧸ center A)) : s = t := by
  have hpq : (⟨p, hp⟩ : A)⁻¹ * ⟨q, hq⟩ ∈ center A := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel]
  have hpqK : p⁻¹ * q ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := congrArg Subtype.val (mem_center_iff.mp hpq ⟨a, ha⟩)
    simpa using this
  have hst : s⁻¹ * t ∈ T ⊓ centralizer (A : Set G) := by
    refine mem_inf.mpr ⟨T.mul_mem (T.inv_mem hs) ht, ?_⟩
    have e : s⁻¹ * t = (s⁻¹ * p) * (p⁻¹ * q) * (t⁻¹ * q)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hc.sylowR.le hρs) hpqK) (inv_mem (hc.sylowR.le hρt))
  rw [inf_centralizer_eq_bot hc, mem_bot] at hst
  calc s = s * (s⁻¹ * t) := by rw [hst, mul_one]
    _ = t := by group

theorem conj_mem_of_mem_center {z : G} (hzA : z ∈ A) (hzK : z ∈ centralizer (A : Set G))
    {k : ℕ} (hzk : z ^ 2 ^ k = 1) : g⁻¹ * z * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := g⁻¹ * z * g with hw
  have hwK : w ∈ rightConjugate (centralizer (A : Set G)) g := by
    rw [mem_rightConjugate_iff, hw]
    simpa [mul_assoc] using hzK
  have hwcent : ∀ x ∈ rightConjugate (centralizer (A : Set G)) g, x * w = w * x := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := mem_centralizer_iff.mp hx z hzA
    calc x * w = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [hw]; group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [← h1]
      _ = w * x := by rw [hw]; group
  have hwp : IsPGroup 2 (zpowers w) := by
    have hd : orderOf w ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hw, show g⁻¹ * z * g = g⁻¹ * z * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hzk]
      group
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hwC : w ∈ centralizer (T : Set G) :=
    mem_centralizer_iff.mpr fun x hx => hwcent x (hc.sylowT.le hx)
  have hle : zpowers w ≤ normalizer (T : Set G) :=
    (zpowers_le.mpr hwC).trans (centralizer_le_normalizer _)
  have hsup : IsPGroup 2 ↥(zpowers w ⊔ T) :=
    IsPGroup.to_sup_of_normal_right' hwp hc.sylowT.isPGroup hle
  have heq := hc.sylowT.eq_of_le le_sup_right
    (sup_le (zpowers_le.mpr hwK) hc.sylowT.le) hsup
  exact heq ▸ mem_sup_left (mem_zpowers w)

end Sec3

end CFSG.ComponentClassification.RankTwoExceptional.Step83Proof
