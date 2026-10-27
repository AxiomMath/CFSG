module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineCount

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def secKer (N U R : Subgroup G) (hNU : N ≤ normalizer (U : Set G))
    (hNR : N ≤ normalizer (R : Set G)) : Subgroup G where
  carrier := {g | g ∈ N ∧ ∀ a ∈ U, g * a * g⁻¹ * a⁻¹ ∈ R}
  one_mem' := ⟨N.one_mem, fun a _ => by simp [R.one_mem]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgR⟩ ⟨hh, hhR⟩
    refine ⟨N.mul_mem hg hh, fun a ha => ?_⟩
    have e : g * h * a * (g * h)⁻¹ * a⁻¹ =
        (g * (h * a * h⁻¹ * a⁻¹) * g⁻¹) * (g * a * g⁻¹ * a⁻¹) := by group
    rw [e]
    exact R.mul_mem ((mem_normalizer_iff.mp (hNR hg) _).mp (hhR a ha)) (hgR a ha)
  inv_mem' := by
    rintro g ⟨hg, hgR⟩
    refine ⟨N.inv_mem hg, fun a ha => ?_⟩
    have hb : g⁻¹ * a * g ∈ U := by
      have h := (mem_normalizer_iff.mp (hNU (N.inv_mem hg)) a).mp ha
      rwa [inv_inv] at h
    have h1 := hgR _ hb
    have e : g⁻¹ * a * g⁻¹⁻¹ * a⁻¹ = (g * (g⁻¹ * a * g) * g⁻¹ * (g⁻¹ * a * g)⁻¹)⁻¹ := by group
    rw [e]
    exact R.inv_mem h1

section SecKer

variable {N U R : Subgroup G} {hNU : N ≤ normalizer (U : Set G)}
  {hNR : N ≤ normalizer (R : Set G)}

theorem conj_mem_secKer {g d : G} (hg : g ∈ N) (hd : d ∈ secKer N U R hNU hNR) :
    g * d * g⁻¹ ∈ secKer N U R hNU hNR := by
  refine ⟨N.mul_mem (N.mul_mem hg hd.1) (N.inv_mem hg), fun a ha => ?_⟩
  have hb : g⁻¹ * a * g ∈ U := by
    have h := (mem_normalizer_iff.mp (hNU (N.inv_mem hg)) a).mp ha
    rwa [inv_inv] at h
  have h1 := hd.2 _ hb
  have e : g * d * g⁻¹ * a * (g * d * g⁻¹)⁻¹ * a⁻¹ =
      g * (d * (g⁻¹ * a * g) * d⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp (hNR hg) _).mp h1

theorem mem_secKer_of_mem (hUN : U ≤ N) (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ R)
    {u : G} (hu : u ∈ U) : u ∈ secKer N U R hNU hNR :=
  ⟨hUN hu, fun a ha => hcomm u hu a ha⟩

end SecKer

theorem exists_isSylowOf_normalized [Finite G] {p : ℕ} [hp : Fact p.Prime] {W A : Subgroup G}
    (hA : IsPGroup p A) (hAW : A ≤ normalizer (W : Set G)) :
    ∃ P : Subgroup G, IsSylowOf p P W ∧ A ≤ normalizer (P : Set G) := by
  let _ : MulDistribMulAction A W := Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAW
  have hcard : ¬ p ∣ Nat.card (Sylow p W) := by
    intro h
    have h1 := card_sylow_modEq_one p W
    rw [Nat.ModEq, Nat.mod_eq_of_lt hp.out.one_lt, (Nat.dvd_iff_mod_eq_zero).mp h] at h1
    exact zero_ne_one h1
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p W) hcard
  refine ⟨(S : Subgroup W).map W.subtype, ⟨S, rfl⟩, fun a ha => mem_normalizer_iff.2 fun x => ?_⟩
  have hfix : (⟨a, ha⟩ : A) • (S : Subgroup W) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : A) • s ∈ (S : Subgroup W) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s _ _ hs
    exact ⟨_, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : G) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

theorem exists_two_mul_odd [Finite G] (g : G) :
    ∃ g₂ g₀ : G, g = g₂ * g₀ ∧ (∃ k : ℕ, g₂ ^ (2 ^ k) = 1) ∧ Odd (orderOf g₀) ∧
      g₂ ∈ zpowers g ∧ g₀ ∈ zpowers g := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set A := Nat.gcdA (2 ^ k) m
  set B := Nat.gcdB (2 ^ k) m
  refine ⟨g ^ ((m : ℤ) * B), g ^ (((2 ^ k : ℕ) : ℤ) * A), ?_, ⟨k, ?_⟩, ?_, zpow_mem_zpowers _ _,
    zpow_mem_zpowers _ _⟩
  · rw [← zpow_add, add_comm, ← hbez, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have e : (m : ℤ) * B * ((2 ^ k : ℕ) : ℤ) = (orderOf g : ℤ) * B := by
      rw [hn]; push_cast; ring
    rw [e, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : (g ^ (((2 ^ k : ℕ) : ℤ) * A)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have e : ((2 ^ k : ℕ) : ℤ) * A * (m : ℤ) = (orderOf g : ℤ) * A := by
        rw [hn]; push_cast; ring
      rw [e, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem le_normalizer_of_conj_mem {S H : Subgroup G} (h : ∀ g ∈ S, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    S ≤ normalizer (H : Set G) := by
  intro g hg
  refine mem_normalizer_iff.mpr fun x => ⟨h g hg x, fun hx => ?_⟩
  have h' := h g⁻¹ (S.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h'

theorem isPGroup_zpowers_of_pow {p : ℕ} {g : G} {k : ℕ} (h : g ^ (p ^ k) = 1) :
    IsPGroup p (zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  change (g ^ j) ^ (p ^ k) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem conj_eq_inv_of_mem_zpowers {t g h : G} (htg : t * g * t⁻¹ = g⁻¹) (hh : h ∈ zpowers g) :
    t * h * t⁻¹ = h⁻¹ := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
  have e : t * g ^ j * t⁻¹ = (t * g * t⁻¹) ^ j := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [e, htg, inv_zpow]

theorem exists_comm_lift [Finite G] {N U R K : Subgroup G} {t : G}
    (hUK : U ≤ K) (hKN : K ≤ N) (hNU : N ≤ normalizer (U : Set G))
    (hNR : N ≤ normalizer (R : Set G)) (hNK : N ≤ normalizer (K : Set G))
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ R) (hsyl : IsSylowOf 2 U K) (ht : t ∈ N)
    (ht2 : t ^ 2 = 1)
    (hconj : ∀ g : G, g * t * g⁻¹ ∈ U ⊔ zpowers t → ∃ u ∈ U, g * t * g⁻¹ = u * t * u⁻¹)
    {x : G} (hxK : x ∈ K) (hxt : x * t * x⁻¹ * t⁻¹ ∈ secKer N U R hNU hNR) :
    ∃ x' ∈ K, x' * t = t * x' ∧ x'⁻¹ * x ∈ secKer N U R hNU hNR := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := secKer N U R hNU hNR with hD
  set DK := K ⊓ D with hDK
  have hUD : U ≤ D := fun u hu => mem_secKer_of_mem (hUK.trans hKN) hcomm hu
  have hUDK : U ≤ DK := le_inf hUK hUD
  have hsylD : IsSylowOf 2 U DK := hsyl.of_le hUDK inf_le_left
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hxN : x ∈ N := hKN hxK
  have hconjK : ∀ g ∈ N, ∀ y ∈ K, g * y * g⁻¹ ∈ K := fun g hg y hy =>
    (mem_normalizer_iff.mp (hNK hg) y).mp hy
  have hNDK : N ≤ normalizer (DK : Set G) := le_normalizer_of_conj_mem fun g hg y hy =>
    ⟨hconjK g hg y hy.1, conj_mem_secKer hg hy.2⟩
  obtain ⟨s, hs⟩ : ∃ s, s = x * t * x⁻¹ := ⟨_, rfl⟩
  have hsN : s ∈ N := by rw [hs]; exact N.mul_mem (N.mul_mem hxN ht) (N.inv_mem hxN)
  have hss : s * s = 1 := by
    rw [hs]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hs2 : s ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two, hss]
  obtain ⟨P, hP, hsPn⟩ := exists_isSylowOf_normalized (isPGroup_zpowers_of_pow hs2)
    ((zpowers_le (H := normalizer (DK : Set G))).mpr (hNDK hsN))
  obtain ⟨k, hkDK, hk⟩ := hsylD.exists_mem_conj hP
  have hsP : s ∈ normalizer (P : Set G) := hsPn (mem_zpowers s)
  obtain ⟨s', hs'⟩ : ∃ s', s' = k⁻¹ * s * k := ⟨_, rfl⟩
  have hs'U : s' ∈ normalizer (U : Set G) := by
    refine mem_normalizer_iff.mpr fun z => ?_
    have h1 : z ∈ U ↔ k * z * k⁻¹ ∈ P := by
      rw [hk]
      have e : k⁻¹ * (k * z * k⁻¹) * k = z := by group
      rw [e]
    have h2 : s' * z * s'⁻¹ ∈ U ↔ s * (k * z * k⁻¹) * s⁻¹ ∈ P := by
      rw [hk]
      have e : k⁻¹ * (s * (k * z * k⁻¹) * s⁻¹) * k = s' * z * s'⁻¹ := by rw [hs']; group
      rw [e]
    rw [h1, h2]
    exact mem_normalizer_iff.mp hsP _
  obtain ⟨d, hd⟩ : ∃ d, d = t⁻¹ * s' := ⟨_, rfl⟩
  have hdU : d ∈ normalizer (U : Set G) := by
    rw [hd]; exact (normalizer _).mul_mem ((normalizer _).inv_mem (hNU ht)) hs'U
  have hdK : d ∈ K := by
    have e : d = (t⁻¹ * (k⁻¹ * x) * t⁻¹⁻¹) * (x⁻¹ * k) := by rw [hd, hs', hs]; group
    rw [e]
    exact K.mul_mem (hconjK _ (N.inv_mem ht) _ (K.mul_mem (K.inv_mem hkDK.1) hxK))
      (K.mul_mem (K.inv_mem hxK) hkDK.1)
  have hdD : d ∈ D := by
    have e : d = (t⁻¹ * (k⁻¹ * (x * t * x⁻¹ * t⁻¹)) * t⁻¹⁻¹) * k := by
      rw [hd, hs', hs]; group
    rw [e]
    exact D.mul_mem (conj_mem_secKer (N.inv_mem ht) (D.mul_mem (D.inv_mem hkDK.2) hxt)) hkDK.2
  have htd : t * d = s' := by rw [hd, ← mul_assoc, mul_inv_cancel, one_mul]
  have hs's : s' * s' = 1 := by
    rw [hs']
    calc k⁻¹ * s * k * (k⁻¹ * s * k) = k⁻¹ * (s * s) * k := by group
      _ = 1 := by rw [hss, mul_one, inv_mul_cancel]
  have hdinv : t * d * t⁻¹ = d⁻¹ := by
    have h1 : t * d * (t * d) = 1 := by rw [htd, hs's]
    rw [htinv]
    calc t * d * t = t * d * (t * d) * d⁻¹ := by group
      _ = d⁻¹ := by rw [h1, one_mul]
  obtain ⟨d₂, d₀, hdd, ⟨a, ha⟩, hodd, hd₂z, hd₀z⟩ := exists_two_mul_odd d
  have hdM : d ∈ DK ⊓ normalizer (U : Set G) := ⟨⟨hdK, hdD⟩, hdU⟩
  have hd₂M : d₂ ∈ DK ⊓ normalizer (U : Set G) := (zpowers_le.mpr hdM) hd₂z
  have hd₂U : d₂ ∈ U := by
    have hP2 : IsPGroup 2 ↥(zpowers d₂ ⊔ U) :=
      IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow ha) hsylD.isPGroup
        (zpowers_le.mpr hd₂M.2)
    have heq := hsylD.eq_of_le le_sup_right (sup_le (zpowers_le.mpr hd₂M.1) hUDK) hP2
    rw [← heq]
    exact mem_sup_left (mem_zpowers d₂)
  obtain ⟨r, hr⟩ := hodd
  obtain ⟨e, he⟩ : ∃ e, e = d₀ ^ (r + 1) := ⟨_, rfl⟩
  have hee : e * e = d₀ := by
    rw [he, ← pow_add, show r + 1 + (r + 1) = orderOf d₀ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hez : e ∈ zpowers d := by rw [he]; exact (zpowers d).pow_mem hd₀z _
  have heM : e ∈ DK ⊓ normalizer (U : Set G) := (zpowers_le.mpr hdM) hez
  have hte : t * e * t⁻¹ = e⁻¹ := conj_eq_inv_of_mem_zpowers hdinv hez
  have hd₂e : d₂ * e = e * d₂ := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hd₂z
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hez
    exact (Commute.zpow_zpow_self d i j).eq
  have hes' : e * s' * e⁻¹ = t * d₂ := by
    have hs'd : s' = t * (d₂ * (e * e)) := by rw [hee, ← hdd, htd]
    calc e * s' * e⁻¹ = e * (t * (d₂ * (e * e))) * e⁻¹ := by rw [hs'd]
      _ = e * t * (d₂ * e) := by group
      _ = e * t * (e * d₂) := by rw [hd₂e]
      _ = e * (t * e * t⁻¹) * t * d₂ := by group
      _ = t * d₂ := by rw [hte]; group
  obtain ⟨g, hg⟩ : ∃ g, g = e * k⁻¹ * x := ⟨_, rfl⟩
  have hgt : g * t * g⁻¹ = t * d₂ := by
    rw [← hes', hg, hs', hs]; group
  have hmem : g * t * g⁻¹ ∈ U ⊔ zpowers t := by
    rw [hgt]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hd₂U)
  obtain ⟨u, hu, hut⟩ := hconj g hmem
  refine ⟨u⁻¹ * g, ?_, ?_, ?_⟩
  · rw [hg]
    exact K.mul_mem (K.inv_mem (hUK hu)) (K.mul_mem (K.mul_mem heM.1.1 (K.inv_mem hkDK.1)) hxK)
  · calc u⁻¹ * g * t = u⁻¹ * (g * t * g⁻¹) * g := by group
      _ = u⁻¹ * (u * t * u⁻¹) * g := by rw [hut]
      _ = t * (u⁻¹ * g) := by group
  · have e1 : (u⁻¹ * g)⁻¹ * x = x⁻¹ * (k * e⁻¹ * u) * x⁻¹⁻¹ := by rw [hg]; group
    rw [e1]
    exact conj_mem_secKer (N.inv_mem hxN)
      (D.mul_mem (D.mul_mem hkDK.2 (D.inv_mem heM.1.2)) (hUD hu))

theorem exists_comm_lift_odd [Finite G] {N U R K : Subgroup G} {t : G}
    (hUK : U ≤ K) (hKN : K ≤ N) (hNU : N ≤ normalizer (U : Set G))
    (hNR : N ≤ normalizer (R : Set G)) (hNK : N ≤ normalizer (K : Set G))
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ R) (hsyl : IsSylowOf 2 U K) (ht : t ∈ N)
    (ht2 : t ^ 2 = 1)
    (hconj : ∀ g : G, g * t * g⁻¹ ∈ U ⊔ zpowers t → ∃ u ∈ U, g * t * g⁻¹ = u * t * u⁻¹)
    {x : G} (hxK : x ∈ K) (hxt : x * t * x⁻¹ * t⁻¹ ∈ secKer N U R hNU hNR) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m ∈ secKer N U R hNU hNR) :
    ∃ x' ∈ K, x' * t = t * x' ∧ Odd (orderOf x') ∧ x'⁻¹ * x ∈ secKer N U R hNU hNR := by
  set D := secKer N U R hNU hNR with hD
  obtain ⟨x₁, hx₁K, hx₁t, hx₁D⟩ :=
    exists_comm_lift hUK hKN hNU hNR hNK hcomm hsyl ht ht2 hconj hxK hxt
  have hxN : x ∈ N := hKN hxK
  have hx₁N : x₁ ∈ N := hKN hx₁K
  have hδ : x⁻¹ * x₁ ∈ D := by
    have h := D.inv_mem hx₁D
    rwa [mul_inv_rev, inv_inv] at h
  have hpow : ∀ n : ℕ, (x ^ n)⁻¹ * x₁ ^ n ∈ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (x ^ (n + 1))⁻¹ * x₁ ^ (n + 1) =
          (x⁻¹ * ((x ^ n)⁻¹ * x₁ ^ n) * x⁻¹⁻¹) * (x⁻¹ * x₁) := by
        rw [pow_succ, pow_succ]; group
      rw [e]
      exact D.mul_mem (conj_mem_secKer (N.inv_mem hxN) ih) hδ
  have hx₁m : x₁ ^ m ∈ D := by
    have h := D.mul_mem hxm (hpow m)
    rwa [mul_inv_cancel_left] at h
  obtain ⟨g₂, g₀, hg, ⟨a, ha⟩, hodd, hg₂z, hg₀z⟩ := exists_two_mul_odd x₁
  have hg₂D : g₂ ∈ D := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg₂z
    have hcop : Nat.Coprime m (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
    have hbez := Nat.gcd_eq_gcd_ab m (2 ^ a)
    rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
    have h1 : (x₁ ^ j) ^ m ∈ D := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact D.zpow_mem hx₁m j
    have e1 : x₁ ^ j = (x₁ ^ j) ^ ((m : ℤ) * Nat.gcdA m (2 ^ a) +
        ((2 ^ a : ℕ) : ℤ) * Nat.gcdB m (2 ^ a)) := by
      rw [← hbez, zpow_one]
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ha, one_zpow, mul_one] at e1
    rw [e1]
    exact D.zpow_mem h1 _
  have hg₀ : g₀ = g₂⁻¹ * x₁ := by rw [hg]; group
  refine ⟨g₀, (zpowers_le.mpr hx₁K) hg₀z, ?_, hodd, ?_⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg₀z
    exact (Commute.zpow_left (show Commute x₁ t from hx₁t) i).eq
  · have e : g₀⁻¹ * x = (x₁⁻¹ * g₂ * x₁⁻¹⁻¹) * (x₁⁻¹ * x) := by rw [hg₀]; group
    rw [e]
    exact D.mul_mem (conj_mem_secKer (N.inv_mem hx₁N) hg₂D) hx₁D

end SixNineCount

end CFSG.SeitzReduction.RankOne
