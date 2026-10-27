module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Facts
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G]

section Center

variable {A : Subgroup G}

theorem odd_orderOf_of_mem_center (hZ : Odd (Nat.card (center ↥A))) {x : G} (hxA : x ∈ A)
    (hxC : x ∈ centralizer (A : Set G)) : Odd (orderOf x) := by
  have hcen : (⟨x, hxA⟩ : ↥A) ∈ center ↥A := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hxC) g g.2)
  have h1 : orderOf (⟨⟨x, hxA⟩, hcen⟩ : center ↥A) ∣ Nat.card (center ↥A) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat hZ h1

theorem eq_one_of_mem_center_of_pow (hZ : Odd (Nat.card (center ↥A))) {x : G} (hxA : x ∈ A)
    (hxC : x ∈ centralizer (A : Set G)) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hodd := odd_orderOf_of_mem_center hZ hxA hxC
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk))

end Center

section APart

variable {A : Subgroup G}

theorem IsAPart.unique (hZ : Odd (Nat.card (center ↥A))) {t p p' : G}
    (hp : IsAPart A t p) (hp' : IsAPart A t p') : p = p' := by
  obtain ⟨hpA, ⟨k, hk⟩, hpC⟩ := hp
  obtain ⟨hpA', ⟨k', hk'⟩, hpC'⟩ := hp'
  set z := p⁻¹ * p' with hz
  have hzC : z ∈ centralizer (A : Set G) := by
    have h : z = (t⁻¹ * p)⁻¹ * (t⁻¹ * p') := by rw [hz]; group
    rw [h]
    exact mul_mem (inv_mem hpC) hpC'
  have hzA : z ∈ A := mul_mem (inv_mem hpA) hpA'
  have hpz : Commute p z := (mem_centralizer_iff.mp hzC) p hpA
  have hp'eq : p' = p * z := by rw [hz]; group
  have e1 : p ^ 2 ^ (k + k') = 1 := by rw [pow_add, pow_mul, hk, one_pow]
  have e2 : p' ^ 2 ^ (k + k') = 1 := by rw [add_comm, pow_add, pow_mul, hk', one_pow]
  rw [hp'eq, hpz.mul_pow, e1, one_mul] at e2
  rw [hp'eq, eq_one_of_mem_center_of_pow hZ hzA hzC e2, mul_one]

theorem IsAPart.conj {a t p : G} (ha : a ∈ A) (hp : IsAPart A t p) :
    IsAPart A (a * t * a⁻¹) (a * p * a⁻¹) := by
  obtain ⟨hpA, ⟨k, hk⟩, hpC⟩ := hp
  refine ⟨mul_mem (mul_mem ha hpA) (inv_mem ha), ⟨k, by rw [conj_pow, hk, mul_one,
    mul_inv_cancel]⟩, ?_⟩
  have h : a * (t⁻¹ * p) = t⁻¹ * p * a := (mem_centralizer_iff.mp hpC) a ha
  have h1 : (a * t * a⁻¹)⁻¹ * (a * p * a⁻¹) = a * (t⁻¹ * p) * a⁻¹ := by group
  rw [h1, h, mul_inv_cancel_right]
  exact hpC

theorem IsAPart.commute_iff {a t p : G} (ha : a ∈ A) (hp : IsAPart A t p) :
    a * t = t * a ↔ a * p = p * a := by
  have h : a * (t⁻¹ * p) = t⁻¹ * p * a := (mem_centralizer_iff.mp hp.2.2) a ha
  constructor
  · intro hat
    calc a * p = a * t * (t⁻¹ * p) := by group
      _ = t * (a * (t⁻¹ * p)) := by rw [hat, mul_assoc]
      _ = p * a := by rw [h]; group
  · intro hap
    have hc : Commute a (t⁻¹ * p) := h
    have e : t = p * (t⁻¹ * p)⁻¹ := by group
    calc a * t = a * (p * (t⁻¹ * p)⁻¹) := by rw [← e]
      _ = p * ((t⁻¹ * p)⁻¹ * a) := by rw [← mul_assoc, hap, mul_assoc, hc.inv_right.eq]
      _ = t * a := by rw [← mul_assoc, ← e]

end APart

namespace Hyp221

variable {A T : Subgroup G} (hH : Hyp221 A T)
include hH

theorem sq_eq_one {t : G} (ht : t ∈ T) : t ^ 2 = 1 := hH.elem.2 t ht

theorem commute {t s : G} (ht : t ∈ T) (hs : s ∈ T) : t * s = s * t :=
  congrArg Subtype.val (hH.elem.1.is_comm.comm ⟨t, ht⟩ ⟨s, hs⟩)

theorem eq_one_of_mem_centralizer {t : G} (ht : t ∈ T) (htC : t ∈ centralizer (A : Set G)) :
    t = 1 := by
  have h : t ∈ T ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨ht, htC⟩
  rw [hH.inf_eq_bot] at h
  exact h

theorem aPart_ne_one {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : IsAPart A t p) : p ≠ 1 := by
  rintro rfl
  apply ht1
  refine hH.eq_one_of_mem_centralizer ht ?_
  have h := inv_mem hp.2.2
  rwa [mul_one, inv_inv] at h

variable (hZ : Odd (Nat.card (center ↥A)))
include hZ

theorem exists_aPart {t : G} (ht : t ∈ T) : ∃ p : G, IsAPart A t p := by
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (A : Set G)) (hH.le_sup ht)
  have hac' : a * c = c * a := (mem_centralizer_iff.mp hc) a ha
  have hac : Commute a c := hac'
  have ha2C : a ^ 2 ∈ centralizer (A : Set G) := by
    have h : a ^ 2 * c ^ 2 = 1 := by rw [← hac.mul_pow]; exact hH.sq_eq_one ht
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem (pow_mem hc 2)
  obtain ⟨j, hj⟩ := odd_orderOf_of_mem_center hZ (pow_mem ha 2) ha2C
  have h1 : (a ^ 2) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
  have hc' : Commute a ((a ^ 2) ^ (j + 1))⁻¹ :=
    ((Commute.self_pow a 2).pow_right (j + 1)).inv_right
  refine ⟨a * ((a ^ 2) ^ (j + 1))⁻¹, mul_mem ha (inv_mem (pow_mem (pow_mem ha 2) _)),
    ⟨1, ?_⟩, ?_⟩
  · rw [pow_one, hc'.mul_pow, inv_pow, ← pow_mul, show (j + 1) * 2 = 2 * j + 1 + 1 by ring,
      pow_succ (a ^ 2) (2 * j + 1), h1, one_mul, mul_inv_cancel]
  · have h : (a * c)⁻¹ * (a * ((a ^ 2) ^ (j + 1))⁻¹) = c⁻¹ * ((a ^ 2) ^ (j + 1))⁻¹ := by group
    rw [h]
    exact mul_mem (inv_mem hc) (inv_mem (pow_mem ha2C _))

theorem aPart_sq {t p : G} (ht : t ∈ T) (hp : IsAPart A t p) : p ^ 2 = 1 := by
  obtain ⟨hpA, ⟨k, hk⟩, hpC⟩ := hp
  set c := t⁻¹ * p with hc
  have hpc : p * c = c * p := (mem_centralizer_iff.mp hpC) p hpA
  have htc : Commute t c := by
    have ht' : t = p * c⁻¹ := by rw [hc]; group
    show t * c = c * t
    rw [ht', mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc,
      show c * p = p * c from hpc.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hp2 : p ^ 2 = c ^ 2 := by
    rw [show p = t * c by rw [hc]; group, htc.mul_pow, hH.sq_eq_one ht, one_mul]
  refine eq_one_of_mem_center_of_pow hZ (pow_mem hpA 2) ?_ (k := k) ?_
  · rw [hp2]
    exact pow_mem hpC 2
  · rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]

theorem orderOf_aPart {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : IsAPart A t p) :
    orderOf p = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (hH.aPart_sq hZ ht hp) (hH.aPart_ne_one ht ht1 hp)

omit hZ in
theorem mul_cParts {t s p q : G} (ht : t ∈ T) (hs : s ∈ T) (hp : IsAPart A t p)
    (hq : IsAPart A s q) :
    p * q * ((p⁻¹ * t) * (q⁻¹ * s)) = q * p * ((q⁻¹ * s) * (p⁻¹ * t)) := by
  have hcC : p⁻¹ * t ∈ centralizer (A : Set G) := by
    have h := inv_mem hp.2.2
    rwa [mul_inv_rev, inv_inv] at h
  have hdC : q⁻¹ * s ∈ centralizer (A : Set G) := by
    have h := inv_mem hq.2.2
    rwa [mul_inv_rev, inv_inv] at h
  have hcq : q * (p⁻¹ * t) = p⁻¹ * t * q := (mem_centralizer_iff.mp hcC) q hq.1
  have hdp : p * (q⁻¹ * s) = q⁻¹ * s * p := (mem_centralizer_iff.mp hdC) p hp.1
  have e1 : t * s = p * q * ((p⁻¹ * t) * (q⁻¹ * s)) := by
    calc t * s = p * (p⁻¹ * t * q) * (q⁻¹ * s) := by group
      _ = p * q * ((p⁻¹ * t) * (q⁻¹ * s)) := by rw [← hcq]; group
  have e2 : s * t = q * p * ((q⁻¹ * s) * (p⁻¹ * t)) := by
    calc s * t = q * (q⁻¹ * s * p) * (p⁻¹ * t) := by group
      _ = q * p * ((q⁻¹ * s) * (p⁻¹ * t)) := by rw [← hdp]; group
  rw [← e1, ← e2, hH.commute ht hs]

theorem commute_aPart {t s p q : G} (ht : t ∈ T) (hs : s ∈ T) (hp : IsAPart A t p)
    (hq : IsAPart A s q) : p * q = q * p := by
  have hcC : p⁻¹ * t ∈ centralizer (A : Set G) := by
    have h := inv_mem hp.2.2
    rwa [mul_inv_rev, inv_inv] at h
  have hdC : q⁻¹ * s ∈ centralizer (A : Set G) := by
    have h := inv_mem hq.2.2
    rwa [mul_inv_rev, inv_inv] at h
  have hp2 : p * p = 1 := by rw [← sq]; exact hH.aPart_sq hZ ht hp
  have hq2 : q * q = 1 := by rw [← sq]; exact hH.aPart_sq hZ hs hq
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  set w := p * q with hw
  have hwC : w * w ∈ centralizer (A : Set G) := by
    have e := hH.mul_cParts ht hs hp hq
    have h1 : w * w = (q * p)⁻¹ * (p * q) := by rw [mul_inv_rev, hpinv, hqinv]
    have h2 : (q * p)⁻¹ * (p * q) =
        ((q⁻¹ * s) * (p⁻¹ * t)) * ((p⁻¹ * t) * (q⁻¹ * s))⁻¹ := by
      rw [show p * q = q * p * ((q⁻¹ * s) * (p⁻¹ * t)) * ((p⁻¹ * t) * (q⁻¹ * s))⁻¹ by
        rw [← e]; group]
      group
    rw [h1, h2]
    exact mul_mem (mul_mem hdC hcC) (inv_mem (mul_mem hcC hdC))
  have hwA : w * w ∈ A := mul_mem (mul_mem hp.1 hq.1) (mul_mem hp.1 hq.1)
  have hpw : p * w * p⁻¹ = w⁻¹ := by
    rw [hw, mul_inv_rev, hqinv, hpinv, ← mul_assoc, hp2, one_mul]
  have hpww : p * (w * w) * p⁻¹ = (w * w)⁻¹ := by
    calc p * (w * w) * p⁻¹ = (p * w * p⁻¹) * (p * w * p⁻¹) := by group
      _ = w⁻¹ * w⁻¹ := by rw [hpw]
      _ = (w * w)⁻¹ := by group
  have hcomm : p * (w * w) = w * w * p := (mem_centralizer_iff.mp hwC) p hp.1
  have hww : (w * w) ^ 2 ^ 1 = 1 := by
    have h : w * w = (w * w)⁻¹ := by rw [← hpww, hcomm, mul_inv_cancel_right]
    rw [pow_one, sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel _
  have hw1 := eq_one_of_mem_center_of_pow hZ hwA hwC hww
  have hwinv : w = w⁻¹ := by rw [← mul_eq_one_iff_eq_inv]; exact hw1
  rw [hwinv, hw, mul_inv_rev, hqinv, hpinv]

theorem commute_cPart {t s p q : G} (ht : t ∈ T) (hs : s ∈ T) (hp : IsAPart A t p)
    (hq : IsAPart A s q) : (p⁻¹ * t) * (q⁻¹ * s) = (q⁻¹ * s) * (p⁻¹ * t) := by
  have e := hH.mul_cParts ht hs hp hq
  rw [hH.commute_aPart hZ ht hs hp hq] at e
  exact mul_left_cancel e

theorem isAPart_mul {t s p q : G} (ht : t ∈ T) (hs : s ∈ T) (hp : IsAPart A t p)
    (hq : IsAPart A s q) : IsAPart A (t * s) (p * q) := by
  have hpq := hH.commute_aPart hZ ht hs hp hq
  refine ⟨mul_mem hp.1 hq.1, ⟨1, ?_⟩, ?_⟩
  · rw [pow_one, (show Commute p q from hpq).mul_pow, hH.aPart_sq hZ ht hp,
      hH.aPart_sq hZ hs hq, one_mul]
  · have hcq : q * (t⁻¹ * p) = t⁻¹ * p * q := (mem_centralizer_iff.mp hp.2.2) q hq.1
    have h : (t * s)⁻¹ * (p * q) = (s⁻¹ * q) * (t⁻¹ * p) := by
      calc (t * s)⁻¹ * (p * q) = s⁻¹ * (t⁻¹ * p * q) := by group
        _ = (s⁻¹ * q) * (t⁻¹ * p) := by rw [← hcq]; group
    rw [h]
    exact mul_mem hq.2.2 hp.2.2

theorem cPart_mem_centralizer {t p : G} (ht : t ∈ T) (hp : IsAPart A t p) :
    t⁻¹ * p ∈ centralizer (T : Set G) := by
  rw [mem_centralizer_iff]
  intro s hs
  obtain ⟨q, hq⟩ := hH.exists_aPart hZ hs
  have hcd := hH.commute_cPart hZ ht hs hp hq
  have hcq : q * (t⁻¹ * p) = t⁻¹ * p * q := (mem_centralizer_iff.mp hp.2.2) q hq.1
  have hts : t⁻¹ * p = (p⁻¹ * t)⁻¹ := by group
  have hs' : s = q * (q⁻¹ * s) := by group
  have hd : (q⁻¹ * s) * (t⁻¹ * p) = (t⁻¹ * p) * (q⁻¹ * s) := by
    have hc : Commute (p⁻¹ * t) (q⁻¹ * s) := hcd
    have h2 := hc.inv_left
    rw [← hts] at h2
    exact h2.eq.symm
  rw [hs']
  calc q * (q⁻¹ * s) * (t⁻¹ * p) = q * ((t⁻¹ * p) * (q⁻¹ * s)) := by rw [mul_assoc, hd]
    _ = t⁻¹ * p * (q * (q⁻¹ * s)) := by rw [← mul_assoc, hcq, mul_assoc]

omit hZ in
theorem mem_normalizer {x : G} (hx : x ∈ T ⊔ A) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hxt : x * t * x⁻¹ ∈ T) : x ∈ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact mem_normalizer_of_tightlyEmbedded_subgroupOf le_sup_left hH.tight hx ht hxt
    (orderOf_eq_prime (hH.sq_eq_one ht) ht1)

omit hZ in
theorem mem_normalizer_of_commute {a t : G} (ha : a ∈ A) (ht : t ∈ T) (ht1 : t ≠ 1)
    (hat : a * t = t * a) : a ∈ normalizer (T : Set G) :=
  hH.mem_normalizer (mem_sup_right ha) ht ht1 (by rw [hat, mul_inv_cancel_right]; exact ht)

end Hyp221

theorem mem_four_of_card {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsElemAbelian 2 T) (hT4 : Nat.card T = 4) {t u : G} (ht : t ∈ T) (hu : u ∈ T)
    (ht1 : t ≠ 1) (hu1 : u ≠ 1) (hut : u ≠ t) {v : G} (hv : v ∈ T) :
    v = 1 ∨ v = t ∨ v = u ∨ v = t * u := by
  classical
  have ht2 : t * t = 1 := by rw [← sq]; exact hT.2 t ht
  have htu1 : t * u ≠ 1 := by
    intro h
    apply hut
    calc u = t * (t * u) := by rw [← mul_assoc, ht2, one_mul]
      _ = t := by rw [h, mul_one]
  have htut : t * u ≠ t := fun h => hu1 (by simpa using h)
  have htuu : t * u ≠ u := fun h => ht1 (by simpa using h)
  let s : Finset G := {1, t, u, t * u}
  have hs : s.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair htuu.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hut.symm, htut.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ht1.symm, hu1.symm, htu1.symm⟩
  have hsub : (s : Set G) ⊆ (T : Set G) := by
    intro x hx
    simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem T
    · exact ht
    · exact hu
    · exact mul_mem ht hu
  have heq : (s : Set G) = (T : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hs, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hT4]
  have hv' : v ∈ (s : Set G) := heq ▸ hv
  simpa [s] using hv'

namespace Hyp221

variable [Finite G] {A T : Subgroup G} (hH : Hyp221 A T) (hZ : Odd (Nat.card (center ↥A)))
include hH hZ

theorem normalizer_cond_of (hNP : ∀ p ∈ A, orderOf p = 2 → NoPairOrbit A p) :
    ∀ x ∈ T ⊔ A, rightConjugate T x ⊓ normalizer (T : Set G) ≤ centralizer (T : Set G) := by
  rcases hH.normalizer_cond with hT4 | h
  swap
  · exact h
  intro x hx y hy
  obtain ⟨hyx, hyN⟩ := mem_inf.mp hy
  rw [mem_rightConjugate_iff] at hyx
  by_contra hyC
  have hyTA : y ∈ T ⊔ A := by
    have h : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [h]
    exact mul_mem (mul_mem (inv_mem hx) (mem_sup_left hyx)) hx
  obtain ⟨a, ha, τ, hτ, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH.le_normalizer
    (show y ∈ A ⊔ T by rw [sup_comm]; exact hyTA)
  have hy2 : (a * τ) * (a * τ) = 1 := by
    have h := hH.sq_eq_one hyx
    rw [sq, show x * (a * τ) * x⁻¹ * (x * (a * τ) * x⁻¹) = x * ((a * τ) * (a * τ)) * x⁻¹ by
      group, conj_eq_one_iff] at h
    exact h
  have hact : ∀ v ∈ T, (a * τ) * v * (a * τ)⁻¹ = a * v * a⁻¹ := by
    intro v hv
    have h := hH.commute hτ hv
    calc (a * τ) * v * (a * τ)⁻¹ = a * (τ * v) * τ⁻¹ * a⁻¹ := by group
      _ = a * v * a⁻¹ := by rw [h]; group
  have haN : a ∈ normalizer (T : Set G) := by
    have h : a = (a * τ) * τ⁻¹ := by group
    rw [h]
    exact mul_mem hyN (Subgroup.le_normalizer (inv_mem hτ))
  have hconj : ∀ v ∈ T, a * v * a⁻¹ ∈ T := fun v hv => (mem_normalizer_iff.mp haN v).mp hv
  have ha2 : ∀ v ∈ T, a * (a * v * a⁻¹) * a⁻¹ = v := by
    intro v hv
    rw [← hact _ (hconj v hv), ← hact v hv]
    calc (a * τ) * ((a * τ) * v * (a * τ)⁻¹) * (a * τ)⁻¹ =
        ((a * τ) * (a * τ)) * v * ((a * τ) * (a * τ))⁻¹ := by group
      _ = v := by rw [hy2]; group
  obtain ⟨s, hs, has⟩ : ∃ s ∈ T, a * s * a⁻¹ ≠ s := by
    by_contra hall
    push Not at hall
    apply hyC
    rw [mem_centralizer_iff]
    intro v hv
    have h := hall v hv
    rw [← hact v hv] at h
    calc v * (a * τ) = (a * τ) * v * (a * τ)⁻¹ * (a * τ) := by rw [h]
      _ = (a * τ) * v := by group
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact has (by group)
  set s' := a * s * a⁻¹ with hs'
  have hs'T : s' ∈ T := hconj s hs
  have hss : s * s = 1 := by rw [← sq]; exact hH.sq_eq_one hs
  set t₀ := s * s' with ht₀
  have ht₀T : t₀ ∈ T := mul_mem hs hs'T
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    apply has
    calc a * s * a⁻¹ = s' := rfl
      _ = s * (s * s') := by rw [← mul_assoc, hss, one_mul]
      _ = s := by rw [← ht₀, h, mul_one]
  have hat₀ : a * t₀ * a⁻¹ = t₀ := by
    calc a * t₀ * a⁻¹ = (a * s * a⁻¹) * (a * s' * a⁻¹) := by rw [ht₀]; group
      _ = s' * s := by rw [← hs', hs', ha2 s hs]
      _ = t₀ := by rw [ht₀, hH.commute hs'T hs]
  have has' : a * s * a⁻¹ = s * t₀ := by
    rw [ht₀, ← mul_assoc, hss, one_mul]
  have hst₀ : s ≠ t₀ := by
    intro h
    apply has
    rw [hs', h]
    exact hat₀
  obtain ⟨u, hu⟩ := hH.exists_aPart hZ hs
  obtain ⟨p₀, hp₀⟩ := hH.exists_aPart hZ ht₀T
  have hp₀2 := hH.orderOf_aPart hZ ht₀T ht₀1 hp₀
  have hp₀1 : p₀ ≠ 1 := hH.aPart_ne_one ht₀T ht₀1 hp₀
  have hup₀ : u * p₀ = p₀ * u := hH.commute_aPart hZ hs ht₀T hu hp₀
  have haup : a * u * a⁻¹ = u * p₀ := by
    have h1 := hu.conj ha
    rw [has'] at h1
    exact h1.unique hZ (hH.isAPart_mul hZ hs ht₀T hu hp₀)
  have hap₀ : a * p₀ = p₀ * a :=
    (hp₀.commute_iff ha).mp (by rw [← mul_inv_eq_iff_eq_mul.mp hat₀])
  have horb : ∀ b ∈ A ⊓ centralizer ({p₀} : Set G), b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * p₀ := by
    intro b hb
    obtain ⟨hbA, hbp⟩ := mem_inf.mp hb
    have hbt : b * t₀ = t₀ * b := (hp₀.commute_iff hbA).mpr (mem_centralizer_singleton_iff.mp hbp)
    have hbN := hH.mem_normalizer_of_commute hbA ht₀T ht₀1 hbt
    have hbs : b * s * b⁻¹ ∈ T := (mem_normalizer_iff.mp hbN s).mp hs
    have hbu := hu.conj hbA
    rcases mem_four_of_card hH.elem hT4 ht₀T hs ht₀1 hs1 hst₀ hbs with h | h | h | h
    · exact absurd (by rw [← conj_eq_one_iff (a := b), h]) hs1
    · exfalso
      apply hst₀
      have h1 : b * s * b⁻¹ = b * t₀ * b⁻¹ := by rw [h, hbt, mul_inv_cancel_right]
      calc s = b⁻¹ * (b * s * b⁻¹) * b := by group
        _ = b⁻¹ * (b * t₀ * b⁻¹) * b := by rw [h1]
        _ = t₀ := by group
    · left
      rw [h] at hbu
      exact hbu.unique hZ hu
    · right
      rw [h] at hbu
      rw [hbu.unique hZ (hH.isAPart_mul hZ ht₀T hs hp₀ hu), hup₀]
  have hfix := hNP p₀ hp₀.1 hp₀2 u (mem_inf.mpr ⟨hu.1, mem_centralizer_singleton_iff.mpr hup₀⟩)
    (hH.aPart_sq hZ hs hu) horb a (mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hap₀⟩)
  apply hp₀1
  have h := haup.symm.trans hfix
  calc p₀ = u⁻¹ * (u * p₀) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

end Hyp221

end CFSG.ComponentClassification.RankTwoClassical
