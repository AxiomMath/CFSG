module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Two

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

structure IsHyp212 {H : Type} [Group H] (P : Subgroup H) : Prop where
  sq_eq_one : ∀ x ∈ P, x ^ 2 = 1
  four_le : 4 ≤ Nat.card P
  eq_one_of_mem_center : ∀ x ∈ P, x ∈ center H → x = 1
  conj_mem : ∀ x ∈ P, x ≠ 1 → ∀ a : H, a * x = x * a → ∀ y ∈ P, a * y * a⁻¹ ∈ P

@[expose] def Exc213 (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H → Even (Nat.card (center H)) →
    CFSG.Blueprint.LieModel (H ⧸ center H) τ n 2 1 → ∀ P : Subgroup H, ¬ IsHyp212 P

theorem IsHyp212.exists_pair {H : Type} [Group H] {P : Subgroup H} (hP : IsHyp212 P) :
    ∃ u ∈ P, ∃ v ∈ P, u ≠ 1 ∧ v ≠ 1 ∧ v ≠ u ∧ u * v = v * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : P ≠ ⊥ := by
    intro h
    have h4 := hP.four_le
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hlt : zpowers u < P := by
    refine lt_of_le_of_ne (zpowers_le.mpr hu) fun h => ?_
    have hc : Nat.card (zpowers u) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hP.sq_eq_one u hu) hu1'
    have h4 := hP.four_le
    rw [← h, hc] at h4
    omega
  obtain ⟨v, hv, hvu⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨u, hu, v, hv, hu1', fun h => hvu (h ▸ one_mem _), fun h => hvu (h ▸ mem_zpowers u), ?_⟩
  have h1 := hP.sq_eq_one _ (mul_mem hu hv)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hP.sq_eq_one u hu)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hP.sq_eq_one v hv)
  calc u * v = (u * v)⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← sq, h1]
    _ = v * u := by rw [mul_inv_rev, hui, hvi]

namespace Hyp221

variable {G : Type} [Group G] {A T : Subgroup G} (hH : Hyp221 A T)
include hH

theorem sq_mem_of_mem_sup {x : G} (hx : x ∈ T ⊔ A) : x ^ 2 ∈ A := by
  rw [sup_comm] at hx
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH.le_normalizer hx
  have hta : t * a * t⁻¹ ∈ A := (mem_normalizer_iff.mp (hH.le_normalizer ht) a).mp ha
  have h : (a * t) ^ 2 = a * (t * a * t⁻¹) * t ^ 2 := by rw [sq, sq]; group
  rw [h, hH.sq_eq_one ht, mul_one]
  exact mul_mem ha hta

theorem commutator_mem_of_mem_sup {x y : G} (hx : x ∈ T ⊔ A) (hy : y ∈ T ⊔ A) :
    x * y * x⁻¹ * y⁻¹ ∈ A := by
  rw [sup_comm] at hx hy
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH.le_normalizer hx
  obtain ⟨b, hb, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH.le_normalizer hy
  have htb : t * b * t⁻¹ ∈ A := (mem_normalizer_iff.mp (hH.le_normalizer ht) b).mp hb
  have hsa : s * a⁻¹ * s⁻¹ ∈ A :=
    (mem_normalizer_iff.mp (hH.le_normalizer hs) a⁻¹).mp (inv_mem ha)
  have h : a * t * (b * s) * (a * t)⁻¹ * (b * s)⁻¹ =
      a * (t * b * t⁻¹) * (t * s * t⁻¹ * a⁻¹ * s⁻¹) * b⁻¹ := by group
  rw [h, hH.commute ht hs, show s * t * t⁻¹ * a⁻¹ * s⁻¹ = s * a⁻¹ * s⁻¹ by group]
  exact mul_mem (mul_mem (mul_mem ha htb) hsa) (inv_mem hb)

theorem commute_of_mem_center {z : G} (hzA : z ∈ A) (hzC : z ∈ centralizer (A : Set G))
    {x : G} (hx : x ∈ T ⊔ A) : z * x = x * z := by
  rw [sup_comm] at hx
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH.le_normalizer hx
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (A : Set G)) (hH.le_sup ht)
  have h1 : Commute z a := ((mem_centralizer_iff.mp hzC) a ha).symm
  have h2 : Commute z b := ((mem_centralizer_iff.mp hzC) b hb).symm
  have h3 : Commute z c := (mem_centralizer_iff.mp hc) z hzA
  exact (h1.mul_right (h2.mul_right h3)).eq

variable [Finite G]

theorem exists_sq_eq_one_mul {x : G} (hxX : x ∈ T ⊔ A) (hxC : x ∈ centralizer (A : Set G)) :
    ∃ w ∈ A, w ∈ centralizer (A : Set G) ∧ (x * w) ^ 2 = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  obtain ⟨j, rfl⟩ := hm
  have hx2A := hH.sq_mem_of_mem_sup hxX
  have hx2C : x ^ 2 ∈ centralizer (A : Set G) := pow_mem hxC 2
  have hxm : x ^ (2 * j + 1) = x * (x ^ 2) ^ j := by
    rw [← pow_mul, pow_succ, (Commute.self_pow x (2 * j)).eq]
  have h2 : (x ^ (2 * j + 1)) ^ 2 = 1 := by
    refine hH.centralizer_two _ (mem_inf.mpr ⟨pow_mem hxX _, pow_mem hxC _⟩) ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  exact ⟨(x ^ 2) ^ j, pow_mem hx2A j, pow_mem hx2C j, by rw [← hxm]; exact h2⟩

omit [Finite G] in
theorem commute_of_sq_eq_one {c d : G} (hcX : c ∈ T ⊔ A) (hcC : c ∈ centralizer (A : Set G))
    (hdX : d ∈ T ⊔ A) (hdC : d ∈ centralizer (A : Set G)) (hc2 : c ^ 2 = 1) (hd2 : d ^ 2 = 1) :
    c * d = d * c := by
  have hcc : c * c = 1 := by rw [← sq]; exact hc2
  have hdd : d * d = 1 := by rw [← sq]; exact hd2
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  set w := (c * d) ^ 2 with hw
  have hwc : w = c * d * c⁻¹ * d⁻¹ := by rw [hw, sq, hci, hdi]; group
  have hwA : w ∈ A := by rw [hwc]; exact hH.commutator_mem_of_mem_sup hcX hdX
  have hwC : w ∈ centralizer (A : Set G) := by rw [hw]; exact pow_mem (mul_mem hcC hdC) 2
  have hcw : c * w * c⁻¹ = w⁻¹ := by
    rw [hw, sq, mul_inv_rev, mul_inv_rev, hci, hdi,
      show c * (c * d * (c * d)) * c = c * c * (d * c * (d * c)) by group, hcc, one_mul]
  have hwc' : c * w = w * c := (hH.commute_of_mem_center hwA hwC hcX).symm
  have hww : w * w = 1 := by
    have h1 : w = w⁻¹ := by rw [← hcw, hwc', mul_inv_cancel_right]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel w
  have h4 : (c * d) ^ 2 ^ 2 = 1 := by rw [pow_succ, pow_one, pow_mul, ← hw, sq, hww]
  have h2 := hH.centralizer_two (c * d) (mem_inf.mpr ⟨mul_mem hcX hdX, mul_mem hcC hdC⟩) ⟨2, h4⟩
  calc c * d = (c * d)⁻¹ := by rw [← mul_eq_one_iff_eq_inv, ← sq, h2]
    _ = d * c := by rw [mul_inv_rev, hci, hdi]

theorem centralizer_commute {c d : G} (hcX : c ∈ T ⊔ A) (hcC : c ∈ centralizer (A : Set G))
    (hdX : d ∈ T ⊔ A) (hdC : d ∈ centralizer (A : Set G)) : c * d = d * c := by
  obtain ⟨u, huA, huC, hu⟩ := hH.exists_sq_eq_one_mul hcX hcC
  obtain ⟨v, hvA, hvC, hv⟩ := hH.exists_sq_eq_one_mul hdX hdC
  have h := hH.commute_of_sq_eq_one (mul_mem hcX (mem_sup_right huA)) (mul_mem hcC huC)
    (mul_mem hdX (mem_sup_right hvA)) (mul_mem hdC hvC) hu hv
  have hud : u * d = d * u := hH.commute_of_mem_center huA huC hdX
  have hvc : v * c = c * v := hH.commute_of_mem_center hvA hvC hcX
  have huv : u * v = v * u := hH.commute_of_mem_center huA huC (mem_sup_right hvA)
  calc c * d = c * u * (d * v) * (u * v)⁻¹ := by
        rw [show c * u * (d * v) = c * (u * d) * v by group, hud]; group
    _ = d * v * (c * u) * (u * v)⁻¹ := by rw [h]
    _ = d * c := by
        rw [show d * v * (c * u) = d * (v * c) * u by group, hvc, huv]; group

theorem exists_aPart_sq {t : G} (ht : t ∈ T) : ∃ p : G, IsAPart A t p ∧ p ^ 2 = 1 := by
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (A : Set G)) (hH.le_sup ht)
  have hcX : c ∈ T ⊔ A := by
    have h : c = a⁻¹ * (a * c) := by group
    rw [h]
    exact mul_mem (mem_sup_right (inv_mem ha)) (mem_sup_left ht)
  obtain ⟨w, hwA, hwC, hw⟩ := hH.exists_sq_eq_one_mul hcX hc
  have hac : Commute a c := (mem_centralizer_iff.mp hc) a ha
  have haw : Commute a w := (mem_centralizer_iff.mp hwC) a ha
  have hcw : Commute c w := ((mem_centralizer_iff.mp hc) w hwA).symm
  have ht2 : (a * c) ^ 2 = 1 := hH.sq_eq_one ht
  rw [hac.mul_pow] at ht2
  rw [hcw.mul_pow] at hw
  have ha2 : a ^ 2 = w ^ 2 := by
    rw [eq_inv_of_mul_eq_one_left ht2, eq_inv_of_mul_eq_one_left hw, inv_inv]
  have hp2 : (a * w⁻¹) ^ 2 = 1 := by rw [haw.inv_right.mul_pow, ha2, inv_pow, mul_inv_cancel]
  refine ⟨a * w⁻¹, ⟨mul_mem ha (inv_mem hwA), ⟨1, by rw [pow_one, hp2]⟩, ?_⟩, hp2⟩
  have h : (a * c)⁻¹ * (a * w⁻¹) = c⁻¹ * w⁻¹ := by group
  rw [h]
  exact mul_mem (inv_mem hc) (inv_mem hwC)

theorem commute_aPart_of {t s p q : G} (ht : t ∈ T) (hs : s ∈ T) (hp : IsAPart A t p)
    (hq : IsAPart A s q) : p * q = q * p := by
  have hcX : p⁻¹ * t ∈ T ⊔ A := mul_mem (mem_sup_right (inv_mem hp.1)) (mem_sup_left ht)
  have hdX : q⁻¹ * s ∈ T ⊔ A := mul_mem (mem_sup_right (inv_mem hq.1)) (mem_sup_left hs)
  have hcC : p⁻¹ * t ∈ centralizer (A : Set G) := by
    have h := inv_mem hp.2.2
    rwa [mul_inv_rev, inv_inv] at h
  have hdC : q⁻¹ * s ∈ centralizer (A : Set G) := by
    have h := inv_mem hq.2.2
    rwa [mul_inv_rev, inv_inv] at h
  have e := hH.mul_cParts ht hs hp hq
  rw [hH.centralizer_commute hdX hdC hcX hcC] at e
  exact mul_right_cancel e

theorem isAPart_mul_of {t s p q : G} (ht : t ∈ T) (hs : s ∈ T) (hp : IsAPart A t p)
    (hq : IsAPart A s q) (hp2 : p ^ 2 = 1) (hq2 : q ^ 2 = 1) :
    IsAPart A (t * s) (p * q) ∧ (p * q) ^ 2 = 1 := by
  have hpq : Commute p q := hH.commute_aPart_of ht hs hp hq
  have h2 : (p * q) ^ 2 = 1 := by rw [hpq.mul_pow, hp2, hq2, one_mul]
  refine ⟨⟨mul_mem hp.1 hq.1, ⟨1, by rw [pow_one, h2]⟩, ?_⟩, h2⟩
  have hcq : q * (t⁻¹ * p) = t⁻¹ * p * q := (mem_centralizer_iff.mp hp.2.2) q hq.1
  have h : (t * s)⁻¹ * (p * q) = (s⁻¹ * q) * (t⁻¹ * p) := by
    calc (t * s)⁻¹ * (p * q) = s⁻¹ * (t⁻¹ * p * q) := by group
      _ = (s⁻¹ * q) * (t⁻¹ * p) := by rw [← hcq]; group
  rw [h]
  exact mul_mem hq.2.2 hp.2.2

theorem exists_hyp212 : ∃ P : Subgroup G, P ≤ A ∧ (∀ x ∈ P, x ^ 2 = 1) ∧ 4 ≤ Nat.card P ∧
    (∀ x ∈ P, x ∈ centralizer (A : Set G) → x = 1) ∧
    ∀ x ∈ P, x ≠ 1 → ∀ a ∈ A, a * x = x * a → ∀ y ∈ P, a * y * a⁻¹ ∈ P := by
  classical
  set S : Set (Subgroup G) := {P | P ≤ A ∧ T ⊓ A ≤ P ∧ ∀ x ∈ P, x ^ 2 = 1 ∧
    (x ∈ centralizer (A : Set G) → x = 1) ∧ ∃ t ∈ T, IsAPart A t x} with hS
  have h0 : T ⊓ A ∈ S := by
    refine ⟨inf_le_right, le_rfl, fun x hx => ?_⟩
    obtain ⟨hxT, hxA⟩ := mem_inf.mp hx
    exact ⟨hH.sq_eq_one hxT, hH.eq_one_of_mem_centralizer hxT, x, hxT, hxA,
      ⟨1, by rw [pow_one]; exact hH.sq_eq_one hxT⟩, by rw [inv_mul_cancel]; exact one_mem _⟩
  obtain ⟨P, ⟨hPA, hT0, hPx⟩, hmax⟩ := (Set.toFinite S).exists_maximal ⟨_, h0⟩
  have hall : ∀ t ∈ T, ∃ q ∈ P, IsAPart A t q := by
    intro t ht
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hp2⟩ := hH.exists_aPart_sq ht
    have hcomm : ∀ q ∈ P, q * p = p * q := fun q hq => by
      obtain ⟨-, -, s, hs, hqs⟩ := hPx q hq
      exact hH.commute_aPart_of hs ht hqs hp
    have hpr : ∀ r ∈ P, p * r * p⁻¹ = r := fun r hr => by
      rw [← hcomm r hr, mul_inv_cancel_right]
    have hpr' : ∀ r ∈ P, p⁻¹ * r * p = r := fun r hr => by
      rw [mul_assoc, hcomm r hr, inv_mul_cancel_left]
    have hpN : p ∈ normalizer (P : Set G) := mem_normalizer_iff.mpr fun q =>
      ⟨fun hq => by rw [hpr q hq]; exact hq, fun hq => by
        have h := hpr' _ hq
        rw [show p⁻¹ * (p * q * p⁻¹) * p = q by group] at h
        rw [h]
        exact hq⟩
    have hP'S : P ⊔ zpowers p ∈ S := by
      refine ⟨sup_le hPA (zpowers_le.mpr hp.1), le_trans hT0 le_sup_left, fun x hx => ?_⟩
      obtain ⟨q, hq, h, hh, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer (zpowers_le.mpr hpN) hx
      obtain ⟨hq2, hqC, s, hs, hqs⟩ := hPx q hq
      have hh' : h = 1 ∨ h = p := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
        have h2 : p ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hp2
        rw [zpow_eq_zpow_emod k h2]
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · left; rw [h0, zpow_zero]
        · right; rw [h1, zpow_one]
      rcases hh' with hh1 | hh1
      · rw [hh1, mul_one]
        exact ⟨hq2, hqC, s, hs, hqs⟩
      · rw [hh1]
        obtain ⟨hqp, hqp2⟩ := hH.isAPart_mul_of hs ht hqs hp hq2 hp2
        refine ⟨hqp2, fun hC => ?_, s * t, mul_mem hs ht, hqp⟩
        exfalso
        have hst : s * t ∈ centralizer (A : Set G) := by
          have e : s * t = (q * p) * ((s * t)⁻¹ * (q * p))⁻¹ := by group
          rw [e]
          exact mul_mem hC (inv_mem hqp.2.2)
        have hst1 := hH.eq_one_of_mem_centralizer (mul_mem hs ht) hst
        have hss : s * s = 1 := by rw [← sq]; exact hH.sq_eq_one hs
        have hts : t = s := by
          rw [eq_inv_of_mul_eq_one_right hst1, inv_eq_of_mul_eq_one_right hss]
        exact hno q hq (hts ▸ hqs)
    have hpP : p ∈ P := hmax hP'S le_sup_left (mem_sup_right (mem_zpowers p))
    exact hno p hpP hp
  choose f hfP hf using hall
  have hinj : Function.Injective (fun t : T => (⟨f t t.2, hfP t t.2⟩ : P)) := by
    intro t t' h
    have h' : f t t.2 = f t' t'.2 := congrArg Subtype.val h
    have h1 := (hf t t.2).2.2
    have h2 := (hf t' t'.2).2.2
    rw [h'] at h1
    have h3 : (t : G)⁻¹ * t' ∈ centralizer (A : Set G) := by
      have e : (t : G)⁻¹ * t' = ((t : G)⁻¹ * f t' t'.2) * ((t' : G)⁻¹ * f t' t'.2)⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem h2)
    have h4 := hH.eq_one_of_mem_centralizer (mul_mem (inv_mem t.2) t'.2) h3
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hcard : Nat.card T ≤ Nat.card P := Nat.card_le_card_of_injective _ hinj
  refine ⟨P, hPA, fun x hx => (hPx x hx).1, le_trans hH.four_le hcard,
    fun x hx => (hPx x hx).2.1, ?_⟩
  intro x hx hx1 a ha hax y hy
  obtain ⟨-, hxC, tx, htx, hxt⟩ := hPx x hx
  have htx1 : tx ≠ 1 := by
    rintro rfl
    apply hx1
    apply hxC
    have h := hxt.2.2
    rwa [inv_one, one_mul] at h
  have hat : a * tx = tx * a := (hxt.commute_iff ha).mpr hax
  have haN := hH.mem_normalizer_of_commute ha htx htx1 hat
  obtain ⟨-, -, ty, hty, hyt⟩ := hPx y hy
  have haty : a * ty * a⁻¹ ∈ T := (mem_normalizer_iff.mp haN ty).mp hty
  have hc : a * (ty⁻¹ * y) = ty⁻¹ * y * a := (mem_centralizer_iff.mp hyt.2.2) a ha
  have e : a * y * a⁻¹ = (a * ty * a⁻¹ * ty⁻¹) * y := by
    calc a * y * a⁻¹ = a * ty * a⁻¹ * (a * (ty⁻¹ * y)) * a⁻¹ := by group
      _ = (a * ty * a⁻¹ * ty⁻¹) * y := by rw [hc]; group
  have huT : a * ty * a⁻¹ * ty⁻¹ ∈ T := mul_mem haty (inv_mem hty)
  have huA : a * ty * a⁻¹ * ty⁻¹ ∈ A := by
    have e2 : a * ty * a⁻¹ * ty⁻¹ = a * y * a⁻¹ * y⁻¹ := by rw [e]; group
    rw [e2]
    have hyA := hPA hy
    exact mul_mem (mul_mem (mul_mem ha hyA) (inv_mem ha)) (inv_mem hyA)
  rw [e]
  exact mul_mem (hT0 (mem_inf.mpr ⟨huT, huA⟩)) hy

theorem exists_isHyp212 : ∃ P : Subgroup ↥A, IsHyp212 P := by
  obtain ⟨P, hPA, hP2, hP4, hPC, hPN⟩ := hH.exists_hyp212
  refine ⟨P.subgroupOf A, ⟨fun x hx => ?_, ?_, fun x hx hxZ => ?_, fun x hx hx1 a hax y hy => ?_⟩⟩
  · exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hP2 _ hx)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv]
    exact hP4
  · have h : (x : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun g hg =>
      congrArg Subtype.val ((mem_center_iff.mp hxZ) ⟨g, hg⟩)
    exact Subtype.ext (hPC _ hx h)
  · have h := hPN _ hx (fun h => hx1 (Subtype.ext h)) a a.2 (congrArg Subtype.val hax) _ hy
    rw [mem_subgroupOf]
    simpa using h

end Hyp221

theorem classical222TwoExcCenter_of (hU4 : Exc213 .PSU 4) (hU6 : Exc213 .PSU 6)
    (hSp : Exc213 .PSp 3) (hO : Exc213 .POmegaPlus 4) : Classical222TwoExcCenter := by
  intro G _ _ A T D hD H
  by_contra hodd
  have heven : Even (Nat.card (center ↥A)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨P, hP⟩ := H.exists_isHyp212
  have key : ∃ (τ : StatedLieTag) (n : ℕ), Exc213 τ n ∧
      CFSG.Blueprint.LieModel (↥A ⧸ center ↥A) τ n 2 1 := by
    cases D with
    | linear => simp [ClassicalModel.ExcTwo] at hD
    | orthMinus => simp [ClassicalModel.ExcTwo] at hD
    | unitary n m hn hm K hK e =>
      simp only [ClassicalModel.ExcTwo] at hD
      obtain ⟨hn46, rfl⟩ := hD
      rcases hn46 with rfl | rfl
      · exact ⟨.PSU, 4, hU4, Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩,
          K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
      · exact ⟨.PSU, 6, hU6, Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩,
          K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
    | symplectic n m hn hm hnm K hK e =>
      simp only [ClassicalModel.ExcTwo] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact ⟨.PSp, 3, hSp, Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩,
        K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
    | orthPlus n m hn hm K hK e =>
      simp only [ClassicalModel.ExcTwo] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact ⟨.POmegaPlus, 4, hO, Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, le_rfl⟩,
        K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
  obtain ⟨τ, n, hE, hL⟩ := key
  exact hE ↥A H.quasisimple heven hL P hP

end CFSG.ComponentClassification.RankTwoClassical
