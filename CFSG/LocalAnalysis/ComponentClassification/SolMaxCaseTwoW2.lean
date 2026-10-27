module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCaseTwoW1
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace CaseTwoW

variable {X : Type} [Group X]

@[expose] def baseSubgroup {m : ℕ} (hm : 13 ≤ m) : Subgroup (Perm (Fin m)) where
  carrier := {v | IsBase hm v ∧ v ∈ alternatingGroup (Fin m)}
  mul_mem' ha hb := ⟨ha.1.mul hb.1, mul_mem ha.2 hb.2⟩
  one_mem' := ⟨isBase_one, one_mem _⟩
  inv_mem' ha := ⟨ha.1.inv, inv_mem ha.2⟩

theorem mem_baseSubgroup {m : ℕ} {hm : 13 ≤ m} {v : Perm (Fin m)} :
    v ∈ baseSubgroup hm ↔ IsBase hm v ∧ v ∈ alternatingGroup (Fin m) := Iff.rfl

theorem card_baseSubgroup_le {m : ℕ} (hm : 13 ≤ m) : Nat.card (baseSubgroup hm) ≤ 8 :=
  card_le_eight_of_isBase _ fun _ hv => hv

structure Setup (H M : Subgroup X) {m : ℕ} (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m))
    (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)) (t w : X) : Prop where
  perm : IsPermAction θ ρ
  m13 : 13 ≤ m
  MH : M ≤ H
  HN : H ≤ normalizer (M : Set X)
  ker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)
  tH : t ∈ H
  t2 : t * t = 1
  t4 : (ρ ⟨t, HN tH⟩).support.card = 4
  fus : ∀ g : X, g * t * g⁻¹ ∈ H → g ∈ H
  syl : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ H
  wH : w ∈ H
  w2 : w * w = 1
  wσ : ρ ⟨w, HN wH⟩ = σ8 m13

variable {H M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} {t w : X}

namespace Setup

variable (S : Setup H M θ ρ t w)
include S

theorem ρ_mul {a b : X} (ha : a ∈ H) (hb : b ∈ H) :
    ρ ⟨a * b, S.HN (mul_mem ha hb)⟩ = ρ ⟨a, S.HN ha⟩ * ρ ⟨b, S.HN hb⟩ := by
  rw [← map_mul]
  rfl

theorem ρ_inv {a : X} (ha : a ∈ H) : ρ ⟨a⁻¹, S.HN (inv_mem ha)⟩ = (ρ ⟨a, S.HN ha⟩)⁻¹ := by
  rw [← map_inv]
  rfl

theorem ρ_pow {a : X} (ha : a ∈ H) (k : ℕ) :
    ρ ⟨a ^ k, S.HN (pow_mem ha k)⟩ = (ρ ⟨a, S.HN ha⟩) ^ k := by
  rw [← map_pow]
  rfl

theorem mem_of_conj_mem_of_four [Finite X] {x : X} (hxH : x ∈ H) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, S.HN hxH⟩).support.card = 4) {g : X} (hg : g⁻¹ * x * g ∈ H) : g ∈ H := by
  obtain ⟨c, hcH, hc⟩ := S.perm.exists_conj_of_four (by have := S.m13; omega) S.MH S.ker
    (S.HN S.tH) (S.HN hxH) S.tH hxH S.t2 hx2 S.t4 hx4
  have h1 : (g⁻¹ * c) * t * (g⁻¹ * c)⁻¹ ∈ H := by
    rw [show (g⁻¹ * c) * t * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * t * c⁻¹) * g by group, hc]
    exact hg
  have h2 := S.fus _ h1
  have h3 := H.mul_mem hcH (H.inv_mem h2)
  rwa [show c * (g⁻¹ * c)⁻¹ = g by group] at h3

theorem odd_index [Finite X] : ¬ 2 ∣ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := S.syl
  intro h
  exact P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hP))

theorem le_of_isPGroup [Finite X] {Y : Subgroup X} (hY : IsPGroup 2 Y) {x : X} (hxY : x ∈ Y)
    (hxH : x ∈ H) (hx2 : x * x = 1) (hx4 : (ρ ⟨x, S.HN hxH⟩).support.card = 4) : Y ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (g y : X), g • (QuotientGroup.mk y : X ⧸ H) = QuotientGroup.mk y ↔
      y⁻¹ * g * y ∈ H := fun g y => by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, ← H.inv_mem_iff]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨q, hq⟩ := hY.nonempty_fixed_point_of_prime_not_dvd_card (X ⧸ H) S.odd_index
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ u ∈ Y, y⁻¹ * u * y ∈ H := fun u hu => (key u y).mp (hq ⟨u, hu⟩)
  have hy : y ∈ H := by
    have h1 := S.mem_of_conj_mem_of_four hxH hx2 hx4 (g := y) (hfix x hxY)
    exact h1
  intro u hu
  have h1 := H.mul_mem (H.mul_mem hy (hfix u hu)) (H.inv_mem hy)
  rwa [show y * (y⁻¹ * u * y) * y⁻¹ = u by group] at h1

theorem eq_one_of_ρ_eq_one [Finite X] {y : X} (hyH : y ∈ H) (hy : ∃ k, y ^ 2 ^ k = 1)
    (h1 : ρ ⟨y, S.HN hyH⟩ = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hy
  have hodd := S.ker _ hyH (S.perm.mem_coreActionKernel _ h1)
  have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul, Nat.not_odd_iff_even])

theorem ρ_injOn [Finite X] {Y : Subgroup X} (hY : IsPGroup 2 Y) (hYH : Y ≤ H) {a b : X}
    (ha : a ∈ Y) (hb : b ∈ Y) (h : ρ ⟨a, S.HN (hYH ha)⟩ = ρ ⟨b, S.HN (hYH hb)⟩) : a = b := by
  have hmem : a⁻¹ * b ∈ Y := mul_mem (inv_mem ha) hb
  obtain ⟨k, hk⟩ := hY ⟨_, hmem⟩
  have h2 : (a⁻¹ * b) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : ρ ⟨a⁻¹ * b, S.HN (hYH hmem)⟩ = 1 := by
    rw [S.ρ_mul (inv_mem (hYH ha)) (hYH hb), S.ρ_inv (hYH ha), h, inv_mul_cancel]
  have := S.eq_one_of_ρ_eq_one (hYH hmem) ⟨k, h2⟩ h1
  exact inv_mul_eq_one.mp this

theorem exists_lift [Finite X] {b : Perm (Fin m)} (hbA : b ∈ alternatingGroup (Fin m))
    (hb : b * σ8 S.m13 = σ8 S.m13 * b) :
    ∃ (y : X) (hy : y ∈ M), y * w = w * y ∧ ρ ⟨y, le_normalizer hy⟩ = b := by
  have hb' : b * ρ ⟨w, S.HN S.wH⟩ = ρ ⟨w, S.HN S.wH⟩ * b := by rw [S.wσ]; exact hb
  exact S.perm.exists_lift_perm (by have := S.m13; omega) (S.HN S.wH) S.w2 hbA hb'

theorem exists_inv_lift [Finite X] {b : Perm (Fin m)} (hbA : b ∈ alternatingGroup (Fin m))
    (hb : b * σ8 S.m13 = σ8 S.m13 * b) (hb2 : b * b = 1) :
    ∃ (y : X) (hy : y ∈ H), y * w = w * y ∧ y * y = 1 ∧ ρ ⟨y, S.HN hy⟩ = b := by
  obtain ⟨y₀, hy₀M, hy₀w, hy₀⟩ := S.exists_lift hbA hb
  have hy₀H : y₀ ∈ H := S.MH hy₀M
  have hy₀' : ρ ⟨y₀, S.HN hy₀H⟩ = b := hy₀
  obtain ⟨k, -, hk2, hk⟩ := S.perm.exists_pow_involution S.HN S.ker hy₀H (by rw [hy₀']; exact hb2)
  exact ⟨y₀ ^ k, pow_mem hy₀H k, ((Commute.pow_left hy₀w k : Commute (y₀ ^ k) w)).eq, hk2,
    hk.trans hy₀'⟩

theorem exists_inv_lift_comm [Finite X] {b : Perm (Fin m)} (hbA : b ∈ alternatingGroup (Fin m))
    (hb : b * σ8 S.m13 = σ8 S.m13 * b) (hb2 : b * b = 1) {x : X} (hxH : x ∈ H)
    (hxw : x * w = w * x) (hx2 : x * x = 1) (hbx : b * ρ ⟨x, S.HN hxH⟩ = ρ ⟨x, S.HN hxH⟩ * b) :
    ∃ (y : X) (hy : y ∈ H), y * w = w * y ∧ y * x = x * y ∧ y * y = 1 ∧ ρ ⟨y, S.HN hy⟩ = b := by
  obtain ⟨y₀, hy₀M, hy₀w, hy₀⟩ := S.exists_lift hbA hb
  have hy₀H : y₀ ∈ H := S.MH hy₀M
  let A : Subgroup X := H ⊓ centralizer ({w} : Set X)
  have hAH : A ≤ H := inf_le_left
  have hxA : x ∈ A := ⟨hxH, mem_centralizer_singleton_iff.mpr hxw⟩
  have hy₀A : y₀ ∈ A := ⟨hy₀H, mem_centralizer_singleton_iff.mpr hy₀w⟩
  have hy₀' : ρ ⟨y₀, S.HN (hAH hy₀A)⟩ = b := hy₀
  obtain ⟨y₁, hy₁A, hy₁x, hy₁⟩ := S.perm.exists_commute_lift S.HN S.ker hAH hxA hx2 hy₀A
    (by rw [hy₀']; exact hbx)
  rw [hy₀'] at hy₁
  have hy₁w : y₁ * w = w * y₁ := mem_centralizer_singleton_iff.mp hy₁A.2
  obtain ⟨k, -, hk2, hk⟩ := S.perm.exists_pow_involution S.HN S.ker (hAH hy₁A)
    (by rw [hy₁]; exact hb2)
  exact ⟨y₁ ^ k, pow_mem (hAH hy₁A) k, (Commute.pow_left hy₁w k).eq,
    (Commute.pow_left hy₁x k).eq, hk2, hk.trans hy₁⟩

theorem exists_conj_lift [Finite X] {u v : X} (huH : u ∈ H) (hvH : v ∈ H) (huw : u * w = w * u)
    (hvw : v * w = w * v) (hu2 : u * u = 1) (hv2 : v * v = 1) {π : Perm (Fin m)}
    (hπA : π ∈ alternatingGroup (Fin m)) (hπ : π * σ8 S.m13 = σ8 S.m13 * π)
    (huv : π * ρ ⟨u, S.HN huH⟩ * π⁻¹ = ρ ⟨v, S.HN hvH⟩) :
    ∃ (c : X) (_ : c ∈ H), c * w = w * c ∧ c * u * c⁻¹ = v := by
  obtain ⟨c₀, hc₀M, hc₀w, hc₀⟩ := S.exists_lift hπA hπ
  have hc₀H : c₀ ∈ H := S.MH hc₀M
  have hc₀' : ρ ⟨c₀, S.HN hc₀H⟩ = π := hc₀
  have hu'H : c₀ * u * c₀⁻¹ ∈ H := mul_mem (mul_mem hc₀H huH) (inv_mem hc₀H)
  have hu'2 : c₀ * u * c₀⁻¹ * (c₀ * u * c₀⁻¹) = 1 := by
    calc c₀ * u * c₀⁻¹ * (c₀ * u * c₀⁻¹) = c₀ * (u * u) * c₀⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hρu' : ρ ⟨c₀ * u * c₀⁻¹, S.HN hu'H⟩ = ρ ⟨v, S.HN hvH⟩ := by
    rw [S.ρ_mul (mul_mem hc₀H huH) (inv_mem hc₀H), S.ρ_mul hc₀H huH, S.ρ_inv hc₀H, hc₀', huv]
  have hprodH : c₀ * u * c₀⁻¹ * v ∈ H := mul_mem hu'H hvH
  have hprod1 : ρ ⟨c₀ * u * c₀⁻¹ * v, S.HN hprodH⟩ = 1 := by
    rw [S.ρ_mul hu'H hvH, hρu', ← map_mul, show (⟨v, S.HN hvH⟩ : ↥(normalizer (M : Set X))) *
      ⟨v, S.HN hvH⟩ = 1 from Subtype.ext hv2, map_one]
  have hodd := S.ker _ hprodH (S.perm.mem_coreActionKernel _ hprod1)
  obtain ⟨k, hk⟩ := exists_conj_of_odd_mul hu'2 hv2 hodd
  have hc₀w' : Commute c₀ w := hc₀w
  have hu'w : Commute (c₀ * u * c₀⁻¹) w :=
    ((hc₀w'.mul_left (huw : Commute u w)).mul_left hc₀w'.inv_left).symm.symm
  have hpw : Commute ((c₀ * u * c₀⁻¹ * v) ^ k) w :=
    Commute.pow_left (hu'w.mul_left (hvw : Commute v w)) k
  refine ⟨(c₀ * u * c₀⁻¹ * v) ^ k * c₀, mul_mem (pow_mem hprodH k) hc₀H,
    (hpw.mul_left hc₀w').eq, ?_⟩
  calc (c₀ * u * c₀⁻¹ * v) ^ k * c₀ * u * ((c₀ * u * c₀⁻¹ * v) ^ k * c₀)⁻¹ =
      (c₀ * u * c₀⁻¹ * v) ^ k * (c₀ * u * c₀⁻¹) * ((c₀ * u * c₀⁻¹ * v) ^ k)⁻¹ := by group
    _ = v := hk

theorem ρ_commute_σ8 {g : X} (hgH : g ∈ H) (hgw : g * w = w * g) :
    ρ ⟨g, S.HN hgH⟩ * σ8 S.m13 = σ8 S.m13 * ρ ⟨g, S.HN hgH⟩ := by
  rw [← S.wσ, ← S.ρ_mul hgH S.wH, ← S.ρ_mul S.wH hgH]
  congr 1
  exact Subtype.ext hgw

theorem ρ_lt_iff {g : X} (hgH : g ∈ H) (hgw : g * w = w * g) (i : Fin m) :
    ((ρ ⟨g, S.HN hgH⟩ i : Fin m) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
  have hc := S.ρ_commute_σ8 hgH hgw
  have hcomm : ∀ j, σ8 S.m13 (ρ ⟨g, S.HN hgH⟩ j) = ρ ⟨g, S.HN hgH⟩ (σ8 S.m13 j) := fun j => by
    rw [← Perm.mul_apply, ← hc, Perm.mul_apply]
  constructor
  · intro h
    by_contra hi
    push Not at hi
    have h1 := hcomm i
    rw [σ8_apply_of_ge S.m13 hi] at h1
    exact (σ8_apply_of_lt S.m13 h).1 h1
  · intro h
    by_contra hj
    push Not at hj
    have h1 := hcomm i
    rw [σ8_apply_of_ge S.m13 hj] at h1
    exact (σ8_apply_of_lt S.m13 h).1 ((ρ ⟨g, S.HN hgH⟩).injective h1).symm

end Setup

@[expose] def wGroup (hm : 13 ≤ m) (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m))
    (T : Subgroup X) (hTN : T ≤ normalizer (M : Set X)) : Subgroup X where
  carrier := {u | ∃ hu : u ∈ T, ρ ⟨u, hTN hu⟩ ∈ baseSubgroup hm}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : ρ ⟨a * b, hTN (mul_mem ha hb)⟩ = ρ ⟨a, hTN ha⟩ * ρ ⟨b, hTN hb⟩ := by
      rw [← map_mul]; rfl
    rw [this]
    exact mul_mem ha' hb'
  one_mem' := ⟨one_mem _, by
    have : ρ ⟨1, hTN (one_mem _)⟩ = 1 := by rw [← map_one ρ]; rfl
    rw [this]
    exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have : ρ ⟨a⁻¹, hTN (inv_mem ha)⟩ = (ρ ⟨a, hTN ha⟩)⁻¹ := by rw [← map_inv]; rfl
    rw [this]
    exact inv_mem ha'

namespace Setup

variable (S : Setup H M θ ρ t w)
include S

variable {T : Subgroup X} (hT2 : IsPGroup 2 T) (hTH : T ≤ H) (hTw : ∀ u ∈ T, u * w = w * u)

theorem mem_wGroup {u : X} (huT : u ∈ T) (hu : ρ ⟨u, S.HN (hTH huT)⟩ ∈ baseSubgroup S.m13) :
    u ∈ wGroup S.m13 ρ T (hTH.trans S.HN) := ⟨huT, hu⟩

include hT2 in
theorem wGroup_four [Finite X] (hwT : w ∈ T) {u : X} (hu : u ∈ wGroup S.m13 ρ T (hTH.trans S.HN))
    (hu1 : u ≠ 1) (huw : u ≠ w) :
    u * u = 1 ∧ (ρ ⟨u, S.HN (hTH hu.1)⟩).support.card = 4 := by
  obtain ⟨huT, hub⟩ := hu
  have hb := (mem_baseSubgroup.mp hub)
  have huH := hTH huT
  have h2 : ∃ k, (u * u) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hT2 ⟨u * u, mul_mem huT huT⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨S.eq_one_of_ρ_eq_one (mul_mem huH huH) h2 ?_, ?_⟩
  · rw [S.ρ_mul huH huH]
    exact hb.1.mul_self
  · refine card_support_eq_four_of_isBase hb.1 hb.2 ?_ ?_
    · intro h1
      apply hu1
      obtain ⟨k, hk⟩ := hT2 ⟨u, huT⟩
      exact S.eq_one_of_ρ_eq_one huH ⟨k, by simpa using congrArg Subtype.val hk⟩ h1
    · intro h8
      apply huw
      refine S.ρ_injOn hT2 hTH huT hwT ?_
      rw [h8, ← S.wσ]

include hTw in
theorem conj_mem_wGroup {g u : X} (hgT : g ∈ T) (hu : u ∈ wGroup S.m13 ρ T (hTH.trans S.HN)) :
    g * u * g⁻¹ ∈ wGroup S.m13 ρ T (hTH.trans S.HN) := by
  obtain ⟨huT, hub⟩ := hu
  have hgH := hTH hgT
  have huH := hTH huT
  refine ⟨mul_mem (mul_mem hgT huT) (inv_mem hgT), ?_⟩
  rw [S.ρ_mul (mul_mem hgH huH) (inv_mem hgH), S.ρ_mul hgH huH, S.ρ_inv hgH]
  obtain ⟨hb, hbA⟩ := mem_baseSubgroup.mp hub
  exact ⟨isBase_conj (S.ρ_commute_σ8 hgH (hTw g hgT)) hb,
    (alternatingGroup.normal (α := Fin m)).conj_mem _ hbA _⟩

end Setup

@[expose] def coreSubgroup (H : Subgroup X) (w : X) : Subgroup X where
  carrier := {n | n * w = w * n ∧ ∀ c : X, c * w = w * c → c⁻¹ * n * c ∈ H}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun c hc => ?_⟩
    · calc a * b * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by group
    · rw [show c⁻¹ * (a * b) * c = (c⁻¹ * a * c) * (c⁻¹ * b * c) by group]
      exact mul_mem (ha' c hc) (hb' c hc)
  one_mem' := ⟨by group, fun c _ => by rw [mul_one, inv_mul_cancel]; exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun c hc => ?_⟩
    · calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [ha]
        _ = w * a⁻¹ := by group
    · rw [show c⁻¹ * a⁻¹ * c = (c⁻¹ * a * c)⁻¹ by group]
      exact inv_mem (ha' c hc)

theorem coreSubgroup_le {H : Subgroup X} {w : X} : coreSubgroup H w ≤ H := fun n hn => by
  have := hn.2 1 (by group)
  simpa using this

theorem conj_mem_coreSubgroup {H : Subgroup X} {w n c : X} (hn : n ∈ coreSubgroup H w)
    (hc : c * w = w * c) : c * n * c⁻¹ ∈ coreSubgroup H w := by
  have hcinv : c⁻¹ * w = w * c⁻¹ := by
    calc c⁻¹ * w = c⁻¹ * (w * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * w) * c⁻¹ := by rw [hc]
      _ = w * c⁻¹ := by group
  refine ⟨?_, fun d hd => ?_⟩
  · calc c * n * c⁻¹ * w = c * n * (c⁻¹ * w) := by group
      _ = c * n * (w * c⁻¹) := by rw [hcinv]
      _ = c * (n * w) * c⁻¹ := by group
      _ = c * (w * n) * c⁻¹ := by rw [hn.1]
      _ = (c * w) * n * c⁻¹ := by group
      _ = (w * c) * n * c⁻¹ := by rw [hc]
      _ = w * (c * n * c⁻¹) := by group
  · have hcd : (c⁻¹ * d) * w = w * (c⁻¹ * d) := by
      calc (c⁻¹ * d) * w = c⁻¹ * (d * w) := by group
        _ = c⁻¹ * (w * d) := by rw [hd]
        _ = (c⁻¹ * w) * d := by group
        _ = (w * c⁻¹) * d := by rw [hcinv]
        _ = w * (c⁻¹ * d) := by group
    have := hn.2 _ hcd
    rwa [show (c⁻¹ * d)⁻¹ * n * (c⁻¹ * d) = d⁻¹ * (c * n * c⁻¹) * d by group] at this

namespace Setup

variable (S : Setup H M θ ρ t w)
include S

theorem not_mem_coreSubgroup_of_four [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H)
    {x : X} (hxH : x ∈ H) (hx2 : x * x = 1) (hx4 : (ρ ⟨x, S.HN hxH⟩).support.card = 4) :
    x ∉ coreSubgroup H w := by
  intro hx
  obtain ⟨c₀, hc₀w, hc₀H⟩ := hc₀
  exact hc₀H (S.mem_of_conj_mem_of_four hxH hx2 hx4 (hx.2 c₀ hc₀w))

end Setup

abbrev Hi (m : ℕ) := {i : Fin m // 8 ≤ (i : ℕ)}

theorem five_le_card_Hi (hm : 13 ≤ m) : 5 ≤ Nat.card (Hi m) := by
  let f : Fin 5 → Hi m := fun k => ⟨⟨8 + k, by omega⟩, by simp⟩
  have hf : Function.Injective f := by
    intro a b h
    have := congrArg (fun x : Hi m => ((x : Fin m) : ℕ)) h
    simp only [f] at this
    exact Fin.ext (by omega)
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem ofSubtype_commute_σ8 (hm : 13 ≤ m) (β : Perm (Hi m)) :
    Perm.ofSubtype β * σ8 hm = σ8 hm * Perm.ofSubtype β := by
  refine Equiv.ext fun i => ?_
  simp only [Perm.mul_apply]
  by_cases hi : 8 ≤ (i : ℕ)
  · rw [σ8_apply_of_ge hm hi, Perm.ofSubtype_apply_of_mem β hi,
      σ8_apply_of_ge hm (β ⟨i, hi⟩).2]
  · push Not at hi
    have hσ := (σ8_apply_of_lt hm hi).2
    rw [Perm.ofSubtype_apply_of_not_mem β (by omega),
      Perm.ofSubtype_apply_of_not_mem β (by omega)]

theorem apply_eq_of_commute_alternating (hm : 13 ≤ m) {π : Perm (Fin m)}
    (hπ : ∀ i : Fin m, 8 ≤ (i : ℕ) → 8 ≤ ((π i : Fin m) : ℕ))
    (hc : ∀ β ∈ alternatingGroup (Hi m), π * Perm.ofSubtype β = Perm.ofSubtype β * π)
    {i : Fin m} (hi : 8 ≤ (i : ℕ)) : π i = i := by
  classical
  by_contra hne
  set a : Hi m := ⟨i, hi⟩
  set b : Hi m := ⟨π i, hπ i hi⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h).symm
  have hcard : 2 < ((Finset.univ : Finset (Hi m)).erase a |>.erase b).card := by
    have h5 := five_le_card_Hi hm
    rw [Nat.card_eq_fintype_card] at h5
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (((Finset.univ : Finset (Hi m)).erase a).erase b).card)
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk hl
  set γ : Perm (Hi m) := swap a k * swap k l with hγ
  have hγA : γ ∈ alternatingGroup (Hi m) := by
    rw [Perm.mem_alternatingGroup, hγ, Perm.sign_mul, Perm.sign_swap hk.2.symm,
      Perm.sign_swap hkl]
    decide
  have hγa : γ a = k := by
    rw [hγ, Perm.mul_apply, swap_apply_of_ne_of_ne hk.2.symm (Ne.symm hl.2), swap_apply_left]
  have hγb : γ b = b := by
    rw [hγ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hk.1) (Ne.symm hl.1),
      swap_apply_of_ne_of_ne hab.symm (Ne.symm hk.1)]
  have h1 := congrArg (fun f : Perm (Fin m) => f i) (hc γ hγA)
  simp only [Perm.mul_apply] at h1
  rw [Perm.ofSubtype_apply_of_mem γ hi] at h1
  have h2 : Perm.ofSubtype γ (π i) = π i := by
    rw [Perm.ofSubtype_apply_of_mem γ (hπ i hi)]
    exact congrArg Subtype.val hγb
  rw [h2] at h1
  have h3 : π (k : Fin m) = π i := by
    have : ((γ ⟨i, hi⟩ : Hi m) : Fin m) = k := congrArg Subtype.val hγa
    rw [this] at h1
    exact h1
  exact hk.2 (Subtype.ext (π.injective h3))

namespace Setup

variable (S : Setup H M θ ρ t w)
include S

theorem core_apply_of_ge [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H) {n : X}
    (hn : n ∈ coreSubgroup H w) {i : Fin m} (hi : 8 ≤ (i : ℕ)) :
    ρ ⟨n, S.HN (coreSubgroup_le hn)⟩ i = i := by
  classical
  have hnH : n ∈ H := coreSubgroup_le hn
  have hlift : ∀ β ∈ alternatingGroup (Hi m), ∃ (b : X) (hb : b ∈ H), b * w = w * b ∧
      ρ ⟨b, S.HN hb⟩ = Perm.ofSubtype β := by
    intro β hβ
    have hβA : Perm.ofSubtype β ∈ alternatingGroup (Fin m) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact hβ
    obtain ⟨b, hbM, hbw, hb⟩ := S.exists_lift hβA (ofSubtype_commute_σ8 S.m13 β)
    exact ⟨b, S.MH hbM, hbw, hb⟩
  let R : Subgroup (alternatingGroup (Hi m)) :=
    { carrier := {β | ∃ (ν : X) (hν : ν ∈ coreSubgroup H w),
        ρ ⟨ν, S.HN (coreSubgroup_le hν)⟩ = Perm.ofSubtype (β : Perm (Hi m))}
      mul_mem' := by
        rintro β γ ⟨ν, hν, hνβ⟩ ⟨μ, hμ, hμγ⟩
        refine ⟨ν * μ, mul_mem hν hμ, ?_⟩
        rw [S.ρ_mul (coreSubgroup_le hν) (coreSubgroup_le hμ), hνβ, hμγ, Subgroup.coe_mul,
          map_mul]
      one_mem' := ⟨1, one_mem _, by
        rw [Subgroup.coe_one, map_one, ← map_one ρ]
        rfl⟩
      inv_mem' := by
        rintro β ⟨ν, hν, hνβ⟩
        refine ⟨ν⁻¹, inv_mem hν, ?_⟩
        rw [S.ρ_inv (coreSubgroup_le hν), hνβ, Subgroup.coe_inv, map_inv] }
  have hRn : R.Normal := by
    refine ⟨fun β hβ γ => ?_⟩
    obtain ⟨ν, hν, hνβ⟩ := hβ
    obtain ⟨c, hcH, hcw, hc⟩ := hlift γ γ.2
    refine ⟨c * ν * c⁻¹, conj_mem_coreSubgroup hν hcw, ?_⟩
    rw [S.ρ_mul (mul_mem hcH (coreSubgroup_le hν)) (inv_mem hcH), S.ρ_mul hcH (coreSubgroup_le hν),
      S.ρ_inv hcH, hc, hνβ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_mul, map_inv]
  have : IsSimpleGroup (alternatingGroup (Hi m)) :=
    alternatingGroup.isSimpleGroup (five_le_card_Hi S.m13)
  have hπge : ∀ j : Fin m, 8 ≤ (j : ℕ) →
      8 ≤ ((ρ ⟨n, S.HN hnH⟩ j : Fin m) : ℕ) := fun j hj => by
    by_contra h
    push Not at h
    have := (S.ρ_lt_iff hnH hn.1 j).mp h
    omega
  have hπlt : ∀ j : Fin m, (j : ℕ) < 8 → ((ρ ⟨n, S.HN hnH⟩ j : Fin m) : ℕ) < 8 :=
    fun j hj => (S.ρ_lt_iff hnH hn.1 j).mpr hj
  rcases hRn.eq_bot_or_eq_top with hR | hR
  ·
    refine apply_eq_of_commute_alternating S.m13 hπge (fun β hβ => ?_) hi
    obtain ⟨b, hbH, hbw, hb⟩ := hlift β hβ
    set π := ρ ⟨n, S.HN hnH⟩ with hπ
    set κ := π * Perm.ofSubtype β * π⁻¹ * (Perm.ofSubtype β)⁻¹ with hκ
    have hν : n * b * n⁻¹ * b⁻¹ ∈ coreSubgroup H w := by
      have h1 := conj_mem_coreSubgroup (inv_mem hn) hbw
      rw [show n * b * n⁻¹ * b⁻¹ = n * (b * n⁻¹ * b⁻¹) by group]
      exact mul_mem hn h1
    have hρν : ρ ⟨n * b * n⁻¹ * b⁻¹, S.HN (coreSubgroup_le hν)⟩ = κ := by
      rw [S.ρ_mul (mul_mem (mul_mem hnH hbH) (inv_mem hnH)) (inv_mem hbH),
        S.ρ_mul (mul_mem hnH hbH) (inv_mem hnH), S.ρ_mul hnH hbH, S.ρ_inv hnH, S.ρ_inv hbH, hb]
    have hai : ∀ (f : Perm (Fin m)) (x : Fin m), f (f⁻¹ x) = x := fun f x => by
      rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    have hκlt : ∀ x : Fin m, (x : ℕ) < 8 → κ x = x := by
      intro x hx
      have h1 : (Perm.ofSubtype β)⁻¹ x = x := by
        rw [Perm.inv_eq_iff_eq, Perm.ofSubtype_apply_of_not_mem β (by omega)]
      have h2 : ((π⁻¹ x : Fin m) : ℕ) < 8 := by
        by_contra h
        push Not at h
        have := hπge _ h
        rw [hai] at this
        omega
      rw [hκ, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, h1,
        Perm.ofSubtype_apply_of_not_mem β (by omega), hai]
    have h₁ : ∀ x : Fin m, 8 ≤ ((κ x : Fin m) : ℕ) ↔ 8 ≤ (x : ℕ) := by
      intro x
      constructor
      · intro h
        by_contra hx
        push Not at hx
        rw [hκlt x hx] at h
        omega
      · intro h
        by_contra hx
        push Not at hx
        have := hκlt _ hx
        rw [κ.injective this] at hx
        omega
    have h₂ : ∀ x : Fin m, κ x ≠ x → 8 ≤ (x : ℕ) := fun x hx => by
      by_contra h
      push Not at h
      exact hx (hκlt x h)
    have hκsign : Perm.sign (κ.subtypePerm (p := fun x : Fin m => 8 ≤ (x : ℕ)) h₁) = 1 := by
      rw [← Perm.sign_ofSubtype, Perm.ofSubtype_subtypePerm h₁ h₂, hκ, Perm.sign_mul,
        Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, Perm.sign_inv,
        mul_right_comm (Perm.sign π), Int.units_mul_self, one_mul, Int.units_mul_self]
    have hmem : (⟨κ.subtypePerm (p := fun x : Fin m => 8 ≤ (x : ℕ)) h₁, hκsign⟩ :
        alternatingGroup (Hi m)) ∈ R :=
      ⟨_, hν, by rw [hρν]; exact (Perm.ofSubtype_subtypePerm h₁ h₂).symm⟩
    rw [hR, Subgroup.mem_bot] at hmem
    have hκ1 : κ = 1 := by
      have := congrArg (fun x : alternatingGroup (Hi m) => Perm.ofSubtype (x : Perm (Hi m))) hmem
      simp only [Subgroup.coe_one, map_one] at this
      rw [← Perm.ofSubtype_subtypePerm h₁ h₂]
      exact this
    rw [hκ] at hκ1
    have := congrArg (· * Perm.ofSubtype β) hκ1
    simp only [one_mul, inv_mul_cancel_right] at this
    calc π * Perm.ofSubtype β = π * Perm.ofSubtype β * π⁻¹ * π := by group
      _ = Perm.ofSubtype β * π := by rw [this]
  ·
    exfalso
    have hp₁ : ∀ x : Fin m, 8 ≤ ((p1 S.m13 x : Fin m) : ℕ) ↔ 8 ≤ (x : ℕ) := by
      intro x
      constructor
      · intro h
        by_contra hx
        push Not at hx
        rw [p1_apply_of_lt S.m13 hx] at h
        omega
      · intro h
        by_contra hx
        push Not at hx
        have := p1_apply_of_lt S.m13 hx
        rw [(p1 S.m13).injective this] at hx
        omega
    have hp₂ : ∀ x : Fin m, p1 S.m13 x ≠ x → 8 ≤ (x : ℕ) := fun x hx => by
      by_contra h
      push Not at h
      exact hx (p1_apply_of_lt S.m13 h)
    have hsign :
        Perm.sign ((p1 S.m13).subtypePerm (p := fun x : Fin m => 8 ≤ (x : ℕ)) hp₁) = 1 := by
      rw [← Perm.sign_ofSubtype, Perm.ofSubtype_subtypePerm hp₁ hp₂]
      exact Perm.mem_alternatingGroup.mp (p1_mem S.m13)
    have hmem : (⟨(p1 S.m13).subtypePerm (p := fun x : Fin m => 8 ≤ (x : ℕ)) hp₁, hsign⟩ :
        alternatingGroup (Hi m)) ∈ R := by
      rw [hR]
      exact mem_top _
    obtain ⟨ν, hν, hνp⟩ := hmem
    rw [Perm.ofSubtype_subtypePerm hp₁ hp₂] at hνp
    have hνH := coreSubgroup_le hν
    obtain ⟨k, -, hk2, hk⟩ := S.perm.exists_pow_involution S.HN S.ker hνH
      (by rw [hνp]; exact p1_mul_self S.m13)
    refine S.not_mem_coreSubgroup_of_four hc₀ (pow_mem hνH k) hk2 ?_ (pow_mem hν k)
    rw [hk, hνp]
    exact card_support_p1 S.m13

end Setup

end CaseTwoW

end CFSG.ComponentClassification.SolMax
