module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Elem
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Compl
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearStageZero

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.ABGLocalTools
open scoped commutatorElement

namespace GMS28

variable {D : Type} [Group D]

theorem commutator_mem_of_sq_mem {W A : Subgroup D} (hWA : ∀ r ∈ W, ∀ a ∈ A, r * a = a * r)
    (hsq : ∀ x ∈ W, x * x ∈ A) {x z : D} (hx : x ∈ W) (hz : z ∈ W) :
    x * z * x⁻¹ * z⁻¹ ∈ A := by
  have e1 : x * z * x⁻¹ * z⁻¹ = (x * z * (x * z)) * (z⁻¹ * (x * x)⁻¹ * z) * (z * z)⁻¹ := by group
  have h1 : z⁻¹ * (x * x)⁻¹ * z = (x * x)⁻¹ := by
    rw [mul_assoc, ← hWA z hz _ (inv_mem (hsq x hx)), ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e1, h1]
  exact mul_mem (mul_mem (hsq _ (mul_mem hx hz)) (inv_mem (hsq x hx))) (inv_mem (hsq z hz))

theorem mem_normalizer_of_conj_mem_of_finite [Finite D] {H : Subgroup D} {g : D}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set D) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hg x hx
  exact map_conj_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj]))

theorem exists_mul_two_odd [Finite D] (g : D) :
    ∃ a ∈ zpowers g, ∃ b ∈ zpowers g, g = a * b ∧ (∃ k : ℕ, a ^ 2 ^ k = 1) ∧
      Odd (orderOf b) := by
  obtain ⟨k, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hb
  set α := Nat.gcdA (2 ^ k) m
  set β := Nat.gcdB (2 ^ k) m
  have hNz : ((orderOf g : ℕ) : ℤ) = (2 ^ k : ℕ) * (m : ℤ) := by rw [hN, Nat.cast_mul]
  have hone : g ^ ((orderOf g : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨g ^ ((m : ℤ) * β), zpow_mem (mem_zpowers g) _, g ^ (((2 ^ k : ℕ) : ℤ) * α),
    zpow_mem (mem_zpowers g) _, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm, ← hb, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have : (m : ℤ) * β * ((2 ^ k : ℕ) : ℤ) = ((orderOf g : ℕ) : ℤ) * β := by rw [hNz]; ring
    rw [this, zpow_mul, hone, one_zpow]
  · apply hm.of_dvd_nat
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : ((2 ^ k : ℕ) : ℤ) * α * (m : ℤ) = ((orderOf g : ℕ) : ℤ) * α := by rw [hNz]; ring
    rw [this, zpow_mul, hone, one_zpow]

variable {J R X U P V₁ : Subgroup D} {n : ℕ} {t y d : D}

namespace Setup

theorem conj_mul_inv_mem [Finite D] (hS : Setup J R X U P n t) {g v : D}
    (hg : g ∈ normalizer ((U ⊔ R : Subgroup D) : Set D)) (hv : v ∈ U ⊔ R) :
    g * v * g⁻¹ * v⁻¹ ∈ U := by
  have hgU := hS.normalizer_V_le hg
  have hw : g * v * g⁻¹ ∈ U ⊔ R := (mem_normalizer_iff.mp hg v).mp hv
  by_cases hvU : v ∈ U
  · exact mul_mem ((mem_normalizer_iff.mp hgU v).mp hvU) (inv_mem hvU)
  · have hwU : g * v * g⁻¹ ∉ U := fun h1 => hvU (by
      have := (mem_normalizer_iff.mp (inv_mem hgU) _).mp h1
      rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at this)
    have ha := (hS.mem_or_mul_mem hw).resolve_left hwU
    have hb := (hS.mem_or_mul_mem hv).resolve_left hvU
    have hvv : v⁻¹ = v :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact gms_sq_V hS.data v hv)
    rw [hvv]
    have e : g * v * g⁻¹ * v = (g * v * g⁻¹ * t) * (v * t) := by
      rw [hS.commute_V hv hS.t_mem_V,
        show g * v * g⁻¹ * t * (t * v) = g * v * g⁻¹ * (t * t) * v by group, hS.mul_self_t,
        mul_one]
    rw [e]
    exact mul_mem ha hb

theorem pow_conj_eq [Finite D] (hS : Setup J R X U P n t) {g : D}
    (hg : g ∈ X ⊓ normalizer (U : Set D)) :
    ∀ u ∈ U, g ^ (2 ^ n - 1) * u * (g ^ (2 ^ n - 1))⁻¹ = u := by
  obtain ⟨-, -, -, -, -, ⟨-, hcard, -⟩, -⟩ := hS.data
  have hact : gmsQuotConjAct X U (QuotientGroup.mk ⟨g, hg⟩) = gmsConjAct X U ⟨g, hg⟩ := rfl
  have hq : gmsConjAct X U ⟨g, hg⟩ ^ (2 ^ n - 1) = 1 := by
    have h1 : (QuotientGroup.mk ⟨g, hg⟩ : GMSNormalizerQuotient X U) ^ (2 ^ n - 1) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    rw [← hact, ← map_pow, h1, map_one]
  have hcoe : ∀ (j : ℕ) (u : U),
      (((gmsConjAct X U ⟨g, hg⟩ ^ j) u : U) : D) = g ^ j * u * (g ^ j)⁻¹ := by
    intro j u
    rw [← map_pow, SteinbergBT.gmsConjAct_coe_apply]
    simp
  intro u hu
  have h1 := congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : D)) hq
  simp only [hcoe, MulAut.one_apply] at h1
  exact h1

end Setup

namespace IsTorus

theorem pow_conj_U (hT : IsTorus U R V₁ t y d) (k : ℕ) :
    ∀ u ∈ U, d ^ k * u * (d ^ k)⁻¹ = y ^ k * u * (y ^ k)⁻¹ := by
  induction k with
  | zero => intro u _; simp
  | succ k ih =>
    intro u hu
    have hku : y ^ k * u * (y ^ k)⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (pow_mem hT.mem_normalizer_U k) u).mp hu
    calc d ^ (k + 1) * u * (d ^ (k + 1))⁻¹ = d * (d ^ k * u * (d ^ k)⁻¹) * d⁻¹ := by group
      _ = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by rw [ih u hu, hT.conj_eq _ (mem_sup_left hku)]
      _ = y ^ (k + 1) * u * (y ^ (k + 1))⁻¹ := by group

theorem eq_one_of_conj_eq [Finite D] (hT : IsTorus U R V₁ t y d) (hS : Setup J R X U P n t)
    {u : D} (hu : u ∈ U) (hyu : y * u * y⁻¹ = u) : u = 1 := by
  by_contra hu1
  have hpow : ∀ k : ℕ, y ^ k * u * (y ^ k)⁻¹ = u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * u * (y ^ (k + 1))⁻¹ = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = u := by rw [ih, hyu]
  have hle : U ≤ zpowers u := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact one_mem _
    · obtain ⟨k, hk⟩ := hT.trans u hu b hb hu1 hb1
      rw [← hk, hpow]
      exact mem_zpowers u
  have hcard := card_le_of_le hle
  rw [Nat.card_zpowers] at hcard
  have hord : orderOf u ≤ 2 :=
    orderOf_le_of_pow_eq_one (by norm_num) (gms_sq_V hS.data u (mem_sup_left hu))
  obtain ⟨hn3, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := hS.data
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  omega

theorem exists_conj_mul_eq [Finite D] (hT : IsTorus U R V₁ t y d) (hS : Setup J R X U P n t) :
    ∀ u ∈ U, ∃ a ∈ U, y * a * y⁻¹ * a = u := by
  let f : U → U := fun a =>
    ⟨y * a * y⁻¹ * a, mul_mem ((mem_normalizer_iff.mp hT.mem_normalizer_U a).mp a.2) a.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : y * (a : D) * y⁻¹ * a = y * b * y⁻¹ * b := congrArg Subtype.val hab
    have h2 : y * (a : D) * y⁻¹ = y * b * y⁻¹ * b * (a : D)⁻¹ := eq_mul_inv_of_mul_eq h1
    have hcU : (b : D)⁻¹ * a ∈ U := mul_mem (inv_mem b.2) a.2
    have ha : (a : D)⁻¹ = a := inv_eq_of_mul_eq_one_right (hS.mul_self_U a.2)
    have hb : (b : D)⁻¹ = b := inv_eq_of_mul_eq_one_right (hS.mul_self_U b.2)
    have hyc : y * ((b : D)⁻¹ * a) * y⁻¹ = (b : D)⁻¹ * a := by
      calc y * ((b : D)⁻¹ * a) * y⁻¹ = (y * b * y⁻¹)⁻¹ * (y * a * y⁻¹) := by group
        _ = (y * b * y⁻¹)⁻¹ * (y * b * y⁻¹ * b * (a : D)⁻¹) := by rw [h2]
        _ = (b : D) * (a : D)⁻¹ := by group
        _ = (b : D)⁻¹ * a := by rw [ha, hb]
    have h3 := hT.eq_one_of_conj_eq hS hcU hyc
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro u hu
  obtain ⟨a, ha⟩ := hsurj ⟨u, hu⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

end IsTorus

theorem IsV₁.exists_conj_eq_of_mem_centralizer [Finite D] (hV₁ : IsV₁ U R P V₁)
    (hS : Setup J R X U P n t) {m : D} (hmC : m ∈ centralizer ((U ⊔ R : Subgroup D) : Set D))
    (hmN : m ∈ normalizer (V₁ : Set D)) :
    ∃ v ∈ U ⊔ R, ∀ x ∈ V₁, m * x * m⁻¹ = v * x * v⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, b, hb, hab, ⟨k, hk⟩, hbodd⟩ := exists_mul_two_odd m
  have hzC : zpowers m ≤ centralizer ((U ⊔ R : Subgroup D) : Set D) := zpowers_le.mpr hmC
  have hzN : zpowers m ≤ normalizer (V₁ : Set D) := zpowers_le.mpr hmN
  have hCTr : centralizer ((U ⊔ R : Subgroup D) : Set D) ≤
      normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) := fun c hc =>
    mem_inf.mpr ⟨centralizer_le_normalizer _ hc,
      centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hc⟩
  have haV : a ∈ U ⊔ R := by
    have hap : IsPGroup 2 (zpowers a) := by
      have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hp := hV₁.isPGroup.to_sup_of_normal_left' hap (zpowers_le.mpr (hzN ha))
    have heq := hV₁.sylow.eq_of_le le_sup_left
      (sup_le hV₁.sylow.le (zpowers_le.mpr (hCTr (hzC ha)))) hp
    have haV₁ : a ∈ V₁ := heq ▸ mem_sup_right (mem_zpowers a)
    exact hV₁.mem_V_of_commute hS haV₁ (mem_centralizer_iff.mp (hzC ha) t hS.t_mem_V).symm
  have hbC := hzC hb
  have hbt : b * t = t * b := (mem_centralizer_iff.mp hbC t hS.t_mem_V).symm
  have hbR : ∀ x ∈ V₁, b * x * b⁻¹ = x := by
    intro x hx
    have hbx : b * x * b⁻¹ ∈ V₁ := (mem_normalizer_iff.mp (hzN hb) x).mp hx
    obtain ⟨z, hz⟩ : ∃ z, z = x⁻¹ * (b * x * b⁻¹) := ⟨_, rfl⟩
    have hzV₁ : z ∈ V₁ := hz ▸ mul_mem (inv_mem hx) hbx
    have hc := hS.comm_mem (hV₁.le_tr hx)
    have hcb : (b * x * b⁻¹) * t * (b * x * b⁻¹)⁻¹ * t = x * t * x⁻¹ * t := by
      have hbt' : b⁻¹ * t * b = t := by
        calc b⁻¹ * t * b = b⁻¹ * (t * b) := by group
          _ = t := by rw [← hbt]; group
      have e1 : (b * x * b⁻¹) * t * (b * x * b⁻¹)⁻¹ * t =
          b * (x * (b⁻¹ * t * b) * x⁻¹ * (b⁻¹ * t * b)) * b⁻¹ := by group
      rw [e1, hbt', ← mem_centralizer_iff.mp hbC _ (mem_sup_left hc), mul_inv_cancel_right]
    have hzV : z ∈ U ⊔ R := by
      rw [← hV₁.comm_eq_one_iff_mem hS hzV₁, hz,
        hS.comm_mul (hV₁.le_tr (inv_mem hx)) (hV₁.le_tr hbx), hV₁.comm_inv hS hx, hcb]
      exact hS.mul_self_U hc
    have hbz : b * z = z * b := (mem_centralizer_iff.mp hbC z hzV).symm
    have hzz : z * z = 1 := by rw [← sq]; exact gms_sq_V hS.data z hzV
    exact conj_eq_of_odd_of_eq_mul hbodd hbz hzz (by rw [hz]; group)
  refine ⟨a, haV, fun x hx => ?_⟩
  rw [hab]
  calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * x * a⁻¹ := by rw [hbR x hx]

theorem IsTorus.exists_conj_eq_of_mem_P [Finite D] (hT : IsTorus U R V₁ t y d)
    (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) (hyX : y ∈ X ⊓ normalizer (U : Set D))
    (hygen : ∀ g ∈ X ⊓ normalizer (U : Set D), ∃ k : ℕ,
      ∀ v ∈ U ⊔ R, g * v * g⁻¹ = y ^ k * v * (y ^ k)⁻¹)
    {w : D} (hw : w ∈ P) :
    ∃ k : ℕ, ∃ v ∈ U ⊔ R, ∀ x ∈ V₁,
      (w⁻¹ * d * w) * x * (w⁻¹ * d * w)⁻¹ = v * (d ^ k * x * (d ^ k)⁻¹) * v⁻¹ := by
  obtain ⟨-, -, -, -, -, -, ⟨hPN, -⟩⟩ := hS.data
  have hwV := hS.P_le_normalizer_V hw
  have hwR := hPN hw
  have hyV : y ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := gms_NXU_le_L hS.data hyX
  obtain ⟨-, -, hwY, -⟩ := gms_LR_normalizes hS.data (inv_mem hwV) (inv_mem hwR)
  have hwy : w⁻¹ * y * w ∈ X ⊓ normalizer (U : Set D) := by
    have := (mem_normalizer_iff.mp hwY y).mp hyX
    rwa [inv_inv] at this
  obtain ⟨k, hk⟩ := hygen _ hwy
  have hdpow : ∀ j : ℕ, ∀ v ∈ U ⊔ R, d ^ j * v * (d ^ j)⁻¹ = y ^ j * v * (y ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro v _; simp
    | succ j ih =>
      intro v hv
      have hjv : y ^ j * v * (y ^ j)⁻¹ ∈ U ⊔ R :=
        (mem_normalizer_iff.mp (pow_mem hyV j) v).mp hv
      calc d ^ (j + 1) * v * (d ^ (j + 1))⁻¹ = d * (d ^ j * v * (d ^ j)⁻¹) * d⁻¹ := by group
        _ = y * (y ^ j * v * (y ^ j)⁻¹) * y⁻¹ := by rw [ih v hv, hT.conj_eq _ hjv]
        _ = y ^ (j + 1) * v * (y ^ (j + 1))⁻¹ := by group
  obtain ⟨m, hm⟩ : ∃ m, m = (w⁻¹ * d * w) * (d ^ k)⁻¹ := ⟨_, rfl⟩
  have hmC : m ∈ centralizer ((U ⊔ R : Subgroup D) : Set D) := by
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : (d ^ k)⁻¹ * v * d ^ k ∈ U ⊔ R := by
      have := (mem_normalizer_iff.mp (inv_mem (pow_mem hT.mem_normalizer_V k)) v).mp hv
      simpa using this
    have hwv : w * ((d ^ k)⁻¹ * v * d ^ k) * w⁻¹ ∈ U ⊔ R := (mem_normalizer_iff.mp hwV _).mp hv'
    have h1 : m * v * m⁻¹ = v := by
      calc m * v * m⁻¹ = w⁻¹ * (d * (w * ((d ^ k)⁻¹ * v * d ^ k) * w⁻¹) * d⁻¹) * w := by
            rw [hm]; group
        _ = w⁻¹ * (y * (w * ((d ^ k)⁻¹ * v * d ^ k) * w⁻¹) * y⁻¹) * w := by
            rw [hT.conj_eq _ hwv]
        _ = (w⁻¹ * y * w) * ((d ^ k)⁻¹ * v * d ^ k) * (w⁻¹ * y * w)⁻¹ := by group
        _ = y ^ k * ((d ^ k)⁻¹ * v * d ^ k) * (y ^ k)⁻¹ := hk _ hv'
        _ = d ^ k * ((d ^ k)⁻¹ * v * d ^ k) * (d ^ k)⁻¹ := (hdpow k _ hv').symm
        _ = v := by group
    calc v * m = m * v * m⁻¹ * m := by rw [h1]
      _ = m * v := by group
  have hmN : m ∈ normalizer (V₁ : Set D) := by
    rw [hm]
    exact mul_mem (mul_mem (mul_mem (inv_mem (hV₁.le_normalizer hw)) hT.mem_normalizer)
      (hV₁.le_normalizer hw)) (inv_mem (pow_mem hT.mem_normalizer k))
  obtain ⟨v, hv, hvx⟩ := hV₁.exists_conj_eq_of_mem_centralizer hS hmC hmN
  refine ⟨k, v, hv, fun x hx => ?_⟩
  have hx' : d ^ k * x * (d ^ k)⁻¹ ∈ V₁ :=
    (mem_normalizer_iff.mp (pow_mem hT.mem_normalizer k) x).mp hx
  have e1 : w⁻¹ * d * w = m * d ^ k := by rw [hm]; group
  rw [e1, ← hvx _ hx']
  group

theorem IsV₁.exists_U₁ [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t) (hT : IsTorus U R V₁ t y d)
    (hyX : y ∈ X ⊓ normalizer (U : Set D)) (hsq : ∀ x ∈ V₁, x * x ∈ U) :
    ∃ U₁ : Subgroup D, U ≤ U₁ ∧ U₁ ≤ V₁ ∧ U₁ ⊓ (U ⊔ R) = U ∧ U₁ ⊔ R = V₁ ∧ U₁ ⊓ R = ⊥ ∧
      U₁ = ⁅zpowers d, V₁⁆ ∧ d ∈ normalizer (U₁ : Set D) ∧ V₁ ≤ normalizer (U₁ : Set D) ∧
      Nat.card U₁ = (2 ^ n) ^ 2 ∧
      (∀ u ∈ U₁, u * t * u⁻¹ * t ∈ U) ∧
      (∀ a ∈ U₁, ∀ b ∈ U₁,
        a * b * t * (a * b)⁻¹ * t = (a * t * a⁻¹ * t) * (b * t * b⁻¹ * t)) ∧
      (∀ u ∈ U₁, u * t * u⁻¹ * t = 1 ↔ u ∈ U) ∧
      (∀ u ∈ U, ∃ u₁ ∈ U₁, u₁ * t * u₁⁻¹ * t = u) ∧
      (∀ u ∈ U₁, (d * u * d⁻¹) * t * (d * u * d⁻¹)⁻¹ * t = d * (u * t * u⁻¹ * t) * d⁻¹) ∧
      (∀ u ∈ U₁, d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹ = u) ∧
      ∀ U' : Subgroup D, U ≤ U' → U' ≤ V₁ → U' ⊓ (U ⊔ R) = U →
        (∀ u ∈ U', d * u * d⁻¹ ∈ U') → U' ≤ U₁ := by
  have hdU : d ∈ normalizer (U : Set D) := hS.normalizer_V_le hT.mem_normalizer_V
  have hRA : ∀ r ∈ V₁, ∀ a ∈ U, r * a = a * r := fun r hr a ha => (hV₁.commute_U hr ha).symm
  have hcomm : ∀ x ∈ V₁, ∀ z ∈ V₁, x * z * x⁻¹ * z⁻¹ ∈ U := fun x hx z hz =>
    commutator_mem_of_sq_mem hRA hsq hx hz
  have hfix : ∀ x ∈ V₁, d * x * d⁻¹ * x⁻¹ ∈ U ↔ x ∈ U ⊔ R := by
    intro x hx
    constructor
    · intro ha
      by_contra hxV
      have hdx : d * x * d⁻¹ = (d * x * d⁻¹ * x⁻¹) * x := by group
      have hc := hS.comm_mem (hV₁.le_tr hx)
      have h1 : (d * x * d⁻¹) * t * (d * x * d⁻¹)⁻¹ * t = x * t * x⁻¹ * t := by
        rw [hdx, hS.comm_mul (hS.V_le_tr (mem_sup_left ha)) (hV₁.le_tr hx),
          hS.comm_eq_one_iff.mpr (hS.commute_t ha), one_mul]
      rw [hT.comm_conj hV₁ hS hx] at h1
      exact hxV ((hV₁.comm_eq_one_iff_mem hS hx).mp (hT.eq_one_of_conj_eq hS hc h1))
    · intro hxV
      exact hS.conj_mul_inv_mem hT.mem_normalizer_V hxV
  have hD : CFSG.ComponentClassification.GMS78.ComplData V₁ U (U ⊔ R) d :=
    { A_le := le_sup_left
      Z_le := hV₁.le
      normal := fun p hp a ha => by rw [hRA p hp a ha, mul_inv_cancel_right]; exact ha
      comm := hcomm
      sq := hsq
      normP := hT.mem_normalizer
      normA := hdU
      odd := hT.odd
      fix := hfix }
  obtain ⟨U₁, hAU, hUV₁, hUV, hfac, hUd, hmax⟩ := CFSG.ComponentClassification.GMS78.exists_compl hD
  have hdN : d ∈ normalizer (U₁ : Set D) := mem_normalizer_of_conj_mem_of_finite hUd
  have hV₁N : V₁ ≤ normalizer (U₁ : Set D) := fun x hx =>
    mem_normalizer_of_conj_mem_of_finite fun u hu => by
      have h1 := hcomm x hx u (hUV₁ hu)
      have e : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
      rw [e]
      exact mul_mem (hAU h1) hu
  have hR1 : U₁ ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxU : x ∈ U := by
      rw [← hUV]
      exact mem_inf.mpr ⟨(mem_inf.mp hx).1, mem_sup_right (mem_inf.mp hx).2⟩
    have h1 := mem_inf.mpr ⟨hxU, (mem_inf.mp hx).2⟩
    rwa [hS.inf_eq_bot] at h1
  have hsup : U₁ ⊔ R = V₁ := by
    refine le_antisymm (sup_le hUV₁ (le_sup_right.trans hV₁.le)) fun x hx => ?_
    obtain ⟨u, hu, z, hz, rfl⟩ := hfac x hx
    exact mul_mem (mem_sup_left hu) ((sup_le_sup_right hAU R) hz)
  have hcU₁ : ∀ u ∈ U₁, u * t * u⁻¹ * t ∈ U := fun u hu => hS.comm_mem (hV₁.le_tr (hUV₁ hu))
  have hcmul : ∀ a ∈ U₁, ∀ b ∈ U₁,
      a * b * t * (a * b)⁻¹ * t = (a * t * a⁻¹ * t) * (b * t * b⁻¹ * t) := fun a ha b hb =>
    hS.comm_mul (hV₁.le_tr (hUV₁ ha)) (hV₁.le_tr (hUV₁ hb))
  have hcker : ∀ u ∈ U₁, u * t * u⁻¹ * t = 1 ↔ u ∈ U := by
    intro u hu
    rw [hV₁.comm_eq_one_iff_mem hS (hUV₁ hu)]
    constructor
    · intro huV
      rw [← hUV]
      exact mem_inf.mpr ⟨hu, huV⟩
    · exact fun huU => mem_sup_left huU
  have hconto : ∀ u ∈ U, ∃ u₁ ∈ U₁, u₁ * t * u₁⁻¹ * t = u := by
    intro u hu
    obtain ⟨x, hx, hxt⟩ := htr u hu
    obtain ⟨u₁, hu₁, z, hz, rfl⟩ := hfac x hx
    refine ⟨u₁, hu₁, ?_⟩
    have h1 := hS.comm_mul (hV₁.le_tr (hUV₁ hu₁)) (hS.V_le_tr hz)
    rw [hS.comm_eq_one_iff.mpr (hS.commute_V hz hS.t_mem_V), mul_one] at h1
    rw [← h1, hxt, mul_assoc, hS.mul_self_t, mul_one]
  have hcd : ∀ u ∈ U₁,
      (d * u * d⁻¹) * t * (d * u * d⁻¹)⁻¹ * t = d * (u * t * u⁻¹ * t) * d⁻¹ := by
    intro u hu
    rw [hT.comm_conj hV₁ hS (hUV₁ hu), hT.conj_eq _ (mem_sup_left (hcU₁ u hu))]
  have hcard : Nat.card U₁ = (2 ^ n) ^ 2 := by
    obtain ⟨-, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := hS.data
    let φ : U₁ →* U :=
      { toFun := fun u => ⟨u * t * (u : D)⁻¹ * t, hcU₁ u u.2⟩
        map_one' := Subtype.ext (by simp [hS.mul_self_t])
        map_mul' := fun a b => Subtype.ext (hcmul a a.2 b b.2) }
    have hsurj : Function.Surjective φ := fun u => by
      obtain ⟨u₁, hu₁, h1⟩ := hconto u u.2
      exact ⟨⟨u₁, hu₁⟩, Subtype.ext h1⟩
    have hker : φ.ker = U.subgroupOf U₁ := by
      ext u
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro h1
        exact (hcker u u.2).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((hcker u u.2).mpr h1)
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, hker,
      Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv, hUcard] at h1
    rw [h1, sq]
  have hdU₁ : ∀ u ∈ U₁, ∀ j : ℤ, d ^ j * u * (d ^ j)⁻¹ ∈ U₁ := fun u hu j =>
    (mem_normalizer_iff.mp (zpow_mem hdN j) u).mp hu
  have hle : ⁅zpowers d, V₁⁆ ≤ U₁ := by
    rw [Subgroup.commutator_le]
    intro g hg x hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
    obtain ⟨u, hu, z, hz, rfl⟩ := hfac x hx
    have h1 := hS.conj_mul_inv_mem (zpow_mem hT.mem_normalizer_V j) hz
    rw [commutatorElement_def]
    have e : d ^ j * (u * z) * (d ^ j)⁻¹ * (u * z)⁻¹ =
        (d ^ j * u * (d ^ j)⁻¹) * (d ^ j * z * (d ^ j)⁻¹ * z⁻¹) * u⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hdU₁ u hu j) (hAU h1)) (inv_mem hu)
  have hmemC : ∀ x ∈ V₁, d * x * d⁻¹ * x⁻¹ ∈ ⁅zpowers d, V₁⁆ := fun x hx => by
    have := commutator_mem_commutator (mem_zpowers d) hx
    rwa [commutatorElement_def] at this
  have hUC : U ≤ ⁅zpowers d, V₁⁆ := by
    intro u hu
    obtain ⟨a, ha, hau⟩ := hT.exists_conj_mul_eq hS u hu
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hS.mul_self_U ha)
    have h2 : d * a * d⁻¹ * a⁻¹ = u := by
      rw [hT.conj_eq a (mem_sup_left ha), ha']
      exact hau
    rw [← h2]
    exact hmemC a (hV₁.le (mem_sup_left ha))
  have hge : U₁ ≤ ⁅zpowers d, V₁⁆ := by
    intro u₁ hu₁
    obtain ⟨a, ha, hau⟩ := hT.exists_conj_mul_eq hS _ (hcU₁ u₁ hu₁)
    obtain ⟨x, hx, hxt⟩ := htr a ha
    have hca : x * t * x⁻¹ * t = a := by rw [hxt, mul_assoc, hS.mul_self_t, mul_one]
    obtain ⟨x', hx'⟩ : ∃ x', x' = d * x * d⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hx'C : x' ∈ ⁅zpowers d, V₁⁆ := hx' ▸ hmemC x hx
    have hx'U₁ : x' ∈ U₁ := hle hx'C
    have hdx : d * x * d⁻¹ ∈ V₁ := (mem_normalizer_iff.mp hT.mem_normalizer x).mp hx
    have hcx' : x' * t * x'⁻¹ * t = u₁ * t * u₁⁻¹ * t := by
      rw [hx', hS.comm_mul (hV₁.le_tr hdx) (hV₁.le_tr (inv_mem hx)), hT.comm_conj hV₁ hS hx,
        hV₁.comm_inv hS hx, hca, hau]
    have hm : x'⁻¹ * u₁ ∈ U := by
      have hmem : x'⁻¹ * u₁ ∈ U₁ := mul_mem (inv_mem hx'U₁) hu₁
      rw [← hcker _ hmem, hS.comm_mul (hV₁.le_tr (hUV₁ (inv_mem hx'U₁))) (hV₁.le_tr (hUV₁ hu₁)),
        hV₁.comm_inv hS (hUV₁ hx'U₁), hcx']
      exact hS.mul_self_U (hcU₁ u₁ hu₁)
    have e : u₁ = x' * (x'⁻¹ * u₁) := by group
    rw [e]
    exact mul_mem hx'C (hUC hm)
  have hpowU : ∀ u ∈ U, d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹ = u := by
    intro u hu
    rw [hT.pow_conj_U _ u hu]
    exact hS.pow_conj_eq hyX u hu
  have hpow : ∀ u ∈ U₁, d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹ = u := by
    intro u hu
    have hgodd : Odd (orderOf (d ^ (2 ^ n - 1))) := hT.odd.of_dvd_nat (orderOf_pow_dvd _)
    have hgu : d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹ ∈ U₁ :=
      (mem_normalizer_iff.mp (pow_mem hdN _) u).mp hu
    have hc1 : (d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹) * t *
        (d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹)⁻¹ * t = u * t * u⁻¹ * t := by
      rw [hT.comm_conj_pow hV₁ hS _ (hUV₁ hu)]
      exact hS.pow_conj_eq hyX _ (hcU₁ u hu)
    obtain ⟨a, ha⟩ : ∃ a, a = u⁻¹ * (d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹) := ⟨_, rfl⟩
    have haU₁ : a ∈ U₁ := ha ▸ mul_mem (inv_mem hu) hgu
    have haU : a ∈ U := by
      rw [← hcker a haU₁, ha,
        hS.comm_mul (hV₁.le_tr (hUV₁ (inv_mem hu))) (hV₁.le_tr (hUV₁ hgu)),
        hV₁.comm_inv hS (hUV₁ hu), hc1]
      exact hS.mul_self_U (hcU₁ u hu)
    have hga : d ^ (2 ^ n - 1) * a = a * d ^ (2 ^ n - 1) := by
      have := hpowU a haU
      calc d ^ (2 ^ n - 1) * a = d ^ (2 ^ n - 1) * a * (d ^ (2 ^ n - 1))⁻¹ * d ^ (2 ^ n - 1) := by
            group
        _ = a * d ^ (2 ^ n - 1) := by rw [this]
    exact conj_eq_of_odd_of_eq_mul hgodd hga (hS.mul_self_U haU) (by rw [ha]; group)
  exact ⟨U₁, hAU, hUV₁, hUV, hsup, hR1, le_antisymm hge hle, hdN, hV₁N, hcard, hcU₁, hcmul,
    hcker, hconto, hcd, hpow, hmax⟩

theorem IsV₁.le_normalizer_U₁ [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (hT : IsTorus U R V₁ t y d) (hyX : y ∈ X ⊓ normalizer (U : Set D))
    (hygen : ∀ g ∈ X ⊓ normalizer (U : Set D), ∃ k : ℕ,
      ∀ v ∈ U ⊔ R, g * v * g⁻¹ = y ^ k * v * (y ^ k)⁻¹)
    {U₁ : Subgroup D} (hAU : U ≤ U₁) (hUV₁ : U₁ ≤ V₁) (hUV : U₁ ⊓ (U ⊔ R) = U)
    (hdN : d ∈ normalizer (U₁ : Set D)) (hV₁N : V₁ ≤ normalizer (U₁ : Set D))
    (hmax : ∀ U' : Subgroup D, U ≤ U' → U' ≤ V₁ → U' ⊓ (U ⊔ R) = U →
      (∀ u ∈ U', d * u * d⁻¹ ∈ U') → U' ≤ U₁) :
    P ≤ normalizer (U₁ : Set D) := by
  intro w hw
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, hPNU, -⟩⟩ := hS.data
  have hwU := hPNU hw
  have hwV := hS.P_le_normalizer_V hw
  have hwV₁ := hV₁.le_normalizer hw
  obtain ⟨k, v, hv, hvx⟩ := hT.exists_conj_eq_of_mem_P hV₁ hS hyX hygen hw
  obtain ⟨U', hU'⟩ : ∃ U' : Subgroup D, U' = U₁.map (MulAut.conj w).toMonoidHom := ⟨_, rfl⟩
  have hmemU' : ∀ x, x ∈ U' ↔ w⁻¹ * x * w ∈ U₁ := fun x => by rw [hU', mem_map_conj_iff]
  have hconjU : ∀ a ∈ U, w⁻¹ * a * w ∈ U := fun a ha => by
    have := (mem_normalizer_iff.mp (inv_mem hwU) a).mp ha
    rwa [inv_inv] at this
  have hAU' : U ≤ U' := fun a ha => (hmemU' a).mpr (hAU (hconjU a ha))
  have hU'V₁ : U' ≤ V₁ := fun x hx => by
    have h1 := (mem_normalizer_iff.mp hwV₁ _).mp (hUV₁ ((hmemU' x).mp hx))
    rwa [show w * (w⁻¹ * x * w) * w⁻¹ = x by group] at h1
  have hU'V : U' ⊓ (U ⊔ R) = U := by
    refine le_antisymm (fun x hx => ?_) (le_inf hAU' le_sup_left)
    obtain ⟨hxU', hxV⟩ := mem_inf.mp hx
    have h1 : w⁻¹ * x * w ∈ U := by
      rw [← hUV]
      refine mem_inf.mpr ⟨(hmemU' x).mp hxU', ?_⟩
      have := (mem_normalizer_iff.mp (inv_mem hwV) x).mp hxV
      rwa [inv_inv] at this
    have h2 := (mem_normalizer_iff.mp hwU _).mp h1
    rwa [show w * (w⁻¹ * x * w) * w⁻¹ = x by group] at h2
  have hU'd : ∀ u ∈ U', d * u * d⁻¹ ∈ U' := by
    intro u hu
    rw [hmemU'] at hu ⊢
    have hdk : d ^ k * (w⁻¹ * u * w) * (d ^ k)⁻¹ ∈ U₁ :=
      (mem_normalizer_iff.mp (pow_mem hdN k) _).mp hu
    have hvk := (mem_normalizer_iff.mp (hV₁N (hV₁.le hv)) _).mp hdk
    have e1 : w⁻¹ * (d * u * d⁻¹) * w = (w⁻¹ * d * w) * (w⁻¹ * u * w) * (w⁻¹ * d * w)⁻¹ := by
      group
    rw [e1, hvx _ (hUV₁ hu)]
    exact hvk
  have hle := hmax U' hAU' hU'V₁ hU'V hU'd
  refine mem_normalizer_of_conj_mem_of_finite fun u hu => hle ?_
  rw [hmemU', show w⁻¹ * (w * u * w⁻¹) * w = u by group]
  exact hu

structure Result (R X U P : Subgroup D) (n : ℕ) (t : D) (V₁ U₁ : Subgroup D) (y d : D) :
    Prop where
  sylow : IsSylowOf 2 V₁ (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
  le : U ⊔ R ≤ V₁
  le_normalizer : P ≤ normalizer (V₁ : Set D)
  sylow_sup : IsSylowOf 2 (V₁ ⊔ P) (normalizer ((U ⊔ R : Subgroup D) : Set D))
  mem : y ∈ X ⊓ normalizer (U : Set D)
  odd_y : Odd (orderOf y)
  gen : ∀ g ∈ X ⊓ normalizer (U : Set D), ∃ k : ℕ,
    ∀ v ∈ U ⊔ R, g * v * g⁻¹ = y ^ k * v * (y ^ k)⁻¹
  torus : IsTorus U R V₁ t y d
  sup_eq : U₁ ⊔ R = V₁
  inf_eq_bot : U₁ ⊓ R = ⊥
  eq_commutator : U₁ = ⁅zpowers d, V₁⁆
  U_le : U ≤ U₁
  comm_mem : ∀ u ∈ U₁, u * t * u⁻¹ * t ∈ U
  comm_mul : ∀ a ∈ U₁, ∀ b ∈ U₁,
    a * b * t * (a * b)⁻¹ * t = (a * t * a⁻¹ * t) * (b * t * b⁻¹ * t)
  comm_eq_one_iff : ∀ u ∈ U₁, u * t * u⁻¹ * t = 1 ↔ u ∈ U
  exists_comm_eq : ∀ u ∈ U, ∃ u₁ ∈ U₁, u₁ * t * u₁⁻¹ * t = u
  comm_conj : ∀ u ∈ U₁, (d * u * d⁻¹) * t * (d * u * d⁻¹)⁻¹ * t = d * (u * t * u⁻¹ * t) * d⁻¹
  le_V₁ : U₁ ≤ V₁
  inf_V : U₁ ⊓ (U ⊔ R) = U
  centralizer_eq : U₁ ⊓ centralizer ({t} : Set D) = U
  card : Nat.card U₁ = (2 ^ n) ^ 2
  sq_mem : ∀ x ∈ V₁, x * x ∈ U
  commute_U : ∀ x ∈ V₁, ∀ u ∈ U, x * u = u * x
  mem_normalizer_d : d ∈ normalizer (U₁ : Set D)
  le_normalizer_U₁ : V₁ ≤ normalizer (U₁ : Set D)
  pow_conj : ∀ u ∈ U₁, d ^ (2 ^ n - 1) * u * (d ^ (2 ^ n - 1))⁻¹ = u
  le_normalizer_P : P ≤ normalizer (U₁ : Set D)

end GMS28

theorem gms_normal_root_lemma28_card_two {D : Type} [Group D] [Finite D]
    {J R X U P : Subgroup D} {n : ℕ} (h : GMSNormalRootData J R X U P n) (hR2 : Nat.card R = 2)
    (hsc : ∀ T : Sylow 2 D, U ⊔ R ≤ T →
      ¬ IsStronglyClosedIn (T : Subgroup D) ((U ⊔ R : Subgroup D) : Set D))
    (E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)))
    (hEN : E ≤ (gmsRootConjugateAction (U ⊔ R) R).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal)
    (hreg : ∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
      (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z)
    {t : D} (htR : t ∈ R) (ht1 : t ≠ 1) :
    ∃ V₁ U₁ : Subgroup D, ∃ y d : D, GMS28.Result R X U P n t V₁ U₁ y d := by
  have hVP : U ⊔ R ≤ P := by
    obtain ⟨-, -, -, -, -, -, ⟨-, -, hUP, hRP, -, -, -, -⟩⟩ := h
    exact sup_le hUP hRP
  have hscP : (∃ T : Sylow 2 D, (T : Subgroup D) = P) →
      ¬ IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D) := by
    rintro ⟨T, rfl⟩
    exact hsc T hVP
  obtain ⟨-, -, -, -, hΔ, -⟩ := gms_normal_root_stage_zero h hR2 hscP
  have h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard := by
    rw [hΔ]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.1
  have hS : GMS28.Setup J R X U P n t := ⟨h, htR, ht1, hR2, h3⟩
  have htrTr := hS.exists_tr_conj_eq E hEN hEn hreg
  obtain ⟨V₁, hV₁⟩ := hS.exists_isV₁
  have htr := hV₁.exists_conj_eq hS htrTr
  obtain ⟨y, hyX, hyodd, hygen, d, hT⟩ := hV₁.exists_isTorus hS htr
  have hsq := hV₁.sq_mem hS htr hT hsc
  obtain ⟨U₁, hAU, hUV₁, hUV, hsup, hR1, hcomm, hdN, hV₁N, hcard, hcU₁, hcmul, hcker, hconto,
    hcd, hpow, hmax⟩ := hV₁.exists_U₁ hS htr hT hyX hsq
  have hPU₁ := hV₁.le_normalizer_U₁ hS hT hyX hygen hAU hUV₁ hUV hdN hV₁N hmax
  have hCt : U₁ ⊓ centralizer ({t} : Set D) = U := by
    ext u
    rw [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hu, hut⟩
      exact (hcker u hu).mp (hS.comm_eq_one_iff.mpr hut)
    · intro hu
      exact ⟨hAU hu, hS.commute_t hu⟩
  exact ⟨V₁, U₁, y, d, ⟨hV₁.sylow, hV₁.le, hV₁.le_normalizer, hV₁.isSylowOf_sup hS htr, hyX, hyodd,
    hygen, hT, hsup, hR1, hcomm, hAU, hcU₁, hcmul, hcker, hconto, hcd, hUV₁, hUV, hCt, hcard, hsq,
    fun x hx u hu => (hV₁.commute_U hx hu).symm, hdN, hV₁N, hpow, hPU₁⟩⟩

section Setting

open CFSG.Blueprint
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

variable {G : Type} [Group G] [Finite G]

theorem psl2_lemma28_of_card_sylow_eq_two (hGold : Goldschmidt1974) {L : Subgroup G}
    (h : SeitzSetting G L) {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {T : Subgroup G}
    (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G)))
    (E : Subgroup (Equiv.Perm (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t))))
    (hEN : E ≤ (gmsRootConjugateAction (T ⊓ L ⊔ zpowers t) (zpowers t)).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (T ⊓ L ⊔ zpowers t) (zpowers t)).range).Normal)
    (hreg : ∀ Q Z : gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t), ∃! a : E,
      (a : Equiv.Perm (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t))) Q = Z) :
    ∃ V₁ U₁ : Subgroup G, ∃ y d : G, GMS28.Result (zpowers t) L (T ⊓ L) T f t V₁ U₁ y d := by
  have hdata := gmsNormalRootData_of_psl2_of_card_sylow_eq_two h hf hL hS2 ht htC hTN hT
  have hR2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hsc : ∀ S : Sylow 2 G, T ⊓ L ⊔ zpowers t ≤ S →
      ¬ IsStronglyClosedIn (S : Subgroup G) ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) := by
    rintro S - ⟨hVS, hcl⟩
    have hVel := gms_isElementaryAbelian_V hdata
    have hV1 : T ⊓ L ⊔ zpowers t ≠ ⊥ := by
      intro hbot
      have htV : t ∈ T ⊓ L ⊔ zpowers t := mem_sup_right (mem_zpowers t)
      rw [hbot, mem_bot] at htV
      exact ht1 htV
    exact false_of_stronglyClosed_abelian_of_goldschmidt hGold h (Or.inl ⟨f, hf, hL⟩) S hVS
      hVel.toIsMulCommutative hV1 hcl
  exact gms_normal_root_lemma28_card_two hdata hR2 hsc E hEN hEn hreg (mem_zpowers t) ht1

end Setting

end CFSG.SeitzReduction.RankOne
