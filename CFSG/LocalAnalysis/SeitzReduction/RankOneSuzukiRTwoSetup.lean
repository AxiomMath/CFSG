module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Trans
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularCoords

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis SzPartition

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]

structure SzRSetup (T₁ R : Subgroup G) (t d : G) (a : ℕ) (u v : G → K) (κ : K) : Prop where
  coords : SzRootCoords T₁ a d u v κ
  one_le : 1 ≤ a
  card : Fintype.card K = 2 ^ (2 * a + 1)
  gen' : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w
  t_mem : t ∈ centralizer (T₁ : Set G)
  t_sq : t ^ 2 = 1
  t_not_mem : t ∉ T₁
  d_comm : d * t = t * d
  le_normalizer : R ≤ normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G)
  le_normalizer_T : R ≤ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G)
  le_normalizer_szA₁ : R ≤ normalizer (szA₁ T₁ : Set G)
  normalizer_le : normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) ≤
    normalizer (R : Set G)
  le : T₁ ⊔ zpowers t ≤ R
  isPGroup : IsPGroup 2 R
  inf_centralizer : R ⊓ centralizer ({t} : Set G) = T₁ ⊔ zpowers t
  rho_mem : ∀ x ∈ R, x * t * x⁻¹ * t⁻¹ ∈ szA₁ T₁
  exists_conj : ∀ b ∈ szA₁ T₁, ∃ r ∈ R, r * t * r⁻¹ = b * t
  mem_of_isPGroup : ∀ y ∈ normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G),
    IsPGroup 2 (R ⊔ zpowers y : Subgroup G) → y ∈ R

namespace SzRSetup

variable {T₁ R : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K}
  (h : SzRSetup T₁ R t d a u v κ)
include h

theorem t_mem_szA₁ : t ∈ centralizer (szA₁ T₁ : Set G) :=
  centralizer_le (szA₁_le T₁) h.t_mem

theorem d_mem_normalizer_T₁ : d ∈ normalizer (T₁ : Set G) :=
  mem_normalizer_of_forall_inv_mul_mul_mem h.coords.conj_mem

theorem d_mem_normalizer_szA₁ : d ∈ normalizer (szA₁ T₁ : Set G) :=
  mem_normalizer_of_forall_inv_mul_mul_mem fun _ hx => h.coords.conj_mem_szA₁ h.one_le h.card hx

theorem d_mem_normalizer_szA :
    d ∈ normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_normalizer_sup_zpowers h.t_mem_szA₁ h.d_mem_normalizer_szA₁ h.d_comm

theorem d_mem_normalizer_T : d ∈ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_normalizer_sup_zpowers h.t_mem h.d_mem_normalizer_T₁ h.d_comm

theorem d_mem_normalizer_R : d ∈ normalizer (R : Set G) :=
  h.normalizer_le h.d_mem_normalizer_szA

theorem szA_le_T : szA₁ T₁ ⊔ zpowers t ≤ T₁ ⊔ zpowers t :=
  sup_le_sup_right (szA₁_le T₁) _

theorem szA_le_R : szA₁ T₁ ⊔ zpowers t ≤ R := h.szA_le_T.trans h.le

theorem szA₁_le_R : szA₁ T₁ ≤ R := le_sup_left.trans h.szA_le_R

theorem sq_eq_one_of_mem_szA {w : G} (hw : w ∈ szA₁ T₁ ⊔ zpowers t) : w ^ 2 = 1 :=
  h.coords.sq_eq_one_of_mem_szA₁_sup h.one_le h.card h.t_mem h.t_sq hw

theorem commute_of_mem_szA {w z : G} (hw : w ∈ szA₁ T₁ ⊔ zpowers t) (hz : z ∈ T₁ ⊔ zpowers t) :
    z * w = w * z := by
  rw [← SzRootCoords.inf_centralizer_sup_eq h.t_mem] at hw
  exact mem_centralizer_iff.mp (mem_inf.mp hw).2 z hz

theorem commute_szA₁ {b b' : G} (hb : b ∈ szA₁ T₁) (hb' : b' ∈ szA₁ T₁) : b * b' = b' * b :=
  (mem_centralizer_iff.mp (mem_szA₁.mp hb).2 b' (szA₁_le T₁ hb')).symm

theorem sq_eq_one_of_mem_szA₁ {b : G} (hb : b ∈ szA₁ T₁) : b ^ 2 = 1 :=
  h.coords.sq_eq_one_of_mem_szA₁ h.one_le h.card hb

theorem sq_mem_szA₁_of_mem_T {z : G} (hz : z ∈ T₁ ⊔ zpowers t) : z ^ 2 ∈ szA₁ T₁ :=
  (h.coords.sq_mem_and_v_sq h.one_le h.card h.t_mem h.t_sq h.t_not_mem hz).1

theorem card_szA₁ : Nat.card (szA₁ T₁) = 2 ^ (2 * a + 1) := by
  rw [h.coords.card_szA₁ h.one_le h.card, Nat.card_eq_fintype_card, h.card]

theorem conj_szA₁ {x : G} (hx : x ∈ R) {b : G} (hb : b ∈ szA₁ T₁) : x * b * x⁻¹ = b := by
  refine GMS28.commute_of_isPGroup_of_transitive (U := szA₁ T₁) (S := R) (y := d⁻¹)
    h.le_normalizer_szA₁ (inv_mem h.d_mem_normalizer_szA₁) (inv_mem h.d_mem_normalizer_R)
    (fun b hb b' hb' hb1 hb'1 => ?_) (fun s hs => ?_) ?_ x hx b hb
  · obtain ⟨k, hk⟩ := h.coords.exists_pow_conj_eq_szA₁ h.one_le h.card h.gen' hb hb' hb1 hb'1
    exact ⟨k, by rw [inv_pow, inv_inv, hk]⟩
  · obtain ⟨k, hk⟩ := h.isPGroup ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, fun b _ => by rw [hk', one_mul, inv_one, mul_one]⟩
  · rw [h.card_szA₁]
    exact dvd_pow_self 2 (by omega)

theorem commute_szA₁_of_mem {x : G} (hx : x ∈ R) {b : G} (hb : b ∈ szA₁ T₁) : x * b = b * x := by
  have e := h.conj_szA₁ hx hb
  calc x * b = x * b * x⁻¹ * x := by group
    _ = b * x := by rw [e]

theorem rho_mul {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * t * (x * y)⁻¹ * t⁻¹ = x * t * x⁻¹ * t⁻¹ * (y * t * y⁻¹ * t⁻¹) := by
  have e : x * y * t * (x * y)⁻¹ * t⁻¹ =
      x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * t⁻¹) := by group
  rw [e, h.conj_szA₁ hx (h.rho_mem y hy), h.commute_szA₁ (h.rho_mem y hy) (h.rho_mem x hx)]

theorem rho_eq_one_iff {x : G} (hx : x ∈ R) :
    x * t * x⁻¹ * t⁻¹ = 1 ↔ x ∈ T₁ ⊔ zpowers t := by
  rw [← h.inf_centralizer]
  constructor
  · intro h1
    refine mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
      _ = t * x := by rw [h1, one_mul]
  · intro h1
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2]
    group

theorem rho_inv {x : G} (hx : x ∈ R) :
    x⁻¹ * t * x⁻¹⁻¹ * t⁻¹ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by
  have h1 := h.rho_mul (inv_mem hx) hx
  rw [inv_mul_cancel, show (1 : G) * t * 1⁻¹ * t⁻¹ = 1 by group] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem rho_conj (k : ℕ) (x : G) :
    (d ^ k)⁻¹ * x * d ^ k * t * ((d ^ k)⁻¹ * x * d ^ k)⁻¹ * t⁻¹ =
      (d ^ k)⁻¹ * (x * t * x⁻¹ * t⁻¹) * d ^ k := by
  have h3 : (d ^ k)⁻¹ * t * d ^ k = t := by
    rw [mul_assoc, ← ((Commute.pow_left h.d_comm k).eq)]
    group
  conv_lhs => rw [← h3]
  group

theorem conj_pow_mem_R (k : ℕ) {x : G} (hx : x ∈ R) : (d ^ k)⁻¹ * x * d ^ k ∈ R := by
  have := (mem_normalizer_iff.mp (inv_mem (pow_mem h.d_mem_normalizer_R k)) x).mp hx
  simpa using this

theorem exists_conj_mem {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) (hxT : x ∉ T₁ ⊔ zpowers t)
    (hx'T : x' ∉ T₁ ⊔ zpowers t) :
    ∃ k : ℕ, x'⁻¹ * ((d ^ k)⁻¹ * x * d ^ k) ∈ T₁ ⊔ zpowers t := by
  have h1 : x * t * x⁻¹ * t⁻¹ ≠ 1 := fun h1 => hxT ((h.rho_eq_one_iff hx).mp h1)
  have h2 : x' * t * x'⁻¹ * t⁻¹ ≠ 1 := fun h2 => hx'T ((h.rho_eq_one_iff hx').mp h2)
  obtain ⟨k, hk⟩ := h.coords.exists_pow_conj_eq_szA₁ h.one_le h.card h.gen' (h.rho_mem x hx)
    (h.rho_mem x' hx') h1 h2
  refine ⟨k, (h.rho_eq_one_iff (mul_mem (inv_mem hx') (h.conj_pow_mem_R k hx))).mp ?_⟩
  rw [h.rho_mul (inv_mem hx') (h.conj_pow_mem_R k hx), h.rho_inv hx', h.rho_conj k x, hk,
    inv_mul_cancel]

theorem pow_theta_succ_injective :
    Function.Injective (fun z : K => z ^ (2 ^ (a + 1) + 1)) :=
  Finite.injective_iff_surjective.mpr fun z => SzStartField.exists_pow_theta_succ_eq h.card z

theorem szUT_one : szUT T₁ t u 1 = 0 := by
  rw [szUT_of_mem (one_mem T₁), h.coords.u_one]

theorem szUT_inv {z : G} (hz : z ∈ T₁ ⊔ zpowers t) : szUT T₁ t u z⁻¹ = szUT T₁ t u z := by
  have h1 := h.coords.szUT_mul h.t_mem h.t_sq h.t_not_mem (inv_mem hz) hz
  rw [inv_mul_cancel, h.szUT_one] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination -h1 - szUT T₁ t u z * h2

theorem conj_mul_inv_mem_szA {x : G} (hx : x ∈ R) {z : G} (hz : z ∈ T₁ ⊔ zpowers t) :
    x * z * x⁻¹ * z⁻¹ ∈ szA₁ T₁ ⊔ zpowers t := by
  have hw : x * z * x⁻¹ ∈ T₁ ⊔ zpowers t := (mem_normalizer_iff.mp (h.le_normalizer_T hx) z).mp hz
  have hsq : (x * z * x⁻¹) ^ 2 = z ^ 2 := by
    have e : (x * z * x⁻¹) ^ 2 = x * z ^ 2 * x⁻¹ := by rw [sq, sq]; group
    rw [e, h.conj_szA₁ hx (h.sq_mem_szA₁_of_mem_T hz)]
  have h1 := (h.coords.sq_mem_and_v_sq h.one_le h.card h.t_mem h.t_sq h.t_not_mem hw).2
  have h2 := (h.coords.sq_mem_and_v_sq h.one_le h.card h.t_mem h.t_sq h.t_not_mem hz).2
  rw [hsq, h2] at h1
  have hu : szUT T₁ t u (x * z * x⁻¹) = szUT T₁ t u z := h.pow_theta_succ_injective h1.symm
  refine h.coords.mem_of_szUT_eq_zero h.one_le h.card h.t_mem h.t_sq h.t_not_mem
    (mul_mem hw (inv_mem hz)) ?_
  rw [h.coords.szUT_mul h.t_mem h.t_sq h.t_not_mem hw (inv_mem hz), hu, h.szUT_inv hz,
    CharTwo.add_self_eq_zero]

end SzRSetup

end CFSG.SeitzReduction.RankOne
