module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Tor

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4

namespace Cat7E6

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem starU_starU (u : (Gauss K)ˣ) : starU (starU u) = u := Units.ext (by simp)

theorem normU_rho (u : (Gauss K)ˣ) :
    QuadraticAlgebra.norm ((rho u : (Gauss K)ˣ) : Gauss K) = 1 := by
  rw [← coe_normU, rho, map_mul, map_inv]
  have : normU (starU u) = normU u := Units.ext (by
    rw [coe_normU, coe_normU, coe_starU, QuadraticAlgebra.norm_star])
  rw [this, mul_inv_cancel, Units.val_one]

theorem starU_rho (u : (Gauss K)ˣ) : starU (rho u) = (rho u)⁻¹ := by
  rw [rho, map_mul, map_inv, starU_starU, mul_inv_rev, inv_inv, mul_comm]

theorem starU_eq_rho_inv_mul (u : (Gauss K)ˣ) : starU u = (rho u)⁻¹ * u := by
  rw [rho, mul_inv_rev, inv_inv, inv_mul_cancel_right]

theorem rho_zpow_eq_one_iff (u : (Gauss K)ˣ) (j : ℤ) :
    rho u ^ j = 1 ↔ star ((u ^ j : (Gauss K)ˣ) : Gauss K) = ((u ^ j : (Gauss K)ˣ) : Gauss K) := by
  rw [rho, mul_zpow, inv_zpow, mul_inv_eq_one, ← map_zpow, Units.ext_iff, coe_starU]
  exact eq_comm

theorem eq_algebraMap_of_star_eq (h2 : (2 : K) ≠ 0) {z : Gauss K} (h : star z = z) :
    z = algebraMap K (Gauss K) z.re := by
  have him := (star_eq_self_iff h2 z).mp h
  rw [QuadraticAlgebra.algebraMap_eq]
  ext
  · rfl
  · exact him

section Elements

variable (u : (Gauss K)ˣ)

@[expose] def tA : torSub K :=
  ⟨(rho u, 1), mem_torSub.mpr (by rw [normU_rho, Units.val_one, QuadraticAlgebra.norm_one])⟩

@[expose] def tB : torSub K := ⟨(u, u), mem_torSub.mpr rfl⟩

@[expose] def tC (z : (Gauss K)ˣ) (hz : QuadraticAlgebra.norm (z : Gauss K) = 1) : torSub K :=
  ⟨(1, z), mem_torSub.mpr (by rw [Units.val_one, QuadraticAlgebra.norm_one, hz])⟩

theorem coe_tA : ((tA u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) = (rho u, 1) := rfl

theorem coe_tB : ((tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) = (u, u) := rfl

theorem coe_tC (z : (Gauss K)ˣ) (hz : QuadraticAlgebra.norm (z : Gauss K) = 1) :
    ((tC z hz : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) = (1, z) := rfl

theorem tA_mul_tB : tA u * tB u = tB u * tA u :=
  Subtype.ext (Prod.ext (mul_comm _ _) (mul_comm _ _))

end Elements

section Chain

variable (u v : (Gauss K)ˣ) (hv : QuadraticAlgebra.norm (v : Gauss K) = -1)

@[expose] def a1 : MulAut (StatedProj (StatedSp 2 K)) := cT (tA u)
@[expose] def a2 : MulAut (StatedProj (StatedSp 2 K)) := cT (tB u)
@[expose] def a3 : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K (w3 v hv)
@[expose] def a4 : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K (sig1 v hv)

theorem a1_mul_a2 : a1 u * a2 u = a2 u * a1 u := by
  rw [a1, a2, ← map_mul, tA_mul_tB, map_mul]

theorem cT_tC_rho [Finite K] :
    cT (tC (rho u) (normU_rho u)) = (a1 u)⁻¹ * a2 u * a2 u := by
  rw [a1, a2, ← map_inv, ← map_mul, ← map_mul, cT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  refine conjAut_eq_of_smul _ _ (c := (QuadraticAlgebra.norm (u : Gauss K))⁻¹) ?_
  change mat (torG _) = _ • mat (torG _)
  rw [mat_torG, mat_torG]
  have hN := norm_ne_zero_of_unit u
  have e1 : (((((tA u)⁻¹ * tB u * tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).1 : (Gauss K)ˣ) :
      Gauss K) = algebraMap K (Gauss K) (QuadraticAlgebra.norm (u : Gauss K)) := by
    change (((rho u)⁻¹ * u * u : (Gauss K)ˣ) : Gauss K) = _
    rw [← starU_eq_rho_inv_mul, Units.val_mul, coe_starU, mul_comm, mul_star_eq_norm]
  have e2 : (((((tA u)⁻¹ * tB u * tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).2 : (Gauss K)ˣ) :
      Gauss K) = QuadraticAlgebra.norm (u : Gauss K) • ((rho u : (Gauss K)ˣ) : Gauss K) := by
    change ((1⁻¹ * u * u : (Gauss K)ˣ) : Gauss K) = _
    have hr : (u : Gauss K) = ((rho u : (Gauss K)ˣ) : Gauss K) * star (u : Gauss K) := by
      rw [← coe_starU, ← Units.val_mul, rho, inv_mul_cancel_right]
    rw [inv_one, one_mul, Units.val_mul]
    nth_rewrite 1 [hr]
    rw [mul_assoc, mul_comm (star (u : Gauss K)), mul_star_eq_norm, Algebra.smul_def, mul_comm]
  rw [e1, e2, gaussEmb_algebraMap, gaussEmb_smul, ← blk_smul, smul_smul, inv_mul_cancel₀ hN,
    one_smul, smul_smul, inv_mul_cancel₀ hN, one_smul]
  simp only [coe_tC, Units.val_one, map_one]

theorem a4_conj_a1 : a4 v hv * a1 u * (a4 v hv)⁻¹ = (a1 u)⁻¹ := by
  have hy : (((tA u)⁻¹ : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) =
      (starU ((tA u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).1,
        ((tA u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).2) := by
    change ((rho u)⁻¹, (1 : (Gauss K)ˣ)⁻¹) = (starU (rho u), 1)
    rw [starU_rho, inv_one]
  have h := conj_eq_of_mat (sig1_tor v hv (tA u) (tA u)⁻¹ hy)
  rw [map_inv, map_inv] at h
  exact h

theorem a4_conj_a2 : a4 v hv * a2 u * (a4 v hv)⁻¹ = (a1 u)⁻¹ * a2 u := by
  have hy : (((tA u)⁻¹ * tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) =
      (starU ((tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).1,
        ((tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).2) := by
    change ((rho u)⁻¹ * u, (1 : (Gauss K)ˣ)⁻¹ * u) = (starU u, u)
    rw [starU_eq_rho_inv_mul, inv_one, one_mul]
  have h := conj_eq_of_mat (sig1_tor v hv (tB u) ((tA u)⁻¹ * tB u) hy)
  rw [map_mul, map_mul, map_inv, map_inv] at h
  exact h

theorem a3_conj_a1 [Finite K] : a3 v hv * a1 u * (a3 v hv)⁻¹ = (a1 u)⁻¹ * a2 u * a2 u := by
  have hz : ((tC (rho u) (normU_rho u) : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) =
      (starU (((⟨(1, rho u), (tC (rho u) (normU_rho u)).2⟩ : torSub K) :
        (Gauss K)ˣ × (Gauss K)ˣ).1), rho u) := by
    change ((1 : (Gauss K)ˣ), rho u) = (starU 1, rho u)
    rw [map_one]
  have h := conj_eq_of_mat (w3_tor v hv (tA u) ⟨(1, rho u), (tC (rho u) (normU_rho u)).2⟩
    (tC (rho u) (normU_rho u)) rfl hz)
  rw [← cT_tC_rho]
  exact h

theorem a3_conj_a2 : a3 v hv * a2 u * (a3 v hv)⁻¹ = (a1 u)⁻¹ * a2 u := by
  have hz : (((tA u)⁻¹ * tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ) =
      (starU ((tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).2,
        ((tB u : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).1) := by
    change ((rho u)⁻¹ * u, (1 : (Gauss K)ˣ)⁻¹ * u) = (starU u, u)
    rw [starU_eq_rho_inv_mul, inv_one, one_mul]
  have h := conj_eq_of_mat (w3_tor v hv (tB u) (tB u) ((tA u)⁻¹ * tB u) rfl hz)
  rw [map_mul, map_mul, map_inv, map_inv] at h
  exact h

theorem a3_sq_conj_a1 :
    (a3 v hv * a3 v hv) * a1 u * (a3 v hv * a3 v hv)⁻¹ = (a1 u)⁻¹ := by
  have h1 := w3_tor v hv (tA u) ⟨(1, rho u), (tC (rho u) (normU_rho u)).2⟩
    (tC (rho u) (normU_rho u)) rfl (by
      change ((1 : (Gauss K)ˣ), rho u) = (starU 1, rho u)
      rw [map_one])
  have h2 := w3_tor v hv (tC (rho u) (normU_rho u)) (tA u) (tA u)⁻¹ rfl (by
      change ((rho u)⁻¹, (1 : (Gauss K)ˣ)⁻¹) = (starU (rho u), 1)
      rw [starU_rho, inv_one])
  have h := conj_eq_of_mat (A := w3 v hv * w3 v hv) (X := torG (tA u)) (Y := torG (tA u)⁻¹) (by
    rw [mat_mul, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, h2, Matrix.mul_assoc])
  rw [map_mul, map_inv, map_inv] at h
  exact h

theorem a3_pow_four [Finite K] : a3 v hv ^ 4 = 1 := by
  rw [a3, ← map_pow, show w3 v hv ^ 4 = (w3 v hv * w3 v hv) * (w3 v hv * w3 v hv) by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]]
  exact conjAut_eq_one_of_smul _ (mat_w3_pow_four v hv)

theorem a4_sq (hv1 : QuadraticAlgebra.norm ((v ^ 2 : (Gauss K)ˣ) : Gauss K) = 1) :
    a4 v hv * a4 v hv = cT (tC (v ^ 2) hv1) := by
  rw [a4, ← map_mul, cT, MonoidHom.comp_apply]
  congr 1
  apply gsp_ext
  rw [mat_sig1_sq, mat_torG]
  simp only [coe_tC, Units.val_one, map_one, sq, Units.val_mul]

theorem a4_conj_a3 : a4 v hv * a3 v hv * (a4 v hv)⁻¹ = a4 v hv * a4 v hv * (a3 v hv)⁻¹ := by
  have hs : (swp : gsp 2 K)⁻¹ = swp := inv_eq_of_mul_eq_one_left swp_mul_swp
  have e : sig1 v hv * w3 v hv * (sig1 v hv)⁻¹ = sig1 v hv * sig1 v hv * (w3 v hv)⁻¹ := by
    rw [w3, mul_inv_rev, hs]
    group
  calc a4 v hv * a3 v hv * (a4 v hv)⁻¹ = conjAut 2 K (sig1 v hv * w3 v hv * (sig1 v hv)⁻¹) := by
        simp only [a4, a3, map_mul, map_inv]
    _ = conjAut 2 K (sig1 v hv * sig1 v hv * (w3 v hv)⁻¹) := by rw [e]
    _ = a4 v hv * a4 v hv * (a3 v hv)⁻¹ := by simp only [a4, a3, map_mul, map_inv]

end Chain

section Order

variable (u v : (Gauss K)ˣ) (hv : QuadraticAlgebra.norm (v : Gauss K) = -1)

theorem star_algebraMap (c : K) : star (algebraMap K (Gauss K) c) = algebraMap K (Gauss K) c := by
  rw [QuadraticAlgebra.algebraMap_eq]
  ext <;> simp

theorem a1_zpow_mul_a2_zpow_eq_one_iff [Finite K] (h2 : (2 : K) ≠ 0) (i j : ℤ) :
    a1 u ^ i * a2 u ^ j = 1 ↔ rho u ^ i = 1 ∧ rho u ^ j = 1 := by
  rw [a1, a2, ← map_zpow, ← map_zpow, ← map_mul, cT_eq_one_iff]
  have e1 : (((tA u ^ i * tB u ^ j : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).1) =
      rho u ^ i * u ^ j := by
    simp [coe_tA, coe_tB]
  have e2 : (((tA u ^ i * tB u ^ j : torSub K) : (Gauss K)ˣ × (Gauss K)ˣ).2) = u ^ j := by
    simp [coe_tA, coe_tB]
  rw [e1, e2]
  constructor
  · rintro ⟨c, h1, h2'⟩
    refine ⟨?_, ?_⟩
    · apply Units.ext
      rw [Units.val_mul, ← h2'] at h1
      have h3 : ((rho u ^ i : (Gauss K)ˣ) : Gauss K) * ((u ^ j : (Gauss K)ˣ) : Gauss K) =
          1 * ((u ^ j : (Gauss K)ˣ) : Gauss K) := by rw [h1, one_mul]
      rw [Units.val_one]
      exact (Units.mul_left_inj (u ^ j)).mp h3
    · rw [rho_zpow_eq_one_iff, h2', star_algebraMap]
  · rintro ⟨hi, hj⟩
    rw [rho_zpow_eq_one_iff] at hj
    refine ⟨(((u ^ j : (Gauss K)ˣ) : Gauss K)).re, ?_, eq_algebraMap_of_star_eq h2 hj⟩
    rw [hi, one_mul]
    exact eq_algebraMap_of_star_eq h2 hj

theorem orderOf_a1 [Finite K] (h2 : (2 : K) ≠ 0) : orderOf (a1 u) = orderOf (rho u) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  have h := a1_zpow_mul_a2_zpow_eq_one_iff u h2 n 0
  simp only [zpow_zero, mul_one, zpow_natCast, and_true] at h
  exact h

theorem orderOf_a2 [Finite K] (h2 : (2 : K) ≠ 0) : orderOf (a2 u) = orderOf (rho u) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  have h := a1_zpow_mul_a2_zpow_eq_one_iff u h2 0 n
  simp only [zpow_zero, one_mul, zpow_natCast, true_and] at h
  exact h

abbrev W2 (u : (Gauss K)ˣ) : Subgroup (MulAut (StatedProj (StatedSp 2 K))) :=
  zpowers (a1 u) ⊔ zpowers (a2 u)

theorem zpowers_a1_inf_a2 [Finite K] (h2 : (2 : K) ≠ 0) : zpowers (a1 u) ⊓ zpowers (a2 u) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
  rw [mem_bot]
  have h := (a1_zpow_mul_a2_zpow_eq_one_iff u h2 i (-j)).mp (by
    simp only at hj
    rw [zpow_neg, ← hj, mul_inv_cancel])
  change a1 u ^ i = 1
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_a1 u h2, orderOf_dvd_iff_zpow_eq_one]
  exact h.1

theorem commute_a1_a2_zpow (i j : ℤ) : a1 u ^ i * a2 u ^ j = a2 u ^ j * a1 u ^ i :=
  ((Commute.zpow_zpow (a1_mul_a2 u) i j)).eq

theorem card_W2 [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (W2 u) = orderOf (rho u) * orderOf (rho u) := by
  rw [card_sup_of_commute (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact commute_a1_a2_zpow u i j) (zpowers_a1_inf_a2 u h2),
    Nat.card_zpowers, Nat.card_zpowers, orderOf_a1 u h2, orderOf_a2 u h2]

theorem W2_le_centralizer :
    W2 u ≤ centralizer ({a1 u} : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
  apply sup_le
  · rw [zpowers_le, mem_centralizer_singleton_iff]
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    exact (a1_mul_a2 u).symm

theorem a2_mem_normalizer : a2 u ∈ normalizer ((zpowers (a1 u) : Subgroup _) : Set _) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    have hc : a2 u * a1 u ^ i = a1 u ^ i * a2 u := by
      simpa using (commute_a1_a2_zpow u i 1).symm
    change a1 u ^ i = a2 u * a1 u ^ i * (a2 u)⁻¹
    rw [hc, mul_inv_cancel_right]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hc : a1 u ^ i * a2 u = a2 u * a1 u ^ i := by simpa using commute_a1_a2_zpow u i 1
    change a1 u ^ i = x
    change a1 u ^ i = a2 u * x * (a2 u)⁻¹ at hi
    rw [show x = (a2 u)⁻¹ * (a2 u * x * (a2 u)⁻¹) * a2 u by group, ← hi, mul_assoc, hc,
      ← mul_assoc, inv_mul_cancel, one_mul]

theorem a3_mem_normalizer [Finite K] :
    a3 v hv ∈ normalizer ((W2 u : Subgroup _) : Set _) :=
  mem_normalizer_of_conj_mem (conj_mem_sup_zpowers (by
      rw [a3_conj_a1]
      exact mul_mem (mul_mem (inv_mem (mem_sup_left (mem_zpowers _)))
        (mem_sup_right (mem_zpowers _))) (mem_sup_right (mem_zpowers _)))
    (by
      rw [a3_conj_a2]
      exact mul_mem (inv_mem (mem_sup_left (mem_zpowers _))) (mem_sup_right (mem_zpowers _))))

theorem a3_sq_not_mem [Finite K] (h2 : (2 : K) ≠ 0) (ho : 4 ≤ orderOf (rho u)) :
    a3 v hv ^ 2 ∉ W2 u := by
  intro h
  have hc := mem_centralizer_singleton_iff.mp (W2_le_centralizer u h)
  have h1 := a3_sq_conj_a1 u v hv
  rw [← sq, hc, mul_inv_cancel_right] at h1
  have h3 : a1 u ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h1]
    rw [mul_inv_cancel]
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [orderOf_a1 u h2] at h4
  have := Nat.le_of_dvd two_pos h4
  omega

theorem card_W3 [Finite K] (h2 : (2 : K) ≠ 0) (ho : 4 ≤ orderOf (rho u)) :
    (W2 u).relIndex (W2 u ⊔ zpowers (a3 v hv)) = 4 :=
  relIndex_sup_zpowers_eq_four (a3_mem_normalizer u v hv)
    (by rw [a3_pow_four]; exact one_mem _) (a3_sq_not_mem u v hv h2 ho)

theorem a4_sq_mem [Finite K] (hv2 : v ^ 2 ∈ zpowers (rho u)) : a4 v hv * a4 v hv ∈ W2 u := by
  have hv1 : QuadraticAlgebra.norm ((v ^ 2 : (Gauss K)ˣ) : Gauss K) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, hv]
    norm_num
  rw [a4_sq v hv hv1]
  obtain ⟨j, hj⟩ := hv2
  have e : tC (v ^ 2) hv1 = tC (rho u) (normU_rho u) ^ j := by
    apply Subtype.ext
    simp only [SubgroupClass.coe_zpow, coe_tC, Prod.pow_mk, one_zpow]
    rw [← hj]
  rw [e, map_zpow, cT_tC_rho]
  exact zpow_mem (mul_mem (mul_mem (inv_mem (mem_sup_left (mem_zpowers _)))
    (mem_sup_right (mem_zpowers _))) (mem_sup_right (mem_zpowers _))) j

abbrev W3 : Subgroup (MulAut (StatedProj (StatedSp 2 K))) := W2 u ⊔ zpowers (a3 v hv)

theorem a4_mem_normalizer [Finite K] (hv2 : v ^ 2 ∈ zpowers (rho u)) :
    a4 v hv ∈ normalizer ((W3 u v hv : Subgroup _) : Set _) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  have hle : (W3 u v hv).map (MulAut.conj (a4 v hv)).toMonoidHom ≤ W3 u v hv := by
    rw [W3, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ (zpowers_le.mpr ?_)
    · rintro _ ⟨y, hy, rfl⟩
      refine conj_mem_sup_zpowers (H := W3 u v hv) ?_ ?_ y hy
      · rw [a4_conj_a1]
        exact inv_mem (mem_sup_left (mem_sup_left (mem_zpowers _)))
      · rw [a4_conj_a2]
        exact mul_mem (inv_mem (mem_sup_left (mem_sup_left (mem_zpowers _))))
          (mem_sup_left (mem_sup_right (mem_zpowers _)))
    · change a4 v hv * a3 v hv * (a4 v hv)⁻¹ ∈ W3 u v hv
      rw [a4_conj_a3]
      exact mul_mem (mem_sup_left (a4_sq_mem u v hv hv2)) (inv_mem (mem_sup_right (mem_zpowers _)))
  exact hle ⟨x, hx, rfl⟩

theorem a4_not_mem [Finite K] (h2 : (2 : K) ≠ 0) (ho : 4 ≤ orderOf (rho u))
    (hv2 : v ^ 2 ∈ zpowers (rho u)) : a4 v hv ∉ W3 u v hv := by
  intro h
  obtain ⟨n, hn, k, hk⟩ := (mem_sup_zpowers_iff (a3_mem_normalizer u v hv)).mp h
  have e1 : a4 v hv * a3 v hv * (a4 v hv)⁻¹ = n * a3 v hv * n⁻¹ := by
    rw [hk]
    have : a3 v hv ^ k * a3 v hv * (a3 v hv ^ k)⁻¹ = a3 v hv := by
      rw [← zpow_add_one, ← zpow_neg, ← zpow_add]
      ring_nf
      rw [zpow_one]
    calc n * a3 v hv ^ k * a3 v hv * (n * a3 v hv ^ k)⁻¹ =
        n * (a3 v hv ^ k * a3 v hv * (a3 v hv ^ k)⁻¹) * n⁻¹ := by group
      _ = n * a3 v hv * n⁻¹ := by rw [this]
  rw [a4_conj_a3] at e1
  apply a3_sq_not_mem u v hv h2 ho
  have hm : a3 v hv * n * (a3 v hv)⁻¹ ∈ W2 u :=
    (mem_normalizer_iff.mp (a3_mem_normalizer u v hv) n).mp hn
  have e4 : a4 v hv * a4 v hv = n * a3 v hv * n⁻¹ * a3 v hv := by
    rw [← e1]
    group
  have e2 : a3 v hv ^ 2 = (a3 v hv * n * (a3 v hv)⁻¹) * (n⁻¹ * (a4 v hv * a4 v hv)) := by
    rw [sq, e4]
    group
  rw [e2]
  exact mul_mem hm (mul_mem (inv_mem hn) (a4_sq_mem u v hv hv2))

theorem card_W4 [Finite K] (h2 : (2 : K) ≠ 0) (ho : 4 ≤ orderOf (rho u))
    (hv2 : v ^ 2 ∈ zpowers (rho u)) :
    Nat.card ↥(W3 u v hv ⊔ zpowers (a4 v hv)) = 8 * (orderOf (rho u) * orderOf (rho u)) := by
  have h4 : (W3 u v hv).relIndex (W3 u v hv ⊔ zpowers (a4 v hv)) = 2 :=
    relIndex_sup_zpowers_eq_two (a4_mem_normalizer u v hv hv2)
      (mem_sup_left (a4_sq_mem u v hv hv2)) (a4_not_mem u v hv h2 ho hv2)
  have h3 := card_W3 u v hv h2 ho
  have c3 := Subgroup.relIndex_mul_card (H := W2 u) (K := W3 u v hv)
  have c4 := Subgroup.relIndex_mul_card (H := W3 u v hv) (K := W3 u v hv ⊔ zpowers (a4 v hv))
  rw [h3, inf_of_le_left le_sup_left, card_W2 u h2] at c3
  rw [h4, inf_of_le_left le_sup_left, ← c3] at c4
  rw [← c4]
  ring

end Order



end Cat7E6

end CFSG.ComponentClassification.GSThmB
