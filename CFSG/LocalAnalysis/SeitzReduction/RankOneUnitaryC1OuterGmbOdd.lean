module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped MatrixGroups

section OddMatrices

variable {F : Type*} [Field F]

@[expose] def gmbQa (F : Type*) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def gmbQb {x y : F} (h : x ^ 2 + y ^ 2 = -1) : SL(2, F) :=
  ⟨!![x, y; y, -x], by rw [Matrix.det_fin_two_of]; linear_combination -h⟩

@[expose] def gmbQc {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) : SL(2, F) :=
  ⟨!![(1 + x + y) / 2, (1 + y - x) / 2; (-1 + y - x) / 2, (1 - x - y) / 2], by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination (-2 : F) * h⟩

theorem coe_gmbQa : ((gmbQa F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem coe_gmbQb {x y : F} (h : x ^ 2 + y ^ 2 = -1) :
    ((gmbQb h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![x, y; y, -x] := rfl

theorem coe_gmbQc {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    ((gmbQc h h2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(1 + x + y) / 2, (1 + y - x) / 2; (-1 + y - x) / 2, (1 - x - y) / 2] := rfl

theorem gmbQb_mul_gmbQa {x y : F} (h : x ^ 2 + y ^ 2 = -1) :
    gmbQb h * gmbQa F = gmbQa F * gmbQb h * (gmbQa F * gmbQa F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_gmbQa, coe_gmbQb,
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem gmbQc_mul_gmbQa {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbQc h h2 * gmbQa F = gmbQb h * gmbQc h h2 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_gmbQa, coe_gmbQb,
    coe_gmbQc, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    first | ring1 | linear_combination h | linear_combination (-1 : F) * h

theorem gmbQc_mul_gmbQb {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbQc h h2 * gmbQb h = (gmbQa F * gmbQb h) * gmbQc h h2 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_gmbQa, coe_gmbQb, coe_gmbQc, Matrix.mul_fin_two,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring1

theorem gmbQc_sq {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    ((gmbQc h h2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (gmbQc h h2 : SL(2, F)) =
      (gmbQc h h2 : SL(2, F)) - 1 := by
  rw [coe_gmbQc, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    first | ring1 | linear_combination h | linear_combination (-1 : F) * h |
      linear_combination (2 : F) * h

theorem gmbQc_cube {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    ((gmbQc h h2 * gmbQc h h2 * gmbQc h h2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, gmbQc_sq, sub_mul,
    gmbQc_sq, one_mul, sub_sub_cancel_left]

theorem gmb_mem_center_sl2_iff {w : SL(2, F)} :
    w ∈ center SL(2, F) ↔ (w : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      (w : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (w : Matrix (Fin 2) (Fin 2) F) 0 0 = (w : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, -, hr⟩
    rw [← hr]
    simp
  · rintro ⟨h01, h10, h00⟩
    refine ⟨(w : Matrix (Fin 2) (Fin 2) F) 0 0, ?_, ?_⟩
    · have hd := Matrix.SpecialLinearGroup.det_coe w
      rw [Matrix.det_fin_two, h01, h10, ← h00] at hd
      rw [Fintype.card_fin, sq]
      simpa using hd
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

theorem gmb_center_sl2_mul_self {w : SL(2, F)} (hw : w ∈ center SL(2, F)) : w * w = 1 := by
  obtain ⟨r, hr, hrw⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hw
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrw, Matrix.SpecialLinearGroup.coe_one, ← map_mul,
    ← sq, ← Fintype.card_fin 2, hr, map_one]

end OddMatrices

section OddPSL

variable {F : Type*} [Field F]

abbrev gmbPi (F : Type*) [Field F] : SL(2, F) →* PSL(2, F) :=
  QuotientGroup.mk' (center SL(2, F))

theorem gmbPi_eq_one_iff {g : SL(2, F)} : gmbPi F g = 1 ↔ g ∈ center SL(2, F) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem gmb_pa_mul_self : gmbPi F (gmbQa F) * gmbPi F (gmbQa F) = 1 := by
  rw [← map_mul, gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, Matrix.SpecialLinearGroup.coe_mul,
    coe_gmbQa, Matrix.mul_fin_two]
  simp

theorem gmb_pb_mul_self {x y : F} (h : x ^ 2 + y ^ 2 = -1) :
    gmbPi F (gmbQb h) * gmbPi F (gmbQb h) = 1 := by
  rw [← map_mul, gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, Matrix.SpecialLinearGroup.coe_mul,
    coe_gmbQb, Matrix.mul_fin_two]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

theorem gmb_pa_pb_comm {x y : F} (h : x ^ 2 + y ^ 2 = -1) :
    gmbPi F (gmbQa F) * gmbPi F (gmbQb h) = gmbPi F (gmbQb h) * gmbPi F (gmbQa F) := by
  rw [← map_mul, ← map_mul, gmbQb_mul_gmbQa, map_mul (gmbPi F) (gmbQa F * gmbQb h),
    map_mul (gmbPi F) (gmbQa F) (gmbQa F), gmb_pa_mul_self, mul_one]

theorem gmb_pa_ne_one : gmbPi F (gmbQa F) ≠ 1 := by
  rw [Ne, gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, coe_gmbQa]
  simp

theorem gmb_pb_ne_one {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQb h) ≠ 1 := by
  rw [Ne, gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, coe_gmbQb]
  rintro ⟨h01, -, h00⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h00
  have hx : 2 * x = 0 := by linear_combination h00
  have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_left h2
  have : (0 : F) = -1 := by rw [← h, hx0, h01]; ring
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem gmb_pa_ne_pb {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQa F) ≠ gmbPi F (gmbQb h) := by
  intro hab
  have h1 : gmbPi F (gmbQa F * gmbQb h) = 1 := by rw [map_mul, hab, gmb_pb_mul_self]
  rw [gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, Matrix.SpecialLinearGroup.coe_mul, coe_gmbQa,
    coe_gmbQb, Matrix.mul_fin_two] at h1
  obtain ⟨h01, -, h00⟩ := h1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h00
  have hx0 : x = 0 := by linear_combination -h01
  have hy : 2 * y = 0 := by linear_combination h00
  have hy0 : y = 0 := (mul_eq_zero.mp hy).resolve_left h2
  have : (0 : F) = -1 := by rw [← h, hx0, hy0]; ring
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem gmb_pc_conj_pa {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQc h h2) * gmbPi F (gmbQa F) * (gmbPi F (gmbQc h h2))⁻¹ = gmbPi F (gmbQb h) := by
  rw [← map_mul, gmbQc_mul_gmbQa, map_mul, mul_inv_cancel_right]

theorem gmb_pc_conj_pb {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQc h h2) * gmbPi F (gmbQb h) * (gmbPi F (gmbQc h h2))⁻¹ =
      gmbPi F (gmbQa F) * gmbPi F (gmbQb h) := by
  rw [← map_mul, gmbQc_mul_gmbQb, map_mul, map_mul, mul_inv_cancel_right]

theorem gmb_pc_pow_three {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQc h h2) ^ 3 = 1 := by
  have h1 : gmbPi F (gmbQc h h2 * gmbQc h h2 * gmbQc h h2) = 1 := by
    rw [gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, gmbQc_cube]
    simp
  rw [map_mul, map_mul] at h1
  rw [pow_three, ← mul_assoc]
  exact h1

theorem gmb_pc_ne_one {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQc h h2) ≠ 1 := by
  rw [Ne, gmbPi_eq_one_iff, gmb_mem_center_sl2_iff, coe_gmbQc]
  rintro ⟨h01, h10, -⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h10
  have e : (1 + y - x) / 2 - (-1 + y - x) / 2 = (1 : F) := by
    field_simp
    ring
  rw [h01, h10, sub_zero] at e
  exact zero_ne_one e

theorem gmb_sq_comm_of_pi {g a' : SL(2, F)}
    (hg : gmbPi F g * gmbPi F a' * (gmbPi F g)⁻¹ = gmbPi F a') :
    (g * g) * a' = a' * (g * g) := by
  rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hg
  have hw : (g * a' * g⁻¹)⁻¹ * a' ∈ center SL(2, F) := QuotientGroup.eq.mp hg
  set w := (g * a' * g⁻¹)⁻¹ * a' with hwdef
  have hga : g * a' * g⁻¹ = a' * w⁻¹ := by rw [hwdef]; group
  have hwi : w⁻¹ ∈ center SL(2, F) := inv_mem hw
  have hgw : g * w⁻¹ * g⁻¹ = w⁻¹ := by
    rw [Subgroup.mem_center_iff.mp hwi g, mul_inv_cancel_right]
  have hww : w⁻¹ * w⁻¹ = 1 := gmb_center_sl2_mul_self hwi
  have key : (g * g) * a' * (g * g)⁻¹ = a' := by
    calc (g * g) * a' * (g * g)⁻¹ = g * (g * a' * g⁻¹) * g⁻¹ := by group
      _ = g * (a' * w⁻¹) * g⁻¹ := by rw [hga]
      _ = (g * a' * g⁻¹) * (g * w⁻¹ * g⁻¹) := by group
      _ = a' * w⁻¹ * w⁻¹ := by rw [hga, hgw]
      _ = a' := by rw [mul_assoc, hww, mul_one]
  calc (g * g) * a' = (g * g) * a' * (g * g)⁻¹ * (g * g) := by group
    _ = a' * (g * g) := by rw [key]

theorem gmb_mem_center_of_comm {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    {m : SL(2, F)} (ha : m * gmbQa F = gmbQa F * m) (hb : m * gmbQb h = gmbQb h * m) :
    m ∈ center SL(2, F) := by
  have ea := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F)) ha
  have eb := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F)) hb
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_gmbQa, coe_gmbQb] at ea eb
  have a00 := congrFun (congrFun ea 0) 0
  have a01 := congrFun (congrFun ea 0) 1
  have b00 := congrFun (congrFun eb 0) 0
  have b01 := congrFun (congrFun eb 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a00 a01 b00 b01
  rw [gmb_mem_center_sl2_iff]
  have hqy : 2 * ((m : Matrix (Fin 2) (Fin 2) F) 0 1 * y) = 0 := by
    linear_combination b00 - y * a00
  have hqx : 2 * ((m : Matrix (Fin 2) (Fin 2) F) 0 1 * x) = 0 := by
    linear_combination -b01 + y * a01
  have hqy' := (mul_eq_zero.mp hqy).resolve_left h2
  have hqx' := (mul_eq_zero.mp hqx).resolve_left h2
  have hq : (m : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    linear_combination (m : Matrix (Fin 2) (Fin 2) F) 0 1 * h - x * hqx' - y * hqy'
  refine ⟨hq, ?_, ?_⟩
  · linear_combination -a00 - hq
  · linear_combination a01

end OddPSL

section OddProp

variable {F : Type*} [Field F]

@[expose] def gmbQ₀ {x y : F} (h : x ^ 2 + y ^ 2 = -1) : Subgroup PSL(2, F) :=
  gmbKlein (gmbPi F (gmbQa F)) (gmbPi F (gmbQb h)) gmb_pa_mul_self (gmb_pb_mul_self h)
    (gmb_pa_pb_comm h)

theorem gmbQ₀_card {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    Nat.card (gmbQ₀ h) = 4 :=
  gmbKlein_card gmb_pa_ne_one (gmb_pb_ne_one h h2) (gmb_pa_ne_pb h h2)

theorem gmbQ₀_mul_self {x y : F} (h : x ^ 2 + y ^ 2 = -1) {z : PSL(2, F)} (hz : z ∈ gmbQ₀ h) :
    z * z = 1 :=
  gmbKlein_mul_self hz

theorem gmb_pc_mem_normalizer [Finite F] {x y : F} (h : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    gmbPi F (gmbQc h h2) ∈ normalizer ((gmbQ₀ h : Subgroup PSL(2, F)) : Set PSL(2, F)) := by
  apply gmb_mem_normalizer_of_conj
  intro z hz
  rcases mem_gmbKlein.mp hz with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact (gmbQ₀ h).one_mem
  · rw [gmb_pc_conj_pa]
    exact mem_gmbKlein.mpr (Or.inr (Or.inr (Or.inl rfl)))
  · rw [gmb_pc_conj_pb]
    exact mem_gmbKlein.mpr (Or.inr (Or.inr (Or.inr rfl)))
  · rw [show gmbPi F (gmbQc h h2) * (gmbPi F (gmbQa F) * gmbPi F (gmbQb h)) *
          (gmbPi F (gmbQc h h2))⁻¹ =
        (gmbPi F (gmbQc h h2) * gmbPi F (gmbQa F) * (gmbPi F (gmbQc h h2))⁻¹) *
          (gmbPi F (gmbQc h h2) * gmbPi F (gmbQb h) * (gmbPi F (gmbQc h h2))⁻¹) by group,
      gmb_pc_conj_pa, gmb_pc_conj_pb, ← mul_assoc, ← gmb_pa_pb_comm h, mul_assoc,
      gmb_pb_mul_self h, mul_one]
    exact mem_gmbKlein.mpr (Or.inr (Or.inl rfl))

theorem gmb_mul_self_of_centralizes_Q₀ {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    (g : PSL(2, F)) (hg : ∀ z ∈ gmbQ₀ h, g * z * g⁻¹ = z) : g * g = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center SL(2, F)) g
  have ha := gmb_sq_comm_of_pi (hg _ (mem_gmbKlein.mpr (Or.inr (Or.inl rfl))))
  have hb := gmb_sq_comm_of_pi (hg _ (mem_gmbKlein.mpr (Or.inr (Or.inr (Or.inl rfl)))))
  rw [← map_mul]
  exact gmbPi_eq_one_iff.mpr (gmb_mem_center_of_comm h h2 ha hb)

theorem gmb_not_two_dvd_of_mod_eight {q i : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5)
    (h : 4 * i = q * (q ^ 2 - 1) / 2) : ¬ 2 ∣ i := by
  rcases hq with hq | hq
  · obtain ⟨m, rfl⟩ : ∃ m, q = 8 * m + 3 := ⟨q / 8, by omega⟩
    have e : (8 * m + 3) ^ 2 - 1 = 8 * ((4 * m + 1) * (2 * m + 1)) :=
      Nat.sub_eq_of_eq_add (by ring)
    have e2 : (8 * m + 3) * (8 * ((4 * m + 1) * (2 * m + 1))) / 2 =
        4 * ((8 * m + 3) * ((4 * m + 1) * (2 * m + 1))) := by
      rw [show (8 * m + 3) * (8 * ((4 * m + 1) * (2 * m + 1))) =
        2 * (4 * ((8 * m + 3) * ((4 * m + 1) * (2 * m + 1)))) by ring]
      exact Nat.mul_div_cancel_left _ two_pos
    rw [e, e2] at h
    rw [Nat.eq_of_mul_eq_mul_left (by norm_num) h]
    apply Odd.not_two_dvd_nat
    exact Nat.odd_mul.mpr ⟨⟨4 * m + 1, by ring⟩, Nat.odd_mul.mpr ⟨⟨2 * m, by ring⟩, ⟨m, by ring⟩⟩⟩
  · obtain ⟨m, rfl⟩ : ∃ m, q = 8 * m + 5 := ⟨q / 8, by omega⟩
    have e : (8 * m + 5) ^ 2 - 1 = 8 * ((2 * m + 1) * (4 * m + 3)) :=
      Nat.sub_eq_of_eq_add (by ring)
    have e2 : (8 * m + 5) * (8 * ((2 * m + 1) * (4 * m + 3))) / 2 =
        4 * ((8 * m + 5) * ((2 * m + 1) * (4 * m + 3))) := by
      rw [show (8 * m + 5) * (8 * ((2 * m + 1) * (4 * m + 3))) =
        2 * (4 * ((8 * m + 5) * ((2 * m + 1) * (4 * m + 3)))) by ring]
      exact Nat.mul_div_cancel_left _ two_pos
    rw [e, e2] at h
    rw [Nat.eq_of_mul_eq_mul_left (by norm_num) h]
    apply Odd.not_two_dvd_nat
    exact Nat.odd_mul.mpr
      ⟨⟨4 * m + 2, by ring⟩, Nat.odd_mul.mpr ⟨⟨m, by ring⟩, ⟨2 * m + 1, by ring⟩⟩⟩

theorem gmbProp_psl2_odd [Finite F] (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) :
    GmbProp PSL(2, F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have := FiniteField.even_card_iff_char_two.mp hc
    rw [← hcard] at this
    omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have : NeZero (ringChar F) := ⟨hp.ne_zero⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have h : (a : F) ^ 2 + (b : F) ^ 2 = -1 := by
    rw [hab]
    simp
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨ringChar F, n, hp, hp.odd_of_ne_two hchar, n.pos, by rw [hcard, hn]⟩
  have hPSL := CFSG.GorensteinWalter.psl2_card_formula F hodd
  have hQp : IsPGroup 2 (gmbQ₀ h) :=
    IsPGroup.of_card (n := 2) (by rw [gmbQ₀_card h h2]; norm_num)
  have hQi : ¬ 2 ∣ (gmbQ₀ h).index := by
    apply gmb_not_two_dvd_of_mod_eight h8
    rw [← hPSL, ← gmbQ₀_card h h2]
    exact (gmbQ₀ h).card_mul_index
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hco : orderOf (gmbPi F (gmbQc h h2)) = 3 :=
    orderOf_eq_prime (gmb_pc_pow_three h h2) (gmb_pc_ne_one h h2)
  refine gmbProp_of_klein (hQp.toSylow hQi) ?_ ?_ (c := gmbPi F (gmbQc h h2)) ?_
    (gmb_pc_ne_one h h2) ?_ ?_
  · rw [IsPGroup.toSylow_coe]
    exact gmbQ₀_card h h2
  · rw [IsPGroup.toSylow_coe]
    exact fun z hz => gmbQ₀_mul_self h hz
  · rw [IsPGroup.toSylow_coe]
    exact gmb_pc_mem_normalizer h h2
  · rw [hco]
    decide
  · rw [IsPGroup.toSylow_coe]
    exact gmb_mul_self_of_centralizes_Q₀ h h2

end OddProp

end CFSG.SeitzReduction.RankOne
