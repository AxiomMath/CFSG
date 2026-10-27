module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Model
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.TwoNormalized

open Matrix CFSG.Quasithin CFSG.LocalAnalysis.RankThreeTheoremC.A6Model

theorem mk_eq_mk_iff {A B : SL29} :
    (QuotientGroup.mk A : PSL29) = QuotientGroup.mk B ↔
      ∃ r : GF9, r * r = 1 ∧
        (B : Matrix (Fin 2) (Fin 2) GF9) = r • (A : Matrix (Fin 2) (Fin 2) GF9) := by
  rw [mk_eq_iff]
  unfold IsCentral
  simp only [Fintype.card_fin, pow_two]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    have h1 : (B : Matrix (Fin 2) (Fin 2) GF9) =
        (A : Matrix (Fin 2) (Fin 2) GF9) * ((A⁻¹ * B : SL29) : Matrix (Fin 2) (Fin 2) GF9) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [h1, ← h, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.mul_smul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem eq_one_or_eq_zero : ∀ ε r : GF9, ε * ε = 1 → r = ε * r → ε = 1 ∨ r = 0 := by
  decide +kernel

theorem mem_range_of_commute {a : GF9} (ha : a ≠ 0) {g : PSL29} (hg : g * ut a = ut a * g) :
    g ∈ uHom.range := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have h1 : (QuotientGroup.mk (g * um a) : PSL29) = QuotientGroup.mk (um a * g) := hg
  obtain ⟨ε, hε, hmat⟩ := mk_eq_mk_iff.mp h1
  have hdet : (g : Matrix (Fin 2) (Fin 2) GF9).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    show ((um a : SL29) : Matrix (Fin 2) (Fin 2) GF9) = !![1, a; 0, 1] from rfl,
    Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) GF9)] at hmat
  simp only [Matrix.mul_fin_two] at hmat
  have e00 := congrFun (congrFun hmat 0) 0
  have e01 := congrFun (congrFun hmat 0) 1
  have e10 := congrFun (congrFun hmat 1) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply,
    smul_eq_mul, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at e00 e01 e10
  set p := (g : Matrix (Fin 2) (Fin 2) GF9) 0 0 with hp
  set q := (g : Matrix (Fin 2) (Fin 2) GF9) 0 1 with hq
  set r := (g : Matrix (Fin 2) (Fin 2) GF9) 1 0 with hr
  set s := (g : Matrix (Fin 2) (Fin 2) GF9) 1 1 with hs
  have hr0 : r = 0 := by
    rcases eq_one_or_eq_zero ε r hε e10 with h | h
    · subst h
      have : a * r = 0 := by linear_combination e00
      exact (mul_eq_zero.mp this).resolve_left ha
    · exact h
  rw [hr0, mul_zero, add_zero] at e00
  have hε1 : ε = 1 := by
    rcases eq_one_or_eq_zero ε p hε e00 with h | h
    · exact h
    · rw [h, hr0] at hdet
      simp at hdet
  subst hε1
  have hsp : s = p := by
    have : a * (s - p) = 0 := by linear_combination e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
  have hpp : p * p = 1 := by
    rw [hr0, hsp, mul_zero, sub_zero] at hdet
    exact hdet
  refine mem_range_iff.mpr ⟨p * q, mk_eq_mk_iff.mpr ⟨p, hpp, ?_⟩⟩
  change !![1, p * q; 0, 1] = p • (g : Matrix (Fin 2) (Fin 2) GF9)
  rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) GF9), ← hp, ← hq, ← hr, ← hs, hr0, hsp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hpp]

@[expose] def hm : SL29 :=
  ⟨!![GF9.ofNat' 4, 0; 0, GF9.ofNat' 5], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def hmi : SL29 :=
  ⟨!![GF9.ofNat' 5, 0; 0, GF9.ofNat' 4], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def wm : SL29 :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def hb : PSL29 := QuotientGroup.mk hm

@[expose] def wb : PSL29 := QuotientGroup.mk wm

theorem hm_mul_hmi : hm * hmi = 1 := by decide +kernel

theorem hb_inv : hb⁻¹ = QuotientGroup.mk hmi := by
  rw [hb, ← QuotientGroup.mk_inv, inv_eq_of_mul_eq_one_right hm_mul_hmi]

theorem hm_conj : ∀ a : GF9, hm * um a * hmi = um (GF9.ofNat' 6 * a) := by decide +kernel

theorem hmi_conj : ∀ a : GF9, hmi * um a * hm = um (GF9.ofNat' 3 * a) := by decide +kernel

theorem hb_mem_normalizer : hb ∈ Subgroup.normalizer (uHom.range : Set PSL29) := by
  refine mem_normalizer_of_conj (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    refine mem_range_iff.mpr ⟨GF9.ofNat' 6 * a, ?_⟩
    rw [hb_inv]
    change (QuotientGroup.mk (hm * um a * hmi) : PSL29) =
      QuotientGroup.mk (um (GF9.ofNat' 6 * a))
    rw [hm_conj]
  · obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    refine mem_range_iff.mpr ⟨GF9.ofNat' 3 * a, ?_⟩
    rw [hb_inv]
    change (QuotientGroup.mk (hmi * um a * hm) : PSL29) =
      QuotientGroup.mk (um (GF9.ofNat' 3 * a))
    rw [hmi_conj]

theorem wm_mul_hm : wm * hm = hmi * wm := by decide +kernel

theorem wb_mul_hb : wb * hb = hb⁻¹ * wb := by
  rw [hb_inv]
  change (QuotientGroup.mk (wm * hm) : PSL29) = QuotientGroup.mk (hmi * wm)
  rw [wm_mul_hm]

theorem wm_um_cube : (wm * um 1) ^ 3 = 1 := by decide +kernel

theorem wb_ut_cube : (wb * ut 1) ^ 3 = 1 := by
  change (QuotientGroup.mk (wm * um 1) : PSL29) ^ 3 = 1
  rw [← QuotientGroup.mk_pow, wm_um_cube, QuotientGroup.mk_one]

theorem wm_conj_not_central : ∀ c : GF9, ¬ IsCentral ((wm * um 1 * wm⁻¹)⁻¹ * um c) := by
  decide +kernel

theorem wb_not_mem_normalizer : wb ∉ Subgroup.normalizer (uHom.range : Set PSL29) := by
  intro hn
  have h1 : (ut 1 : PSL29) ∈ (uHom.range : Set PSL29) := mem_range_iff.mpr ⟨1, rfl⟩
  obtain ⟨c, hc⟩ := mem_range_iff.mp ((Subgroup.mem_normalizer_iff.mp hn (ut 1)).mp h1)
  refine wm_conj_not_central c (mk_eq_iff.mp ?_)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact hc

theorem eq_zero_of_left : ∀ ε p : GF9, ε * ε = 1 →
    GF9.ofNat' 5 * p = ε * (p * GF9.ofNat' 4) → p = 0 := by
  decide +kernel

theorem eq_zero_of_right : ∀ ε s : GF9, ε * ε = 1 →
    GF9.ofNat' 4 * s = ε * (s * GF9.ofNat' 5) → s = 0 := by
  decide +kernel

@[expose] def am (q r : GF9) (h : q * r = -1) : SL29 :=
  ⟨!![0, q; r, 0], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : GF9) * h⟩

theorem am_cube : ∀ q r : GF9, ∀ h : q * r = -1, IsCentral ((am q r h * um 1) ^ 3) →
    IsCentral ((am q r h)⁻¹ * wm) := by
  decide +kernel

theorem eq_wb {g : PSL29} (h1 : g * hb = hb⁻¹ * g) (h2 : (g * ut 1) ^ 3 = 1) : g = wb := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [hb_inv] at h1
  have h1' : (QuotientGroup.mk (g * hm) : PSL29) = QuotientGroup.mk (hmi * g) := h1
  obtain ⟨ε, hε, hmat⟩ := mk_eq_mk_iff.mp h1'
  have hdet : (g : Matrix (Fin 2) (Fin 2) GF9).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    show ((hm : SL29) : Matrix (Fin 2) (Fin 2) GF9) =
      !![GF9.ofNat' 4, 0; 0, GF9.ofNat' 5] from rfl,
    show ((hmi : SL29) : Matrix (Fin 2) (Fin 2) GF9) =
      !![GF9.ofNat' 5, 0; 0, GF9.ofNat' 4] from rfl,
    Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) GF9)] at hmat
  simp only [Matrix.mul_fin_two] at hmat
  have e00 := congrFun (congrFun hmat 0) 0
  have e11 := congrFun (congrFun hmat 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply,
    smul_eq_mul, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at e00 e11
  have hp : (g : Matrix (Fin 2) (Fin 2) GF9) 0 0 = 0 := eq_zero_of_left ε _ hε e00
  have hs : (g : Matrix (Fin 2) (Fin 2) GF9) 1 1 = 0 := eq_zero_of_right ε _ hε e11
  have hqr : (g : Matrix (Fin 2) (Fin 2) GF9) 0 1 * (g : Matrix (Fin 2) (Fin 2) GF9) 1 0 = -1 := by
    rw [hp, hs] at hdet
    linear_combination (-1 : GF9) * hdet
  have hg : g = am _ _ hqr := by
    apply Subtype.ext
    change (g : Matrix (Fin 2) (Fin 2) GF9) =
      !![0, (g : Matrix (Fin 2) (Fin 2) GF9) 0 1; (g : Matrix (Fin 2) (Fin 2) GF9) 1 0, 0]
    conv_lhs => rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) GF9), hp, hs]
  have h2' : IsCentral ((g * um 1) ^ 3) := by
    rw [← mk_eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul]
    exact h2
  rw [hg] at h2'
  rw [hg]
  exact mk_eq_iff.mpr (am_cube _ _ hqr h2')

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.TwoNormalized
