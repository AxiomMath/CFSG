module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZSL3
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Core2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

variable {K : Type} [Field K]

abbrev x12 (c : K) : SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c

abbrev x21 (c : K) : SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c

theorem x12_mem_coordBlockSL (c : K) : x12 c ∈ coordBlockSL K blk :=
  transvection_mem_coordBlockSL (by decide) (by decide) _ c

theorem x21_mem_coordBlockSL (c : K) : x21 c ∈ coordBlockSL K blk :=
  transvection_mem_coordBlockSL (by decide) (by decide) _ c

theorem diag3_conj_x12 {d : Fin 3 → K} (hd : ∏ i, d i = 1) (c : K) :
    diag3 d hd * x12 c * (diag3 d hd)⁻¹ = x12 (d 1 * c / d 2) := by
  have hd0 := ne_zero_of_prod_eq_one hd
  have hinv : (diag3 d hd)⁻¹ = diag3 (fun i => (d i)⁻¹) (by
      rw [Finset.prod_inv_distrib, hd, inv_one]) := by
    apply inv_eq_of_mul_eq_one_right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, diagonal_mul_diagonal,
      Matrix.SpecialLinearGroup.coe_one]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, one_apply_eq, mul_inv_cancel₀ (hd0 i)]
    · rw [diagonal_apply_ne _ hij, one_apply_ne hij]
  rw [hinv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, x12,
    Matrix.SpecialLinearGroup.transvection_coe, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hd0, mul_comm, div_eq_mul_inv,
      mul_left_comm]

theorem fieldAut_proj_x12 (σ : K ≃+* K) (c : K) :
    fieldAut 3 K σ (proj 3 K (x12 c)) = proj 3 K (x12 (σ c)) := by
  rw [fieldAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, x12, Matrix.SpecialLinearGroup.transvection_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem eq_zero_of_proj_x12_commute {v : K}
    (h : proj 3 K (x12 v) * proj 3 K (x21 1) = proj 3 K (x21 1) * proj 3 K (x12 v)) : v = 0 := by
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  set X : SpecialLinearGroup (Fin 3) K := (x12 v * x21 1)⁻¹ * (x21 1 * x12 v) with hX
  have hrel : x21 1 * x12 v = (x12 v * x21 1) * X := by rw [hX]; group
  have hmat : ((x21 1 * x12 v : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x12 v * x21 1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        scalar (Fin 3) (c : K) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, ← hrel]
  have h00 := congrFun (congrFun hmat 0) 0
  have h11 := congrFun (congrFun hmat 1) 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, x12, x21, Matrix.SpecialLinearGroup.transvection_coe,
    scalar_apply, mul_diagonal] at h00 h11
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply] at h00 h11
  rw [← h00, mul_one] at h11
  linear_combination -h11

theorem glaPPrimeCore_le_center {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq
    (GLAPPrimeCore.normal p _) fun htop => ?_
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (hdvd.trans (Subgroup.card_quotient_dvd_card _))

theorem commute_of_mem_glaPPrimeCoreOf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J)
    {j : G} (hj : j ∈ J) : y * j = j * y := by
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hy
  have hc := Subgroup.mem_center_iff.1 (glaPPrimeCore_le_center hp hq hdvd ho) ⟨j, hj⟩
  exact (congrArg Subtype.val hc).symm

theorem prod_dr {lam : K} (h0 : lam ≠ 0) :
    ∏ i, (![(lam ^ 2)⁻¹, lam, lam] : Fin 3 → K) i = 1 := by
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp

theorem prod_du : ∏ i, (![1, -1, -1] : Fin 3 → K) i = 1 := by
  simp [Fin.prod_univ_three]

theorem coe_diag3_pow {d : Fin 3 → K} (hd : ∏ i, d i = 1) (n : ℕ) :
    ((diag3 d hd ^ n : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal (d ^ n) := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diag3, diagonal_pow]

theorem proj_diag3_eq_of_smul {d d' : Fin 3 → K} (hd : ∏ i, d i = 1) (hd' : ∏ i, d' i = 1) (c : Kˣ)
    (hc : c ^ 3 = 1) (h : ∀ i, d' i = d i * c) :
    proj 3 K (diag3 d' hd') = proj 3 K (diag3 d hd) := by
  have he : diag3 d' hd' = diag3 d hd * scalarElement c hc := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, coe_scalarElement, scalar_apply,
      diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, diagonal_apply_eq, h]
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ hij]
  rw [he, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hc), mul_one]

theorem eq_of_proj_diag3_eq_one {d : Fin 3 → K} (hd : ∏ i, d i = 1) (h : proj 3 K (diag3 d hd) = 1)
    (i j : Fin 3) : d i = d j := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h)
  have hi := congrFun (congrFun hc i) i
  have hj := congrFun (congrFun hc j) j
  rw [coe_diag3, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at hi hj
  rw [hi, hj]

theorem proj_diag3_commute {d d' : Fin 3 → K} (hd : ∏ i, d i = 1) (hd' : ∏ i, d' i = 1) :
    proj 3 K (diag3 d hd) * proj 3 K (diag3 d' hd') = proj 3 K (diag3 d' hd') * proj 3 K (diag3 d hd) := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, diagonal_mul_diagonal, mul_comm]

theorem fieldAut_proj_diag3 (σ : K ≃+* K) {d : Fin 3 → K} (hd : ∏ i, d i = 1) :
    fieldAut 3 K σ (proj 3 K (diag3 d hd)) = proj 3 K (diag3 (fun i => σ (d i))
      (by rw [← map_prod σ d, hd, map_one])) := by
  rw [fieldAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, coe_diag3, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, diagonal_apply_eq]
    rfl
  · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ hij, map_zero]

theorem conj_proj_diag3_x12 {d : Fin 3 → K} (hd : ∏ i, d i = 1) (c : K) :
    MulAut.conj (proj 3 K (diag3 d hd)) (proj 3 K (x12 c)) = proj 3 K (x12 (d 1 * c / d 2)) := by
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, diag3_conj_x12]

section Data

variable [Finite K] {p : ℕ} {lam : K}

theorem lam_ne_zero (hp : p.Prime) (hζ : IsPrimitiveRoot (lam ^ 3) p) : lam ≠ 0 := by
  intro h
  rw [h, zero_pow (by norm_num)] at hζ
  exact hζ.ne_zero hp.ne_zero rfl

theorem zeta_ne_zero (hp : p.Prime) (hζ : IsPrimitiveRoot (lam ^ 3) p) : lam ^ 3 ≠ 0 :=
  hζ.ne_zero hp.ne_zero

theorem zeta_ne_one (hp : p.Prime) (hζ : IsPrimitiveRoot (lam ^ 3) p) : lam ^ 3 ≠ 1 :=
  hζ.ne_one hp.one_lt

noncomputable def rE (hp : p.Prime) (hζ : IsPrimitiveRoot (lam ^ 3) p) : projectiveSL 3 K :=
  proj 3 K (diag3 ![(lam ^ 2)⁻¹, lam, lam] (prod_dr (lam_ne_zero hp hζ)))

noncomputable def tE (hp : p.Prime) (hζ : IsPrimitiveRoot (lam ^ 3) p) : projectiveSL 3 K :=
  proj 3 K (diag3 ![1, lam ^ 3, (lam ^ 3)⁻¹] (prod_diagBlk (zeta_ne_zero hp hζ)))

noncomputable def uE : projectiveSL 3 K := proj 3 K (diag3 ![1, -1, -1] prod_du)

variable (hp : p.Prime) (hζ : IsPrimitiveRoot (lam ^ 3) p)
include hp hζ

theorem rE_pow : rE hp hζ ^ p = 1 := by
  have h0 := lam_ne_zero hp hζ
  have hlp : (lam ^ p) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]
  have hl0 : lam ^ p ≠ 0 := pow_ne_zero p h0
  have hu : (Units.mk0 (lam ^ p) hl0) ^ 3 = 1 := Units.ext (by simpa using hlp)
  rw [rE, ← map_pow, proj_eq_one_iff]
  refine ⟨Units.mk0 (lam ^ p) hl0, hu, ?_⟩
  rw [coe_diag3_pow]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, scalar_apply, diagonal_apply_eq, Pi.pow_apply, Units.val_mk0]
    fin_cases i
    · show ((lam ^ 2)⁻¹) ^ p = lam ^ p
      have h3 : lam ^ (3 * p) = 1 := by rw [pow_mul, hζ.pow_eq_one]
      rw [inv_pow, ← pow_mul, inv_eq_iff_eq_inv]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_add, show 2 * p + p = 3 * p by ring, h3])
    · rfl
    · rfl
  · rw [diagonal_apply_ne _ hij, scalar_apply, diagonal_apply_ne _ hij]

theorem rE_ne_one : rE hp hζ ≠ 1 := by
  intro h
  have h01 := eq_of_proj_diag3_eq_one _ h 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h01
  have h0 := lam_ne_zero hp hζ
  apply zeta_ne_one hp hζ
  calc lam ^ 3 = lam ^ 2 * lam := by ring
    _ = lam ^ 2 * (lam ^ 2)⁻¹ := by rw [h01]
    _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 h0)

theorem tE_pow : tE hp hζ ^ p = 1 := by
  rw [tE, ← map_pow, proj_eq_one_iff]
  refine ⟨1, one_pow 3, ?_⟩
  rw [coe_diag3_pow]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, scalar_apply, diagonal_apply_eq, Pi.pow_apply, Units.val_one]
    fin_cases i
    · exact one_pow p
    · exact hζ.pow_eq_one
    · show ((lam ^ 3)⁻¹) ^ p = 1
      rw [inv_pow, hζ.pow_eq_one, inv_one]
  · rw [diagonal_apply_ne _ hij, scalar_apply, diagonal_apply_ne _ hij]

theorem tE_ne_one : tE hp hζ ≠ 1 := by
  intro h
  have h01 := eq_of_proj_diag3_eq_one _ h 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h01
  exact zeta_ne_one hp hζ h01.symm

theorem rE_tE_commute : rE hp hζ * tE hp hζ = tE hp hζ * rE hp hζ :=
  proj_diag3_commute _ _

theorem rE_uE_commute : rE hp hζ * uE = uE * rE hp hζ :=
  proj_diag3_commute _ _

theorem tE_uE_commute : tE hp hζ * uE = uE * tE hp hζ :=
  proj_diag3_commute _ _

theorem rE_commute_J3 {x : projectiveSL 3 K} (hx : x ∈ J3 K) : rE hp hζ * x = x * rE hp hζ := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hgc := coordBlockSL_le_centralizer_diag3 (d := ![(lam ^ 2)⁻¹, lam, lam])
    (hd := prod_dr (lam_ne_zero hp hζ)) rfl hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  rw [rE, ← map_mul, ← map_mul, hgc]

theorem conj_tE_x12 (c : K) :
    MulAut.conj (tE hp hζ) (proj 3 K (x12 c)) = proj 3 K (x12 ((lam ^ 3) ^ 2 * c)) := by
  rw [tE, conj_proj_diag3_x12]
  congr 2
  show lam ^ 3 * c / (lam ^ 3)⁻¹ = (lam ^ 3) ^ 2 * c
  rw [div_inv_eq_mul]
  ring

theorem conj_tE_zpow_x12 (j : ℤ) (c : K) :
    (MulAut.conj (tE hp hζ) ^ j) (proj 3 K (x12 c)) =
      proj 3 K (x12 ((lam ^ 3) ^ (2 * j) * c)) := by
  have hz := zeta_ne_zero hp hζ
  have hinv : ∀ c' : K, (MulAut.conj (tE hp hζ))⁻¹ (proj 3 K (x12 c')) =
      proj 3 K (x12 ((lam ^ 3) ^ (-2 : ℤ) * c')) := by
    intro c'
    have hc' : proj 3 K (x12 c') =
        MulAut.conj (tE hp hζ) (proj 3 K (x12 ((lam ^ 3) ^ (-2 : ℤ) * c'))) := by
      rw [conj_tE_x12]
      congr 2
      rw [show ((lam ^ 3) ^ 2 : K) = (lam ^ 3) ^ (2 : ℤ) by norm_cast, ← mul_assoc, ← zpow_add₀ hz]
      norm_num
    rw [hc', MulAut.inv_apply_self]
  induction j using Int.induction_on generalizing c with
  | zero => simp
  | succ n ih =>
    rw [_root_.zpow_add_one, MulAut.mul_apply, conj_tE_x12, ih]
    congr 2
    rw [← mul_assoc, show ((lam ^ 3) ^ 2 : K) = (lam ^ 3) ^ (2 : ℤ) by norm_cast, ← zpow_add₀ hz]
    congr 2 <;> ring
  | pred n ih =>
    rw [_root_.zpow_sub_one, MulAut.mul_apply, hinv, ih]
    congr 2
    rw [← mul_assoc, ← zpow_add₀ hz]
    congr 2 <;> ring


variable {σ : K ≃+* K} (hζσ : σ (lam ^ 3) = lam ^ 3)
include hζσ

theorem rE_fix : fieldAut 3 K σ (rE hp hζ) = rE hp hζ := by
  have h0 := lam_ne_zero hp hζ
  set e : K := σ lam / lam with he
  have he0 : e ≠ 0 := div_ne_zero ((map_ne_zero σ).2 h0) h0
  have he3 : e ^ 3 = 1 := by
    rw [he, div_pow, ← map_pow, hζσ, div_self (pow_ne_zero 3 h0)]
  have hσl : σ lam = lam * e := by rw [he, mul_div_cancel₀ _ h0]
  rw [rE, fieldAut_proj_diag3]
  refine proj_diag3_eq_of_smul _ _ (Units.mk0 e he0) (Units.ext (by simpa using he3)) ?_
  intro i
  fin_cases i
  · show σ ((lam ^ 2)⁻¹) = (lam ^ 2)⁻¹ * e
    rw [map_inv₀, map_pow, hσl]
    have : e⁻¹ ^ 2 = e := by
      rw [inv_pow, inv_eq_iff_eq_inv]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, he3])
    rw [mul_pow, mul_inv, ← inv_pow e 2, this]
  · exact hσl
  · exact hσl

theorem tE_fix : fieldAut 3 K σ (tE hp hζ) = tE hp hζ := by
  rw [tE, fieldAut_proj_diag3]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [coe_diag3]
  congr 1
  funext k
  fin_cases k
  · exact map_one σ
  · exact hζσ
  · show σ ((lam ^ 3)⁻¹) = (lam ^ 3)⁻¹
    rw [map_inv₀, hζσ]

omit hp hζ hζσ in
theorem uE_fix : fieldAut 3 K σ (uE : projectiveSL 3 K) = uE := by
  rw [uE, fieldAut_proj_diag3]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [coe_diag3]
  congr 1
  funext k
  fin_cases k <;> simp

end Data

section Pair

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem exists_of_mem_zpowers_sup' {a b x : G} (hab : a * b = b * a)
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : ∃ i j : ℤ, x = a ^ i * b ^ j := by
  let H : Subgroup G :=
    { carrier := {x | ∃ i j : ℤ, x = a ^ i * b ^ j}
      mul_mem' := by
        rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        have hc : Commute (b ^ j) (a ^ k) := (Commute.zpow_zpow hab.symm j k)
        refine ⟨i + k, j + l, ?_⟩
        rw [_root_.zpow_add, _root_.zpow_add]
        calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
          _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc.eq]
          _ = a ^ i * a ^ k * (b ^ j * b ^ l) := by group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro x ⟨i, j, rfl⟩
        have hc : Commute (b ^ (-j)) (a ^ (-i)) := (Commute.zpow_zpow hab.symm (-j) (-i))
        refine ⟨-i, -j, ?_⟩
        rw [_root_.mul_inv_rev, ← _root_.zpow_neg, ← _root_.zpow_neg]
        exact hc.eq }
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨1, 0, by simp⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨0, 1, by simp⟩
  exact hle hx

private theorem card_sup_of_commute' [Finite G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hA : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    Subgroup.mem_normalizer_iff.2 fun b => by
      constructor
      · intro hb
        rw [hc a ha b hb, mul_inv_cancel_right]
        exact hb
      · intro hb
        have h1 : a * b * a⁻¹ = b := by
          have h' := hc a ha (a * b * a⁻¹) hb
          calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
            _ = a⁻¹ * (a * b * a⁻¹ * a) := by rw [h']
            _ = b := by group
        rw [h1] at hb
        exact hb
  have hmul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hA
  let f : A × B → ↥(A ⊔ B) := fun q => ⟨q.1 * q.2, Subgroup.mul_mem_sup q.1.2 q.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ he
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val he
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = b' * (b : G)⁻¹ := by rw [h1]; group
      have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, by rw [h2]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [h, Subgroup.mem_bot] at hmem
      have ha : a' = a := Subtype.ext (inv_mul_eq_one.1 hmem)
      have hb : b' = b := Subtype.ext (mul_inv_eq_one.1 (h2 ▸ hmem))
      rw [ha, hb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by rw [← hmul]; exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem isElemAbelian_card_zpowers_sup [Finite G] {p : ℕ} (hp : p.Prime) {a b : G}
    (hab : a * b = b * a) (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hint : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow hab i j).eq
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨i, j, hx⟩ := exists_of_mem_zpowers_sup' hab x.2
    obtain ⟨k, l, hy⟩ := exists_of_mem_zpowers_sup' hab y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy]
    have h1 := (Commute.zpow_zpow hab i k)
    have h2 := (Commute.zpow_zpow hab i l)
    have h3 := (Commute.zpow_zpow hab k j)
    have h4 : Commute (b ^ j) (b ^ l) := Commute.zpow_zpow_self b j l
    have h5 : Commute (a ^ i) (a ^ k) := Commute.zpow_zpow_self a i k
    exact ((h5.mul_right h2).mul_left (h3.symm.mul_right h4)).eq
  · obtain ⟨i, j, rfl⟩ := exists_of_mem_zpowers_sup' hab hx
    rw [(Commute.zpow_zpow hab i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
      ← _root_.zpow_mul, mul_comm i, mul_comm j, _root_.zpow_mul, _root_.zpow_mul, zpow_natCast,
      zpow_natCast, ha, hb, _root_.one_zpow, _root_.one_zpow, one_mul]
  · rw [card_sup_of_commute' hcomm hint, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime ha ha1, orderOf_eq_prime hb hb1, sq]

end Pair

section Main

variable [Finite K] {p : ℕ} {lam : K}

theorem proj_x12_mul_inv (a b : K) :
    proj 3 K (x12 a) * (proj 3 K (x12 b))⁻¹ = proj 3 K (x12 (a - b)) := by
  rw [← map_inv, ← map_mul, x12, x12, x12, Matrix.SpecialLinearGroup.transvection_inv,
    ← Matrix.SpecialLinearGroup.transvection_add, sub_eq_add_neg]

theorem eq_of_proj_x12_eq {a b : K} (h : proj 3 K (x12 a) = proj 3 K (x12 b)) : a = b := by
  have h1 : proj 3 K (x12 (a - b)) = 1 := by rw [← proj_x12_mul_inv, h, mul_inv_cancel]
  have h2 := eq_one_of_mem_coordBlockSL_of_proj_eq_one (x12_mem_coordBlockSL (a - b)) h1
  have h3 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 2) h2
  simp [x12, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply] at h3
  exact sub_eq_zero.1 h3

theorem zpow_apply_eq_of_apply_eq {σ : K ≃+* K} {x : K} (hx : σ x = x) (k : ℤ) : (σ ^ k) x = x := by
  have hx' : σ⁻¹ x = x := by
    rw [RingAut.inv_apply, RingEquiv.symm_apply_eq]
    exact hx.symm
  induction k using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [_root_.zpow_add_one, RingAut.mul_apply, hx, ih]
  | pred n ih => rw [_root_.zpow_sub_one, RingAut.mul_apply, hx', ih]

variable (hp : p.Prime) (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot (lam ^ 3) p)
include hp hp2 hζ

theorem zpowers_rE_inf_zpowers_tE :
    Subgroup.zpowers (rE hp hζ) ⊓ Subgroup.zpowers (tE hp hζ) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_inf.1 hx).1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_bot]
  have hx1 : (MulAut.conj (tE hp hζ ^ j)) (proj 3 K (x12 1)) = proj 3 K (x12 1) := by
    rw [hj, ← hi, MulAut.conj_apply]
    have hc : Commute (rE hp hζ ^ i) (proj 3 K (x12 1)) :=
      Commute.zpow_left (rE_commute_J3 hp hζ (Subgroup.mem_map_of_mem _ (x12_mem_coordBlockSL 1))) i
    rw [hc.eq, mul_inv_cancel_right]
  rw [map_zpow, conj_tE_zpow_x12] at hx1
  have h2 : (lam ^ 3) ^ (2 * j) = 1 := by
    have := eq_of_proj_x12_eq hx1
    rwa [mul_one] at this
  have hdvd : (p : ℤ) ∣ 2 * j := (hζ.zpow_eq_one_iff_dvd (2 * j)).1 h2
  have hpj : (p : ℤ) ∣ j := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rcases hpz.dvd_or_dvd hdvd with h | h
    · exfalso
      have : p ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
      exact hp2 this
    · exact h
  have htord : orderOf (tE hp hζ) = p := orderOf_eq_prime (tE_pow hp hζ) (tE_ne_one hp hζ)
  rw [← hj]
  exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [htord]; exact hpj)

theorem isElemAbelian_card_R :
    IsElemAbelian p (Subgroup.zpowers (rE hp hζ) ⊔ Subgroup.zpowers (tE hp hζ)) ∧
      Nat.card ↥(Subgroup.zpowers (rE hp hζ) ⊔ Subgroup.zpowers (tE hp hζ)) = p ^ 2 :=
  isElemAbelian_card_zpowers_sup hp (rE_tE_commute hp hζ) (rE_pow hp hζ) (tE_pow hp hζ)
    (rE_ne_one hp hζ) (tE_ne_one hp hζ) (zpowers_rE_inf_zpowers_tE hp hp2 hζ)

variable (hF : 4 ≤ Nat.card K) {σ : K ≃+* K} (hζσ : σ (lam ^ 3) = lam ^ 3)
include hF hζσ

theorem centMod_R (k : ℤ) (s : projectiveSL 3 K)
    (hs : s ∈ Subgroup.zpowers (rE hp hζ) ⊔ Subgroup.zpowers (tE hp hζ))
    (h : ∀ j ∈ J3 K, (fieldAut 3 K σ ^ k * MulAut.conj s) j * j⁻¹ ∈ GLAPPrimeCoreOf p (J3 K)) :
    fieldAut 3 K σ ^ k = 1 ∧ s ∈ Subgroup.zpowers (rE hp hζ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq := isQuasisimple_J3 hp hp2 hζ hF
  have hdvd := dvd_card_J3 (F := K) hp hp2 hζ
  have hJ1 : proj 3 K (x21 1) ∈ J3 K := Subgroup.mem_map_of_mem _ (x21_mem_coordBlockSL 1)
  have hJc : ∀ c : K, proj 3 K (x12 c) ∈ J3 K := fun c =>
    Subgroup.mem_map_of_mem _ (x12_mem_coordBlockSL c)
  have hfk : ∀ c : K, (fieldAut 3 K σ ^ k) (proj 3 K (x12 c)) = proj 3 K (x12 ((σ ^ k) c)) := by
    intro c
    rw [← map_zpow, fieldAut_proj_x12]
  obtain ⟨i, j, rfl⟩ := exists_of_mem_zpowers_sup' (rE_tE_commute hp hζ) hs
  have hri : ∀ y ∈ J3 K, MulAut.conj (rE hp hζ ^ i) y = y := by
    intro y hy
    rw [MulAut.conj_apply, (Commute.zpow_left (rE_commute_J3 hp hζ hy) i).eq, mul_inv_cancel_right]
  have hconj : ∀ c : K, MulAut.conj (rE hp hζ ^ i * tE hp hζ ^ j) (proj 3 K (x12 c)) =
      proj 3 K (x12 ((lam ^ 3) ^ (2 * j) * c)) := by
    intro c
    rw [map_mul, MulAut.mul_apply, map_zpow (MulAut.conj) (tE hp hζ) j, conj_tE_zpow_x12]
    exact hri _ (hJc _)
  have h1 := h _ (hJc 1)
  have hζ2 : σ ((lam ^ 3) ^ (2 * j) * 1) = (lam ^ 3) ^ (2 * j) * 1 := by
    rw [map_mul, map_zpow₀, hζσ, map_one]
  rw [MulAut.mul_apply, hconj, hfk, zpow_apply_eq_of_apply_eq hζ2 k, proj_x12_mul_inv] at h1
  have h2 := commute_of_mem_glaPPrimeCoreOf hp hq hdvd h1 hJ1
  have h3 : (lam ^ 3) ^ (2 * j) = 1 := by
    have := sub_eq_zero.1 (eq_zero_of_proj_x12_commute h2)
    rwa [mul_one] at this
  have hdvd2 : (p : ℤ) ∣ 2 * j := (hζ.zpow_eq_one_iff_dvd (2 * j)).1 h3
  have hpj : (p : ℤ) ∣ j := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rcases hpz.dvd_or_dvd hdvd2 with h' | h'
    · exfalso
      have : p ∣ 2 := by exact_mod_cast h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · exact h'
  have htord : orderOf (tE hp hζ) = p := orderOf_eq_prime (tE_pow hp hζ) (tE_ne_one hp hζ)
  have htj : tE hp hζ ^ j = 1 :=
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [htord]; exact hpj)
  rw [htj, mul_one]
  refine ⟨?_, Subgroup.zpow_mem_zpowers _ i⟩
  have hσk : σ ^ k = 1 := by
    ext c
    have h4 := h _ (hJc c)
    rw [htj, mul_one, MulAut.mul_apply, hri _ (hJc c), hfk, proj_x12_mul_inv] at h4
    have h5 := commute_of_mem_glaPPrimeCoreOf hp hq hdvd h4 hJ1
    exact sub_eq_zero.1 (eq_zero_of_proj_x12_commute h5)
  rw [← map_zpow, hσk, map_one]

end Main

section Fixed

variable [Finite K] (σ : K ≃+* K)

noncomputable abbrev incl0 : SpecialLinearGroup (Fin 3) (semilinearFixedSubfield σ) →*
    SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.map (semilinearFixedSubfield σ).subtype

theorem incl0_injective : Function.Injective (incl0 σ) := by
  intro g g' hgg'
  refine Subtype.ext (Matrix.ext fun a b => Subtype.val_injective ?_)
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) a b) hgg'
  simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h1

theorem incl0_mem_coordBlockSL {g : SpecialLinearGroup (Fin 3) (semilinearFixedSubfield σ)}
    (hg : g ∈ coordBlockSL (semilinearFixedSubfield σ) blk) : incl0 σ g ∈ coordBlockSL K blk := by
  rw [mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  have h1 := hg i j hij
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    h1]
  split_ifs <;> simp

noncomputable abbrev L0 : Subgroup (projectiveSL 3 K) :=
  ((coordBlockSL (semilinearFixedSubfield σ) blk).map (incl0 σ)).map (proj 3 K)

theorem B0_le : (coordBlockSL (semilinearFixedSubfield σ) blk).map (incl0 σ) ≤ coordBlockSL K blk := by
  rintro _ ⟨g, hg, rfl⟩
  exact incl0_mem_coordBlockSL σ hg

theorem J3_inf_fixSubgroup_eq : J3 K ⊓ fixSubgroup (fieldAut 3 K σ) = L0 σ := by
  have hk : ∀ x : K, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => Iff.rfl
  apply le_antisymm
  · rintro x ⟨⟨g, hg, rfl⟩, hfix0⟩
    have hfix : fieldAut 3 K σ (proj 3 K g) = proj 3 K g := hfix0
    rw [fieldAut_proj, proj_eq_proj_iff] at hfix
    obtain ⟨c, -, hc⟩ := mem_scalars.1 hfix
    have hrel : g = Matrix.SpecialLinearGroup.map σ.toRingHom g *
        ((Matrix.SpecialLinearGroup.map σ.toRingHom g)⁻¹ * g) := by group
    have hmat : (g : Matrix (Fin 3) (Fin 3) K) =
        ((Matrix.SpecialLinearGroup.map σ.toRingHom g : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
      conv_lhs => rw [hrel]
      rw [Matrix.SpecialLinearGroup.coe_mul, hc]
    have h00 := congrFun (congrFun hmat 0) 0
    rw [Matrix.SpecialLinearGroup.map_apply_coe, scalar_apply, mul_diagonal, RingHom.mapMatrix_apply,
      Matrix.map_apply, corner_of_mem_coordBlockSL hg, map_one, one_mul] at h00
    have hent : ∀ a b, σ ((g : Matrix (Fin 3) (Fin 3) K) a b) = (g : Matrix (Fin 3) (Fin 3) K) a b := by
      intro a b
      have h1 := congrFun (congrFun hmat a) b
      rw [Matrix.SpecialLinearGroup.map_apply_coe, scalar_apply, mul_diagonal, RingHom.mapMatrix_apply,
        Matrix.map_apply, ← h00, mul_one] at h1
      exact h1.symm
    let g₀ : Matrix (Fin 3) (Fin 3) (semilinearFixedSubfield σ) :=
      Matrix.of fun a b => ⟨_, (hk _).2 (hent a b)⟩
    have hg₀ : g₀.map (semilinearFixedSubfield σ).subtype = g := Matrix.ext fun _ _ => rfl
    have hdet : g₀.det = 1 := Subtype.val_injective (by
      change (semilinearFixedSubfield σ).subtype g₀.det = (semilinearFixedSubfield σ).subtype 1
      rw [RingHom.map_det, map_one]
      change (g₀.map (semilinearFixedSubfield σ).subtype).det = 1
      rw [hg₀]
      exact g.2)
    let g₁ : SpecialLinearGroup (Fin 3) (semilinearFixedSubfield σ) := ⟨g₀, hdet⟩
    have hg₀B : g₁ ∈ coordBlockSL (semilinearFixedSubfield σ) blk := by
      have hg2 := mem_coordBlockSL_iff.1 hg
      rw [mem_coordBlockSL_iff]
      intro i j hij
      apply Subtype.val_injective
      change (g : Matrix (Fin 3) (Fin 3) K) i j = _
      rw [hg2 i j hij]
      split_ifs <;> rfl
    have hg₁ : incl0 σ g₁ = g := Subtype.ext hg₀
    exact ⟨incl0 σ g₁, ⟨g₁, hg₀B, rfl⟩, by rw [hg₁]⟩
  · rintro _ ⟨_, ⟨g₀, hg₀, rfl⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ (incl0_mem_coordBlockSL σ hg₀), ?_⟩
    show fieldAut 3 K σ (proj 3 K (incl0 σ g₀)) = proj 3 K (incl0 σ g₀)
    rw [fieldAut_proj]
    congr 1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact ((g₀ : Matrix (Fin 3) (Fin 3) (semilinearFixedSubfield σ)) i j).2

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lam : K} (hζ : IsPrimitiveRoot (lam ^ 3) p)
  (hζσ : σ (lam ^ 3) = lam ^ 3) (h4 : 4 ≤ Nat.card (semilinearFixedSubfield σ))
include hp hp2 hζ hζσ h4

theorem glaPLayer_J3_inf_fixSubgroup_ne_bot :
    GLAPLayer p (J3 K ⊓ fixSubgroup (fieldAut 3 K σ)) ≠ ⊥ := by
  set B := (coordBlockSL (semilinearFixedSubfield σ) blk).map (incl0 σ) with hB
  have e1 : ↥(coordBlockSL (semilinearFixedSubfield σ) blk) ≃* ↥B :=
    Subgroup.equivMapOfInjective _ (incl0 σ) (incl0_injective σ)
  have e2 : ↥B ≃* ↥(L0 σ) := mapProjEquiv B (B0_le σ)
  have hζ₀ : IsPrimitiveRoot (⟨lam ^ 3, hζσ⟩ : semilinearFixedSubfield σ) p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := (semilinearFixedSubfield σ).subtype)
      Subtype.val_injective).1 hζ
  have hq0 : CFSG.Open.IsQuasisimple ↥(coordBlockSL (semilinearFixedSubfield σ) blk) :=
    isQuasisimple_coordBlockSL (J := blk) (by decide) h4
  have hq : CFSG.Open.IsQuasisimple ↥(L0 σ) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv (e1.trans e2).symm hq0
  have hdvd : p ∣ Nat.card (↥(L0 σ) ⧸ Subgroup.center ↥(L0 σ)) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.natCard_quotient_center_congr (e1.trans e2)]
    exact dvd_card_coordBlockSL_blk hp hp2 hζ₀
  rw [J3_inf_fixSubgroup_eq σ]
  refine CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp le_rfl ?_ hq hdvd
  rw [Subgroup.subgroupOf_self]
  infer_instance

end Fixed

section Assembly

variable [Finite K]

theorem uE_sq : (uE : projectiveSL 3 K) ^ 2 = 1 := by
  rw [uE, ← map_pow, proj_eq_one_iff]
  refine ⟨1, one_pow 3, ?_⟩
  rw [coe_diag3_pow]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, scalar_apply, diagonal_apply_eq, Pi.pow_apply, Units.val_one]
    fin_cases i <;> simp
  · rw [diagonal_apply_ne _ hij, scalar_apply, diagonal_apply_ne _ hij]

theorem uE_ne_one (h2K : (2 : K) ≠ 0) : (uE : projectiveSL 3 K) ≠ 1 := by
  intro h
  have h01 := eq_of_proj_diag3_eq_one _ h 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h01
  apply h2K
  linear_combination h01

theorem uE_commute_J3 {x : projectiveSL 3 K} (hx : x ∈ J3 K) : x * uE = uE * x := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hgc := coordBlockSL_le_centralizer_diag3 (d := ![1, -1, -1]) (hd := prod_du) rfl hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  rw [uE, ← map_mul, ← map_mul, hgc]

theorem z1AutData_fieldAut {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h2K : (2 : K) ≠ 0)
    (hF : 4 ≤ Nat.card K) {σ : K ≃+* K} (h4 : 4 ≤ Nat.card (semilinearFixedSubfield σ))
    {lam : K} (hζ : IsPrimitiveRoot (lam ^ 3) p) (hζσ : σ (lam ^ 3) = lam ^ 3) :
    Z1AutData p (projectiveSL 3 K) (fieldAut 3 K σ) := by
  have h0 := lam_ne_zero hp hζ
  have h01 : (![(lam ^ 2)⁻¹, lam, lam] : Fin 3 → K) 0 ≠ ![(lam ^ 2)⁻¹, lam, lam] 1 := by
    intro h
    have h' : (lam ^ 2)⁻¹ = lam := h
    apply zeta_ne_one hp hζ
    calc lam ^ 3 = lam ^ 2 * lam := by ring
      _ = lam ^ 2 * (lam ^ 2)⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 h0)
  have hJ : GLAPLayer p (Subgroup.centralizer ({rE hp hζ} : Set (projectiveSL 3 K))) = J3 K :=
    glaPLayer_centralizer_proj_diag3 hp hp2 hζ hF (prod_dr h0) rfl h01
  obtain ⟨hRel, hRcard⟩ := isElemAbelian_card_R hp hp2 hζ
  have hRu : ∀ s ∈ Subgroup.zpowers (rE hp hζ) ⊔ Subgroup.zpowers (tE hp hζ), s * uE = uE * s := by
    intro s hs
    obtain ⟨i, j, rfl⟩ := exists_of_mem_zpowers_sup' (rE_tE_commute hp hζ) hs
    have h1 : Commute (rE hp hζ ^ i) uE := Commute.zpow_left (rE_uE_commute hp hζ) i
    have h2 : Commute (tE hp hζ ^ j) uE := Commute.zpow_left (tE_uE_commute hp hζ) j
    exact (h1.mul_left h2).eq
  refine ⟨Subgroup.zpowers (rE hp hζ) ⊔ Subgroup.zpowers (tE hp hζ), hRel, hRcard, ?_, rE hp hζ,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _), rE_ne_one hp hζ, ?_, ?_, ?_,
    ⟨Subgroup.zpowers uE, ?_, ?_, ?_, ?_⟩, uE, uE_ne_one h2K, uE_sq, (rE_uE_commute hp hζ).symm, ?_⟩
  · intro s hs
    obtain ⟨i, j, rfl⟩ := exists_of_mem_zpowers_sup' (rE_tE_commute hp hζ) hs
    rw [map_mul, map_zpow, map_zpow, rE_fix hp hζ hζσ, tE_fix hp hζ hζσ]
  · rw [hJ]
    exact glaPComponent_centralizer_proj_diag3 hp hp2 hζ hF (prod_dr h0) rfl h01
  · intro k s hs hjs
    rw [hJ] at hjs
    exact centMod_R hp hp2 hζ hF hζσ k s hs hjs
  · rw [hJ]
    exact glaPLayer_J3_inf_fixSubgroup_ne_bot σ hp hp2 hζ hζσ h4
  · intro h
    apply uE_ne_one h2K
    have : uE ∈ Subgroup.zpowers (uE : projectiveSL 3 K) := Subgroup.mem_zpowers _
    rw [h] at this
    exact this
  · intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, uE_sq, _root_.one_zpow, Subgroup.coe_one]
  · rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (uE_fix (σ := σ))
  · intro s hs
    refine CFSG.LocalAnalysis.GLTheoremA.H81.normalizer_of_commute fun a ha => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (Commute.zpow_right (hRu s hs) n).eq
  · intro j hj
    rw [hJ] at hj
    exact uE_commute_J3 hj

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin

end
