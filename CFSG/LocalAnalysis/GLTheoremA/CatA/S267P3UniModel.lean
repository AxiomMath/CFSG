module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FormModel
public import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UNorm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S267.P3
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section General

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def suOn (ι : Type) [Fintype ι] [DecidableEq ι] :
    Subgroup (SpecialLinearGroup ι K) where
  carrier := {g | ((g : Matrix ι ι K).map σ)ᵀ * (g : Matrix ι ι K) = 1}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at hg hh ⊢
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (g : Matrix ι ι K), hg, Matrix.one_mul, hh]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.one_mul]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hgi : (g : Matrix ι ι K) * ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hinv : ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) =
        ((g : Matrix ι ι K).map σ)ᵀ := by
      calc ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K)
          = (((g : Matrix ι ι K).map σ)ᵀ * (g : Matrix ι ι K)) *
              ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) := by rw [hg, Matrix.one_mul]
        _ = ((g : Matrix ι ι K).map σ)ᵀ := by rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
    rw [hinv, Matrix.transpose_map, Matrix.transpose_transpose]
    have h1 := congrArg (fun M : Matrix ι ι K => M.map σ) hg
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_map] at h1
    have h2 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h2
    exact mul_eq_one_comm.1 h2

variable {σ}

theorem mem_suOn {ι : Type} [Fintype ι] [DecidableEq ι] {g : SpecialLinearGroup ι K} :
    g ∈ suOn σ ι ↔ ((g : Matrix ι ι K).map σ)ᵀ * (g : Matrix ι ι K) = 1 :=
  Iff.rfl

theorem blk_mem_suOn_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : SpecialLinearGroup (Fin 2) K) (Y : SpecialLinearGroup ι K) :
    blk ι (P, Y) ∈ suOn σ (Fin 2 ⊕ ι) ↔ P ∈ suOn σ (Fin 2) ∧ Y ∈ suOn σ ι := by
  rw [mem_suOn, mem_suOn, mem_suOn, coe_blk, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp only [Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  constructor
  · intro h
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 h
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h4⟩
    rw [h1, h4]

theorem reindex_unitary {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι K) :
    ((reindex e e A).map σ)ᵀ * reindex e e A = reindex e e ((A.map σ)ᵀ * A) := by
  simp only [reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv]

@[expose] noncomputable def toGLReindex {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : ι ≃ Fin m) : SpecialLinearGroup ι K →* GL (Fin m) K :=
  Matrix.SpecialLinearGroup.toGL.comp (slReindex (F := K) e).toMonoidHom

theorem coe_toGLReindex {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (e : ι ≃ Fin m)
    (g : SpecialLinearGroup ι K) :
    ((toGLReindex e g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      reindex e e (g : Matrix ι ι K) := rfl

theorem toGLReindex_injective {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (e : ι ≃ Fin m) :
    Function.Injective (toGLReindex (K := K) e) := fun g h hgh =>
  Subtype.ext ((reindex e e).injective (by
    rw [← coe_toGLReindex, ← coe_toGLReindex, hgh]))

theorem map_suOn {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (e : ι ≃ Fin m) :
    (suOn σ ι).map (toGLReindex e) = SUid σ m := by
  ext B
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [coe_toGLReindex, det_reindex_self]
      exact g.2
    · change ((reindex e e (g : Matrix ι ι K)).map σ)ᵀ * reindex e e (g : Matrix ι ι K) = 1
      rw [reindex_unitary, mem_suOn.1 hg, reindex_apply, submatrix_one_equiv]
  · intro hB
    obtain ⟨hdet, hu⟩ := mem_SUid.1 hB
    set g : SpecialLinearGroup ι K := ⟨reindex e.symm e.symm (B : Matrix (Fin m) (Fin m) K), by
      rw [det_reindex_self]
      exact hdet⟩
    refine ⟨g, ?_, Units.ext ?_⟩
    · rw [SetLike.mem_coe, mem_suOn]
      change ((reindex e.symm e.symm (B : Matrix (Fin m) (Fin m) K)).map σ)ᵀ *
        reindex e.symm e.symm (B : Matrix (Fin m) (Fin m) K) = 1
      rw [reindex_unitary]
      change reindex e.symm e.symm (conjTr σ (B : Matrix (Fin m) (Fin m) K) *
        (B : Matrix (Fin m) (Fin m) K)) = 1
      rw [hu, reindex_apply, submatrix_one_equiv]
    · rw [coe_toGLReindex]
      change reindex e e (reindex e.symm e.symm (B : Matrix (Fin m) (Fin m) K)) = _
      simp

@[expose] noncomputable def suOnEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : ι ≃ Fin m) : ↥(suOn σ ι) ≃* ↥(SUid σ m) :=
  ((suOn σ ι).equivMapOfInjective _ (toGLReindex_injective e)).trans
    (MulEquiv.subgroupCongr (map_suOn e))

theorem map_center_suOnEquiv {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
    (e : ι ≃ Fin m) {H : Subgroup (GL (Fin m) K)} (hS : SUid σ m = H) :
    ((Subgroup.center (SpecialLinearGroup ι K)).subgroupOf (suOn σ ι)).map
        ((suOnEquiv e).trans (MulEquiv.subgroupCongr hS) : ↥(suOn σ ι) →* ↥H) =
      (StatedScalars (Fin m) K).subgroupOf H := by
  set E := (suOnEquiv e).trans (MulEquiv.subgroupCongr hS) with hEdef
  have hE : ∀ x : ↥(suOn σ ι), (((E x : ↥H) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      reindex e e ((x : SpecialLinearGroup ι K) : Matrix ι ι K) := fun x => rfl
  have key : ∀ x : ↥(suOn σ ι), E x ∈ (StatedScalars (Fin m) K).subgroupOf H ↔
      x ∈ (Subgroup.center (SpecialLinearGroup ι K)).subgroupOf (suOn σ ι) := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range,
      Matrix.SpecialLinearGroup.mem_center_iff]
    constructor
    · rintro ⟨u, hu⟩
      have hu' : Matrix.scalar (Fin m) (u : K) =
          reindex e e ((x : SpecialLinearGroup ι K) : Matrix ι ι K) := by
        rw [← hE, ← hu]
        rfl
      have hx : ((x : SpecialLinearGroup ι K) : Matrix ι ι K) = Matrix.scalar ι (u : K) := by
        have h1 : ((x : SpecialLinearGroup ι K) : Matrix ι ι K) =
            (reindex e e).symm (Matrix.scalar (Fin m) (u : K)) := by
          rw [hu', Equiv.symm_apply_apply]
        rw [h1, reindex_symm]
        ext i j
        simp [Matrix.scalar_apply, Matrix.diagonal_apply]
      refine ⟨u, ?_, hx.symm⟩
      have hdet := (x : SpecialLinearGroup ι K).2
      rw [hx] at hdet
      simpa [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
        using hdet
    · rintro ⟨r, hr, hrx⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow Fintype.card_ne_zero] at hr
        exact zero_ne_one hr
      refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, hE, ← hrx]
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine ⟨E.symm y, (key _).1 (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    exact MulEquiv.apply_symm_apply E y

variable (σ) in
@[expose] def cU (a b : K) (h : a * a - b * -σ b = 1) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![a, b; -σ b, a], by rw [Matrix.det_fin_two_of]; exact h⟩

variable (σ) in
@[expose] def wU (l : K) (h : l * σ l - 0 * 0 = 1) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![l, 0; 0, σ l], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem cU_det {a b : K} (hb : σ b * b = 1 - a * a) : a * a - b * -σ b = 1 := by
  linear_combination hb

theorem wU_det {l : K} (hl : σ l * l = 1) : l * σ l - 0 * 0 = 1 := by
  linear_combination hl

theorem cU_mem {a b : K} (hσa : σ a = a) (hσσ : σ (σ b) = b) (hb : σ b * b = 1 - a * a) :
    cU σ a b (cU_det hb) ∈ suOn σ (Fin 2) := by
  rw [mem_suOn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cU, Matrix.mul_apply, Fin.sum_univ_two, hσa, hσσ] <;>
    first | ring1 | linear_combination hb

theorem cU_rel {a b : K} (ha : 2 * a + 1 = 0) (hb : σ b * b = 1 - a * a) :
    (cU σ a b (cU_det hb) : Matrix (Fin 2) (Fin 2) K) * cU σ a b (cU_det hb) +
      cU σ a b (cU_det hb) + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cU, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination a * ha - hb
  · simp [cU, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination b * ha
  · simp [cU, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-σ b) * ha
  · simp [cU, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination a * ha - hb

theorem wU_mem {l : K} (hσσ : σ (σ l) = l) (hl : σ l * l = 1) :
    wU σ l (wU_det hl) ∈ suOn σ (Fin 2) := by
  rw [mem_suOn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wU, Matrix.mul_apply, Fin.sum_univ_two, hσσ] <;>
    first | ring1 | linear_combination hl

theorem cU_mul_wU_ne {a b l : K} (ha : 2 * a + 1 = 0) (hb : σ b * b = 1 - a * a)
    (hl : σ l * l = 1) (hl2 : l ^ 2 ≠ 1) (h3 : (3 : K) ≠ 0) :
    cU σ a b (cU_det hb) * wU σ l (wU_det hl) ≠ wU σ l (wU_det hl) * cU σ a b (cU_det hb) := by
  intro h
  have h01 : b * σ l = l * b := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    change (HMul.hMul (!![a, b; -σ b, a] : Matrix (Fin 2) (Fin 2) K)
        (!![l, 0; 0, σ l] : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (HMul.hMul (!![l, 0; 0, σ l] : Matrix (Fin 2) (Fin 2) K)
        (!![a, b; -σ b, a] : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 at this
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply h3
    have e2 : (0 : K) = 1 - a * a := by simpa using hb
    linear_combination (2 * a - 1) * ha - 4 * e2
  have hσl : σ l = l := by
    have : b * (σ l - l) = 0 := by linear_combination h01
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hb0)
  apply hl2
  rw [sq]
  rw [hσl] at hl
  exact hl

variable (σ) in
theorem negOne_mem_suOn : negOne ∈ suOn σ (Fin 2) := by
  rw [mem_suOn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negOne, Matrix.mul_apply, Fin.sum_univ_two]

end General

section Field

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_norm_one_sq_ne_one (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) :
    ∃ l : K, unitaryInvolution K p f l * l = 1 ∧ l ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul]
    have : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
      have h1 : 1 ≤ p ^ f := by omega
      zify [h1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
      ring
    rw [this, ← hord, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h1 : g ^ ((p ^ f - 1) * 2) = 1 := Units.ext (by
      rw [pow_mul, Units.val_pow_eq_pow_val, h, Units.val_one])
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 : (p ^ f) ^ 2 - 1 ≤ (p ^ f - 1) * 2 := Nat.le_of_dvd (by omega) h2
    have h4 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    zify [h4, (by omega : 1 ≤ p ^ f)] at h3
    nlinarith

theorem exists_norm_eq_of_fixed (hK : Nat.card K = (p ^ f) ^ 2) {c : K}
    (hc : unitaryInvolution K p f c = c) (hc0 : c ≠ 0) :
    ∃ b : K, unitaryInvolution K p f b * b = c := by
  obtain ⟨b, hb⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.exists_norm_eq hK
    (by rw [← unitaryInvolution_apply]; exact hc) hc0
  exact ⟨b, by rw [unitaryInvolution_apply]; exact hb⟩

end Field

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def uniData (hK : Nat.card K = (p ^ f) ^ 2) (ν : Type) [Fintype ν]
    [DecidableEq ν] {a b l : K} (ha : 2 * a + 1 = 0) (hσa : unitaryInvolution K p f a = a)
    (hb : unitaryInvolution K p f b * b = 1 - a * a) (hl : unitaryInvolution K p f l * l = 1)
    (hl2 : l ^ 2 ≠ 1) (h3 : (3 : K) ≠ 0) : FormData K ν where
  G2 := suOn (unitaryInvolution K p f) (Fin 2)
  Gl := suOn (unitaryInvolution K p f) (Lam ν)
  Gk := suOn (unitaryInvolution K p f) (Kap ν)
  Gt := suOn (unitaryInvolution K p f) (Lin.Top ν)
  blk_top P hP Y hY := (blk_mem_suOn_iff P Y).2 ⟨hP, hY⟩
  blk_kap P hP R hR := (blk_mem_suOn_iff P R).2 ⟨hP, hR⟩
  blk_lam P hP := (blk_mem_suOn_iff P 1).2 ⟨hP, one_mem _⟩
  top_inv Y h := ((blk_mem_suOn_iff 1 Y).1 h).2
  kap_inv R h := ((blk_mem_suOn_iff 1 R).1 h).2
  c := cU (unitaryInvolution K p f) a b (cU_det hb)
  c_mem := cU_mem hσa (unitaryInvolution_involutive hK b) hb
  c_rel := cU_rel ha hb
  w := wU (unitaryInvolution K p f) l (wU_det hl)
  w_mem := wU_mem (unitaryInvolution_involutive hK l) hl
  c_mul_w := cU_mul_wU_ne ha hb hl hl2 h3
  negOne_mem := negOne_mem_suOn _

theorem isQuasisimple_suOn (hK : Nat.card K = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 2 ≤ Fintype.card ι) :
    CFSG.Open.IsQuasisimple ↥(suOn (unitaryInvolution K p f) ι) := by
  have h := CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.isQuasisimple_su_of_two_le
    (K := K) (p := p) (f := f) hK h5 hι
  have h' : CFSG.Open.IsQuasisimple
      (CFSG.ClassicalInvolution.Phan.Su K p f (Fintype.card ι)) :=
    ⟨Group.isPerfect_def.1 h.1, h.2.1⟩
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (suOnEquiv (Fintype.equivFin ι)) h'

theorem noThree_uniData (hK : Nat.card K = (p ^ f) ^ 2) (ν : Type) [Fintype ν]
    [DecidableEq ν] {a b l : K} (ha : 2 * a + 1 = 0) (hσa : unitaryInvolution K p f a = a)
    (hb : unitaryInvolution K p f b * b = 1 - a * a) (hl : unitaryInvolution K p f l * l = 1)
    (hl2 : l ^ 2 ≠ 1) (h3 : (3 : K) ≠ 0) (h31 : 3 ∣ p ^ f - 1) :
    ∀ z ∈ (uniData hK ν ha hσa hb hl hl2 h3).Zt, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  have hc := Subgroup.mem_subgroupOf.1 hz
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hu := mem_suOn.1 z.2
  have hzr : (((z : SpecialLinearGroup (Lin.Top ν) K)) : Matrix (Lin.Top ν) (Lin.Top ν) K) =
      Matrix.scalar (Lin.Top ν) r := hr.symm
  rw [hzr] at hu
  have hnorm : unitaryInvolution K p f r * r = 1 := by
    have := congrFun (congrFun hu (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply] using this
  have hr3 : r ^ 3 = 1 := by
    have h1 : (((z : SpecialLinearGroup (Lin.Top ν) K)) : Matrix (Lin.Top ν) (Lin.Top ν) K) ^ 3 =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← Subgroup.coe_pow, hz3]
      rfl
    rw [hzr, ← map_pow] at h1
    have := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this
  rw [unitaryInvolution_apply, ← pow_succ] at hnorm
  obtain ⟨k, hk⟩ := h31
  have hQ1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hQ : p ^ f + 1 = 3 * k + 2 := by omega
  rw [hQ, pow_add, pow_mul, hr3, one_pow, one_mul] at hnorm
  have hr1 : r = 1 := by
    have : r ^ 3 = r ^ 2 * r := pow_succ r 2
    rw [hr3, hnorm, one_mul] at this
    exact this.symm
  apply Subtype.ext
  apply Subtype.ext
  rw [hzr, hr1, map_one]
  rfl

@[expose] noncomputable def projEquiv (hK : Nat.card K = (p ^ f) ^ 2) (ν : Type) [Fintype ν]
    [DecidableEq ν] {a b l : K} (ha : 2 * a + 1 = 0) (hσa : unitaryInvolution K p f a = a)
    (hb : unitaryInvolution K p f b * b = 1 - a * a) (hl : unitaryInvolution K p f l * l = 1)
    (hl2 : l ^ 2 ≠ 1) (h3 : (3 : K) ≠ 0) {m : ℕ} (e : Lin.Top ν ≃ Fin m) :
    (uniData hK ν ha hσa hb hl hl2 h3).XD ≃* StatedProj (StatedSU m (p ^ f) K) :=
  QuotientGroup.congr _ _ ((suOnEquiv e).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK m)))
    (map_center_suOnEquiv e (SUid_eq_statedSU hK m))

end Model

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni

end
