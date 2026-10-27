module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292LBasis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292L

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292

variable {K : Type} [Field K]

section LinAlg

theorem exists_mulVec_eq_smul_of_commute {b : Fin 3 → Fin 3 → K} (hb : IsUnit (colMat b))
    {x g : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} (hd : Function.Injective d)
    (hx : ∀ i, x *ᵥ b i = d i • b i) (hgx : g * x = x * g) (i : Fin 3) :
    ∃ c : K, g *ᵥ b i = c • b i := by
  have hPd : IsUnit (colMat b).det := (Matrix.isUnit_iff_isUnit_det _).mp hb
  obtain ⟨a, hPa⟩ : ∃ a : Fin 3 → K, colMat b *ᵥ a = g *ᵥ b i :=
    ⟨(colMat b)⁻¹ *ᵥ (g *ᵥ b i), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPd, Matrix.one_mulVec]⟩
  have hxP : x * colMat b = colMat b * diagonal d := mul_colMat_eq hx
  have hxu : x *ᵥ (g *ᵥ b i) = d i • (g *ᵥ b i) := by
    rw [Matrix.mulVec_mulVec, ← hgx, ← Matrix.mulVec_mulVec, hx i, Matrix.mulVec_smul]
  have key : diagonal d *ᵥ a = d i • a := by
    have h1 : colMat b *ᵥ (diagonal d *ᵥ a) = colMat b *ᵥ (d i • a) := by
      rw [Matrix.mulVec_mulVec, ← hxP, ← Matrix.mulVec_mulVec, hPa, hxu, Matrix.mulVec_smul,
        hPa]
    exact Matrix.mulVec_injective_iff_isUnit.2 hb h1
  have hak : ∀ k, k ≠ i → a k = 0 := by
    intro k hk
    have h := congrFun key k
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
    have hne : d k - d i ≠ 0 := sub_ne_zero.mpr fun h' => hk (hd h')
    have h0 : (d k - d i) * a k = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hne
  have ha : a = Pi.single i (a i) := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_apply, hk, hak k hk]
  refine ⟨a i, ?_⟩
  rw [← hPa, ← colMat_mulVec_single]
  exact congrArg (colMat b *ᵥ ·) ha

theorem exists_eigenbasis_injective {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0)
    {e : Matrix (Fin 3) (Fin 3) K} (he3 : e ^ 3 = 1) (hdet : e.det = 1)
    (hes : ∀ c : K, e ≠ c • 1) :
    ∃ b : Fin 3 → Fin 3 → K, IsUnit (colMat b) ∧ ∃ d : Fin 3 → K, Function.Injective d ∧
      ∀ i, e *ᵥ b i = d i • b i := by
  obtain ⟨b, hb, hk⟩ := exists_eigenbasis hτ hτ1 h3 he3
  choose k hk using hk
  have hu := isUnit_colMat hb
  have hed : e * colMat b = colMat b * diagonal (fun i => τ ^ (k i : ℕ)) := mul_colMat_eq hk
  have hprod : τ ^ (k 0 : ℕ) * τ ^ (k 1 : ℕ) * τ ^ (k 2 : ℕ) = 1 := by
    have h := congrArg Matrix.det hed
    rw [det_mul, det_mul, hdet, one_mul, det_diagonal, Fin.prod_univ_three] at h
    have hPd := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have h' : (colMat b).det * (τ ^ (k 0 : ℕ) * τ ^ (k 1 : ℕ) * τ ^ (k 2 : ℕ)) =
        (colMat b).det * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ hPd h'
  have hd3 : ∀ i, (τ ^ (k i : ℕ)) ^ 3 = 1 := fun i => by
    rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  have hscalar : τ ^ (k 0 : ℕ) = τ ^ (k 1 : ℕ) → τ ^ (k 1 : ℕ) = τ ^ (k 2 : ℕ) → False := by
    intro h01 h12
    apply hes (τ ^ (k 0 : ℕ))
    have hdiag : diagonal (fun i => τ ^ (k i : ℕ)) =
        τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact h01.symm
      · exact (h01.trans h12).symm
    rw [hdiag, Matrix.mul_smul, Matrix.mul_one] at hed
    apply hu.mul_left_inj.mp
    rw [hed, Matrix.smul_mul, Matrix.one_mul]
  have h01 : τ ^ (k 0 : ℕ) ≠ τ ^ (k 1 : ℕ) := by
    intro h
    refine hscalar h (h.symm.trans ?_)
    linear_combination τ ^ (k 2 : ℕ) * hd3 0 - τ ^ (k 0 : ℕ) * hprod -
      τ ^ (k 0 : ℕ) * τ ^ (k 0 : ℕ) * τ ^ (k 2 : ℕ) * h
  have h02 : τ ^ (k 0 : ℕ) ≠ τ ^ (k 2 : ℕ) := by
    intro h
    have h1 : τ ^ (k 1 : ℕ) = τ ^ (k 0 : ℕ) := by
      linear_combination (-(τ ^ (k 1 : ℕ))) * hd3 0 + τ ^ (k 0 : ℕ) * hprod +
        τ ^ (k 0 : ℕ) * τ ^ (k 0 : ℕ) * τ ^ (k 1 : ℕ) * h
    exact hscalar h1.symm (h1.trans h)
  have h12 : τ ^ (k 1 : ℕ) ≠ τ ^ (k 2 : ℕ) := by
    intro h
    have h0 : τ ^ (k 0 : ℕ) = τ ^ (k 1 : ℕ) := by
      linear_combination (-(τ ^ (k 0 : ℕ))) * hd3 1 + τ ^ (k 1 : ℕ) * hprod +
        τ ^ (k 0 : ℕ) * τ ^ (k 1 : ℕ) * τ ^ (k 1 : ℕ) * h
    exact hscalar h0 h
  refine ⟨b, hu, fun i => τ ^ (k i : ℕ), fun i j hij => ?_, hk⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij h01
  · exact absurd hij h02
  · exact absurd hij.symm h01
  · rfl
  · exact absurd hij h12
  · exact absurd hij.symm h02
  · exact absurd hij.symm h12
  · rfl

end LinAlg

section Members

variable {p f : ℕ}

theorem val_mul_comm_of_mem {E : Subgroup (GL (Fin 3) K)} (hE : IsMulCommutative ↥E)
    {g h : GL (Fin 3) K} (hg : g ∈ E) (hh : h ∈ E) :
    (g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) =
      (h : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
  have := isMulCommutative_iff.mp hE ⟨g, hg⟩ ⟨h, hh⟩
  rw [← Units.val_mul, ← Units.val_mul]
  exact congrArg (fun x : ↥E => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) this

theorem exists_not_eq_smul_one {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (GL (Fin 3) K)} (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcard : 3 < Nat.card E) :
    ∃ e ∈ E, ∀ c : K, (e : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
  by_contra hall
  push Not at hall
  have hroot : ∀ x ∈ E, ((x : Matrix (Fin 3) (Fin 3) K) 0 0) ^ 3 = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := hall x hx
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) (hE3 x hx)
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hc, smul_pow, one_pow] at h
    simpa [hc] using h
  have hne : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro x hx h0
    have := hroot x hx
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  have hle : Nat.card E ≤ Nat.card (rootsOfUnity 3 K) := by
    have := hK.finite
    refine Nat.card_le_card_of_injective
      (fun x : ↥E => (⟨Units.mk0 (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)
        (hne x x.2), by
          rw [mem_rootsOfUnity]
          exact Units.ext (by simp [hroot x x.2])⟩ : rootsOfUnity 3 K)) ?_
    intro x x' hxx'
    have h := congrArg (fun u : rootsOfUnity 3 K => ((u : Kˣ) : K)) hxx'
    simp only [Units.val_mk0] at h
    obtain ⟨c, hc⟩ := hall x x.2
    obtain ⟨c', hc'⟩ := hall x' x'.2
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc'] at h ⊢
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [h]
  rw [card_rootsOfUnity_three hK hq] at hle
  omega

theorem eq_threeFrame_of_mem_frameCands (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree true (p ^ f) K y) {E : Subgroup (GL (Fin 3) K)}
    (hE : E ∈ frameCands true (p ^ f) y) : ∃ v : Fin 3 → K, v ≠ 0 ∧ E = threeFrame y v := by
  obtain ⟨hESL, ⟨hEcomm, hE3⟩, hEcard, -, hEy⟩ := hE
  obtain ⟨ℓ, hy, hℓ⟩ := hT.not_cube hK hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hfin := hK.finite
  have : Finite (GL (Fin 3) K) := Finite.of_injective Units.val Units.val_injective
  obtain ⟨e, heE, hes⟩ := exists_not_eq_smul_one hK hq hE3 (by rw [hEcard]; norm_num)
  have he3 : (e : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hE3 e heE, Units.val_one]
  have hdet : (e : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_slPi_true _).1 (hESL heE)
  obtain ⟨b, hb, d, hd, hbd⟩ := exists_eigenbasis_injective hτ hτ1 h3 he3 hdet hes
  have he1E : y * e * y⁻¹ ∈ E := hEy e heE
  have he2E : y * (y * e * y⁻¹) * y⁻¹ ∈ E := hEy _ he1E
  have hb1 : IsUnit (colMat fun i => (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) :=
    isUnit_colMat_mulVec hb y.isUnit
  have hb2 : IsUnit (colMat fun i => (y : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i)) :=
    isUnit_colMat_mulVec hb1 y.isUnit
  have hbd1 : ∀ i, ((y * e * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) = d i • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) :=
    fun i => by rw [mulVec_conj, hbd i, Matrix.mulVec_smul]
  have hbd2 : ∀ i, ((y * (y * e * y⁻¹) * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i)) =
      d i • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i)) :=
    fun i => by rw [mulVec_conj, hbd1 i, Matrix.mulVec_smul]
  have hv : b 0 ≠ 0 := ne_zero_of_isUnit_colMat hb 0
  have hF := isUnit_colMat_yFrame hℓ hy hv
  have hF0 := ne_zero_of_isUnit_colMat hF
  have hframe : ∀ i, yFrame y (b 0) i = ![b 0, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0,
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0)] i := by
    intro i
    rw [yFrame_eq, Matrix.mulVec_mulVec, sq]
  have hle : E ≤ threeFrame y (b 0) := by
    intro g hg
    refine ⟨(mem_slPi_true _).1 (hESL hg), fun i => ?_⟩
    have hgv : ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y (b 0) i =
        c • yFrame y (b 0) i := by
      rw [hframe]
      fin_cases i
      · exact exists_mulVec_eq_smul_of_commute hb hd hbd
          (val_mul_comm_of_mem hEcomm hg heE) 0
      · exact exists_mulVec_eq_smul_of_commute hb1 hd hbd1
          (val_mul_comm_of_mem hEcomm hg he1E) 0
      · exact exists_mulVec_eq_smul_of_commute hb2 hd hbd2
          (val_mul_comm_of_mem hEcomm hg he2E) 0
    obtain ⟨c, hc⟩ := hgv
    exact ⟨c, pow_three_eq_one_of_mulVec_eq (hE3 g hg) (hF0 i) hc, hc⟩
  refine ⟨b 0, hv, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [hEcard]
  exact (card_frameGroupOf_three hK hq hF).le

end Members

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292L
