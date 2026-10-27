module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitCount

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {ε : ℕ}

@[expose] noncomputable def uMat (v : Fin ε → K) (c : K) :
    Matrix (HypIndex 1 ε) (HypIndex 1 ε) K :=
  blk3 1 (Matrix.of fun _ l => - h.bar (v l)) (Matrix.of fun _ _ => c) 1
    (Matrix.of fun k _ => v k) 1

theorem uMat_mul (v v' : Fin ε → K) (c c' : K) :
    uMat h v c * uMat h v' c' = uMat h (v + v') (c + c' - ∑ l, h.bar (v l) * v' l) := by
  rw [uMat, uMat, blk3_mul, uMat]
  congr 1
  · simp
  · ext i l
    simp [Matrix.add_apply, add_comm]
  · ext i j
    simp [Matrix.mul_apply, Matrix.add_apply, Finset.sum_neg_distrib]
    ring
  · simp
  · ext k j
    simp [Matrix.add_apply, add_comm]
  · simp

theorem uMat_zero : uMat h (0 : Fin ε → K) 0 = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    first
    | simp [uMat, one_apply, Subsingleton.elim i j]
    | simp [uMat, one_apply]

theorem det_uMat (v : Fin ε → K) (c : K) : (uMat h v c).det = 1 := by
  rw [uMat, det_blk3]
  simp

def UAdm (v : Fin ε → K) (c : K) : Prop := c + h.bar c = -∑ l, h.bar (v l) * v l

theorem uMat_gram {v : Fin ε → K} {c : K} (hc : UAdm h v c) :
    ((uMat h v c).map h.bar)ᵀ * hypGram 1 ε K * uMat h v c = hypGram 1 ε K := by
  rw [uMat, blk3_gram_iff]
  refine ⟨by simp, by simp, ?_, ?_⟩
  · ext l j
    simp [h.bar_bar]
  · ext i j
    have := hc
    simp only [UAdm] at this
    simp [Matrix.mul_apply, Matrix.add_apply, Subsingleton.elim i j]
    linear_combination this

@[expose] noncomputable def uElt (v : Fin ε → K) (c : K) (hc : UAdm h v c) : hypSU h 1 ε :=
  mkHypSU h (uMat h v c) (uMat_gram h hc) (det_uMat h v c)

theorem hypSU_ext {r : ℕ} {g g' : hypSU h r ε}
    (e : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) : g = g' :=
  Subtype.ext (Units.ext e)

structure UCtx (τ₀ : K) : Prop where
  bar_τ : h.bar τ₀ = -τ₀
  τ_ne : τ₀ ≠ 0
  two_ne : (2 : K) ≠ 0

variable {h}

theorem bar_fixed (y : h.fixedField) : h.bar (y : K) = y := y.2

theorem bar_two_inv : h.bar ((2 : K)⁻¹) = (2 : K)⁻¹ := by
  rw [map_inv₀, map_ofNat]

@[expose] def pv (x : UP h.fixedField ε) : Fin ε → K := fun l => ((x.1 l : h.fixedField) : K)

theorem bar_pv (x : UP h.fixedField ε) (l : Fin ε) : h.bar (pv x l) = pv x l := (x.1 l).2

@[expose] noncomputable def pc (τ₀ : K) (x : UP h.fixedField ε) : K :=
  ((x.2 : h.fixedField) : K) * τ₀ - 2⁻¹ * ∑ l, (pv x l) ^ 2

theorem pv_add (x y : UP h.fixedField ε) : pv (x + y) = pv x + pv y := by
  funext l
  simp [pv]

theorem pv_zero : pv (0 : UP h.fixedField ε) = 0 := by
  funext l
  simp [pv]

theorem pc_zero (τ₀ : K) : pc τ₀ (0 : UP h.fixedField ε) = 0 := by
  simp [pc, pv]

theorem pc_adm {τ₀ : K} (hc : UCtx h τ₀) (x : UP h.fixedField ε) :
    UAdm h (pv x) (pc τ₀ x) := by
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ hc.two_ne
  have hN : ∑ l, pv x l * pv x l = ∑ l, (pv x l) ^ 2 :=
    Finset.sum_congr rfl fun l _ => (sq _).symm
  unfold UAdm pc
  simp only [map_sub, map_mul, map_sum, map_pow, bar_pv, bar_two_inv, hc.bar_τ, bar_fixed]
  rw [hN]
  linear_combination (-(∑ l, (pv x l) ^ 2)) * h22

theorem pc_add {τ₀ : K} (hc : UCtx h τ₀) (x y : UP h.fixedField ε) :
    pc τ₀ (x + y) = pc τ₀ x + pc τ₀ y - ∑ l, h.bar (pv x l) * pv y l := by
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ hc.two_ne
  have e : ∑ l, (pv (x + y) l) ^ 2 =
      ∑ l, (pv x l) ^ 2 + ∑ l, (pv y l) ^ 2 + 2 * ∑ l, pv x l * pv y l := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [pv_add, Pi.add_apply]
    ring
  have e2 : ∑ l, h.bar (pv x l) * pv y l = ∑ l, pv x l * pv y l :=
    Finset.sum_congr rfl fun l _ => by rw [bar_pv]
  rw [e2]
  unfold pc
  rw [e]
  simp only [Subfield.coe_add, Prod.snd_add]
  linear_combination (-(∑ l, pv x l * pv y l)) * h22

@[expose] noncomputable def uPar {τ₀ : K} (hc : UCtx h τ₀) :
    Multiplicative (UP h.fixedField ε) →* hypSU h 1 ε where
  toFun x := uElt h (pv (Multiplicative.toAdd x)) (pc τ₀ (Multiplicative.toAdd x))
    (pc_adm hc _)
  map_one' := by
    apply hypSU_ext
    show uMat h (pv (0 : UP h.fixedField ε)) (pc τ₀ 0) = 1
    rw [pv_zero, pc_zero, uMat_zero]
  map_mul' x y := by
    apply hypSU_ext
    show uMat h (pv (Multiplicative.toAdd x + Multiplicative.toAdd y))
        (pc τ₀ (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      uMat h (pv (Multiplicative.toAdd x)) (pc τ₀ (Multiplicative.toAdd x)) *
        uMat h (pv (Multiplicative.toAdd y)) (pc τ₀ (Multiplicative.toAdd y))
    rw [uMat_mul, pv_add, pc_add hc]

@[expose] noncomputable def fixedUnit (μ : (h.fixedField)ˣ) : Kˣ :=
  Units.map h.fixedField.subtype.toMonoidHom μ

@[simp] theorem coe_fixedUnit (μ : (h.fixedField)ˣ) :
    ((fixedUnit μ : Kˣ) : K) = (((μ : h.fixedField)) : K) :=
  rfl

theorem bar_fixedUnit (μ : (h.fixedField)ˣ) : h.bar ((fixedUnit μ : Kˣ) : K) = (fixedUnit μ : Kˣ) :=
  (μ : h.fixedField).2

@[expose] noncomputable def tElt (μ : (h.fixedField)ˣ) : hypSU h 1 ε :=
  mkHypSU h (diagonal (torusEntries h (fun _ : Fin 1 => fixedUnit μ) (fun _ : Fin ε => (1 : Kˣ))))
    (diagonal_torusEntries_isometry h _ (fun k => by simp [UnitaryFieldData.norm]))
    (by
      rw [det_diagonal_torusEntries]
      simp only [torusRatio, bar_fixedUnit]
      simp)

theorem pv_utau_zero (μ : h.fixedField) (x : UP h.fixedField ε) (l : Fin ε) :
    pv (utau (0 : Fin ε → h.fixedField) μ x) l = (μ : K) * pv x l := by
  simp [pv, utau_apply]

theorem pc_utau_zero (τ₀ : K) (μ : h.fixedField) (x : UP h.fixedField ε) :
    pc τ₀ (utau (0 : Fin ε → h.fixedField) μ x) = (μ : K) ^ 2 * pc τ₀ x := by
  have e : ∑ l, (pv (utau (0 : Fin ε → h.fixedField) μ x) l) ^ 2 =
      (μ : K) ^ 2 * ∑ l, (pv x l) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pv_utau_zero]
    ring
  unfold pc
  rw [e]
  simp only [utau_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  push_cast
  ring

theorem tElt_mul_uPar {τ₀ : K} (hc : UCtx h τ₀) (μ : (h.fixedField)ˣ)
    (x : Multiplicative (UP h.fixedField ε)) :
    tElt μ * uPar hc x =
      uPar hc (Multiplicative.ofAdd (utau (0 : Fin ε → h.fixedField) (μ : h.fixedField)
        (Multiplicative.toAdd x))) * tElt μ := by
  apply hypSU_ext
  have hμ : ((μ : h.fixedField) : K) ≠ 0 := by
    have := μ.ne_zero
    exact_mod_cast this
  show diagonal (torusEntries h (fun _ : Fin 1 => fixedUnit μ) (fun _ : Fin ε => (1 : Kˣ))) *
      uMat h (pv (Multiplicative.toAdd x)) (pc τ₀ (Multiplicative.toAdd x)) =
    uMat h (pv (utau (0 : Fin ε → h.fixedField) (μ : h.fixedField) (Multiplicative.toAdd x)))
      (pc τ₀ (utau (0 : Fin ε → h.fixedField) (μ : h.fixedField) (Multiplicative.toAdd x))) *
      diagonal (torusEntries h (fun _ : Fin 1 => fixedUnit μ) (fun _ : Fin ε => (1 : Kˣ)))
  have e1 : pv (utau (0 : Fin ε → h.fixedField) (μ : h.fixedField) (Multiplicative.toAdd x)) =
      fun l => (μ : K) * pv (Multiplicative.toAdd x) l :=
    funext fun l => pv_utau_zero _ _ l
  rw [e1, pc_utau_zero]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [uMat, torusEntries, diagonal_mul, mul_diagonal, bar_fixed, bar_pv] <;>
    first
    | exact mul_comm _ _
    | field_simp

@[expose] noncomputable def gw (τ₀ : K) (d : Fin ε → h.fixedField) : Fin ε → K :=
  fun l => 2⁻¹ * (((d l : h.fixedField) : K) * τ₀)

@[expose] noncomputable def gc (τ₀ : K) (d : Fin ε → h.fixedField) : K :=
  -(2⁻¹ * ∑ l, h.bar (gw τ₀ d l) * gw τ₀ d l)

theorem bar_gw {τ₀ : K} (hc : UCtx h τ₀) (d : Fin ε → h.fixedField) (l : Fin ε) :
    h.bar (gw τ₀ d l) = -(2⁻¹ * (((d l : h.fixedField) : K) * τ₀)) := by
  simp only [gw, map_mul, bar_two_inv, bar_fixed, hc.bar_τ]
  ring

theorem gadm {τ₀ : K} (hc : UCtx h τ₀) (d : Fin ε → h.fixedField) :
    UAdm h (gw τ₀ d) (gc τ₀ d) := by
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ hc.two_ne
  have hbN : h.bar (∑ l, h.bar (gw τ₀ d l) * gw τ₀ d l) = ∑ l, h.bar (gw τ₀ d l) * gw τ₀ d l := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_mul, h.bar_bar, mul_comm]
  unfold UAdm gc
  rw [map_neg, map_mul, bar_two_inv, hbN]
  linear_combination (-(∑ l, h.bar (gw τ₀ d l) * gw τ₀ d l)) * h22

@[expose] noncomputable def gElt {τ₀ : K} (hc : UCtx h τ₀) (d : Fin ε → h.fixedField) :
    hypSU h 1 ε :=
  uElt h (gw τ₀ d) (gc τ₀ d) (gadm hc d)

theorem pv_utau_one (d : Fin ε → h.fixedField) (x : UP h.fixedField ε) :
    pv (utau d 1 x) = pv x := by
  funext l
  simp [pv, utau_apply]

theorem pc_utau_one (τ₀ : K) (d : Fin ε → h.fixedField) (x : UP h.fixedField ε) :
    pc τ₀ (utau d 1 x) = pc τ₀ x + (∑ l, ((d l : h.fixedField) : K) * pv x l) * τ₀ := by
  unfold pc
  rw [pv_utau_one]
  simp only [utau_apply, one_pow, one_mul]
  push_cast
  simp only [pv]
  ring

theorem gElt_mul_uPar {τ₀ : K} (hc : UCtx h τ₀) (d : Fin ε → h.fixedField)
    (x : Multiplicative (UP h.fixedField ε)) :
    gElt hc d * uPar hc x =
      uPar hc (Multiplicative.ofAdd (utau d 1 (Multiplicative.toAdd x))) * gElt hc d := by
  apply hypSU_ext
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ hc.two_ne
  show uMat h (gw τ₀ d) (gc τ₀ d) *
      uMat h (pv (Multiplicative.toAdd x)) (pc τ₀ (Multiplicative.toAdd x)) =
    uMat h (pv (utau d 1 (Multiplicative.toAdd x))) (pc τ₀ (utau d 1 (Multiplicative.toAdd x))) *
      uMat h (gw τ₀ d) (gc τ₀ d)
  rw [uMat_mul, uMat_mul, pv_utau_one, pc_utau_one, add_comm (gw τ₀ d)]
  congr 1
  set v := pv (Multiplicative.toAdd x) with hv
  have e1 : ∑ l, h.bar (gw τ₀ d l) * v l =
      -(2⁻¹ * τ₀ * ∑ l, ((d l : h.fixedField) : K) * v l) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [bar_gw hc]
    ring
  have e2 : ∑ l, h.bar (v l) * gw τ₀ d l =
      2⁻¹ * τ₀ * ∑ l, ((d l : h.fixedField) : K) * v l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hv, bar_pv]
    simp only [gw]
    ring
  rw [e1, e2]
  linear_combination ((∑ l, ((d l : h.fixedField) : K) * v l) * τ₀) * h22

@[expose] noncomputable def tPar {τ₀ : K} (hc : UCtx h τ₀) (d : Fin ε → h.fixedField)
    (μ : (h.fixedField)ˣ) : hypSU h 1 ε :=
  gElt hc d * tElt μ

theorem tPar_conj {τ₀ : K} (hc : UCtx h τ₀) (d : Fin ε → h.fixedField) (μ : (h.fixedField)ˣ)
    (x : Multiplicative (UP h.fixedField ε)) :
    tPar hc d μ * uPar hc x * (tPar hc d μ)⁻¹ =
      uPar hc (Multiplicative.ofAdd (utau d (μ : h.fixedField) (Multiplicative.toAdd x))) := by
  rw [mul_inv_eq_iff_eq_mul]
  have h1 := tElt_mul_uPar hc μ x
  have h2 := gElt_mul_uPar hc d
    (Multiplicative.ofAdd (utau (0 : Fin ε → h.fixedField) (μ : h.fixedField)
      (Multiplicative.toAdd x)))
  rw [toAdd_ofAdd, utau_comp] at h2
  unfold tPar
  rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

theorem uPar_inj {τ₀ : K} (hc : UCtx h τ₀) :
    Function.Injective ((hypProj h 1 ε).comp (uPar hc)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : uPar hc x ∈ (hypProj h 1 ε).ker := hx
  rw [ker_hypProj] at hker
  obtain ⟨c, -, -, hg⟩ := hker
  have hm : uMat h (pv (Multiplicative.toAdd x)) (pc τ₀ (Multiplicative.toAdd x)) =
      Matrix.scalar _ (c : K) := by
    have h1 : (((uPar hc x : hypSU h 1 ε) : GL (HypIndex 1 ε) K) :
        Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
        uMat h (pv (Multiplicative.toAdd x)) (pc τ₀ (Multiplicative.toAdd x)) := rfl
    rw [← h1, hg, GeneralLinearGroup.coe_scalar]
  have hv : ∀ l, pv (Multiplicative.toAdd x) l = 0 := fun l => by
    have := congrFun (congrFun hm (.inr (.inl l))) (.inr (.inr 0))
    simpa [uMat, Matrix.scalar_apply, Matrix.diagonal_apply_ne] using this
  have hc0 : pc τ₀ (Multiplicative.toAdd x) = 0 := by
    have := congrFun (congrFun hm (.inl 0)) (.inr (.inr 0))
    simpa [uMat, Matrix.scalar_apply, Matrix.diagonal_apply_ne] using this
  have hx1 : (Multiplicative.toAdd x).1 = 0 := by
    funext l
    exact Subtype.ext (hv l)
  have hx2 : (Multiplicative.toAdd x).2 = 0 := by
    have h3 : (((Multiplicative.toAdd x).2 : h.fixedField) : K) * τ₀ = 0 := by
      have : ∑ l, (pv (Multiplicative.toAdd x) l) ^ 2 = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [hv l]; simp
      unfold pc at hc0
      rw [this, mul_zero, sub_zero] at hc0
      exact hc0
    exact Subtype.ext ((mul_eq_zero.1 h3).resolve_right hc.τ_ne)
  have : Multiplicative.toAdd x = 0 := Prod.ext hx1 hx2
  exact (Multiplicative.toAdd.injective (by simpa using this))

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
