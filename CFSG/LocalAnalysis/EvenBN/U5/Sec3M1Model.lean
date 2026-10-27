module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M2Model
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (xBlock yBlock zBlock)
open scoped commutatorElement

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem exists_I₁_block (h : UnitaryFieldData 2 f K) {b : K} (hb : b ≠ 0) (hbar : h.bar b = b) :
    ∃ j ∈ I₁sub h, mat j ιe₁ ιe₁ = b ∧ mat j ιe₂ ιe₂ = b ∧ mat j ιz ιz = 1 ∧
      mat j ιf₁ ιf₁ = b⁻¹ ∧ mat j ιf₂ ιf₂ = b⁻¹ := by
  obtain ⟨j, hj, e1, e2, e3, e4, e5⟩ := exists_torus h hb hb
  refine ⟨j, mem_I₁sub.2 ⟨hj, e1.trans e2.symm⟩, e1, e2, ?_, ?_, ?_⟩
  · rw [e3, hbar]
    field_simp
  · rw [e4, hbar]
  · rw [e5, hbar]

theorem exists_I₁_fifth (hf : 2 ≤ f) :
    ∃ j ∈ I₁sub h, ∃ β : K, β ≠ 0 ∧ β ≠ β⁻¹ ∧ h.bar β = β ∧ mat (j ^ 5) ιe₁ ιe₁ = β ∧
      mat (j ^ 5) ιe₂ ιe₂ = β ∧ mat (j ^ 5) ιz ιz = 1 ∧ mat (j ^ 5) ιf₁ ιf₁ = β⁻¹ ∧
      mat (j ^ 5) ιf₂ ιf₂ = β⁻¹ := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq4 : 4 ≤ 2 ^ f := (Nat.pow_le_pow_right two_pos hf).trans_eq' (by norm_num)
  have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    have h1 : 1 ≤ 2 ^ f := by omega
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  have hdvd : 2 ^ f + 1 ∣ orderOf ω := by
    rw [hω, e]
    exact dvd_mul_right _ _
  set ω' : Kˣ := ω ^ (2 ^ f + 1) with hω'
  have hord : orderOf ω' = 2 ^ f - 1 := by
    rw [hω', orderOf_pow_of_dvd (by omega) hdvd, hω, e, Nat.mul_div_cancel_left _ (by omega)]
  set b : K := (ω' : K) with hb
  have hb0 : b ≠ 0 := Units.ne_zero _
  have hbar : h.bar b = b := by
    rw [UnitaryFieldData.bar_apply, hb, ← Units.val_pow_eq_pow_val]
    congr 1
    calc ω' ^ 2 ^ f = ω' ^ (2 ^ f - 1 + 1) := by congr 1; omega
      _ = ω' ^ (2 ^ f - 1) * ω' := pow_succ _ _
      _ = ω' := by rw [← hord, pow_orderOf_eq_one, one_mul]
  have hb10 : b ^ 10 ≠ 1 := by
    intro e10
    have e' : ω' ^ 10 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact e10)
    have hd := orderOf_dvd_of_pow_eq_one e'
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    rcases Nat.lt_or_ge f 4 with hf4 | hf4
    · rcases (show f = 2 ∨ f = 3 by omega) with rfl | rfl <;> norm_num at hd
    · have : 16 ≤ 2 ^ f := (Nat.pow_le_pow_right two_pos hf4).trans_eq' (by norm_num)
      omega
  obtain ⟨j, hj, e1, e2, e3, e4, e5⟩ := exists_I₁_block h hb0 hbar
  have hjI : j ∈ hypTorus h 2 1 := torusEq_le _ hj
  refine ⟨j, hj, b ^ 5, pow_ne_zero _ hb0, fun e5' => hb10 ?_, by rw [map_pow, hbar], ?_, ?_, ?_,
    ?_, ?_⟩
  · have h1 : b ^ 5 * b ^ 5 = 1 := by
      calc b ^ 5 * b ^ 5 = b ^ 5 * (b ^ 5)⁻¹ := by rw [← e5']
        _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hb0)
    rw [← h1]
    ring
  · rw [torus_pow_apply hjI, e1]
  · rw [torus_pow_apply hjI, e2]
  · rw [torus_pow_apply hjI, e3, one_pow]
  · rw [torus_pow_apply hjI, e4, inv_pow]
  · rw [torus_pow_apply hjI, e5, inv_pow]

theorem mem_N₁sub_of_blk3 {g : hypSU h 2 1}
    (hg : mat g = blk3 (xBlock (mat g)) 0 0 (zBlock (mat g)) 0 (yBlock (mat g)))
    (hdet : (xBlock (mat g)).det = 1) : g ∈ N₁sub h := by
  set A := xBlock (mat g) with hAdef
  set P := zBlock (mat g) with hPdef
  set D := yBlock (mat g) with hDdef
  have hgram : ((mat g).map h.bar)ᵀ * hypGram 2 1 K * mat g = hypGram 2 1 K :=
    (mem_hypSU.1 g.2).1
  have hdetg : (mat g).det = 1 := (mem_hypSU.1 g.2).2
  rw [hg] at hgram hdetg
  obtain ⟨hAD, -, -, -⟩ := (blk3_gram_iff h A 0 0 P 0 D).1 hgram
  have hA : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hD : D = barInvT h A := eq_barInvT_of_mul_eq_one hAD
  rw [det_blk3, hD, det_barInvT hA, hdet, map_one, inv_one, one_mul, mul_one] at hdetg
  have hP : P = of fun _ _ => (1 : K) := by
    ext k l
    fin_cases k
    fin_cases l
    rw [← hdetg, Matrix.det_fin_one]
    rfl
  have hlev : g = lev (hK := h) A hA := by
    apply mat_injective
    rw [hg, mat_lev, oddDiag, hdet, map_one, div_one, ← hP, ← hD]
  refine ⟨⟨A, hdet⟩, ?_⟩
  rw [hlev]
  exact (lev_eq_leviSU ⟨A, hdet⟩ hA).symm

theorem N₁sub_comm_I₁sub {n i : hypSU h 2 1} (hn : n ∈ N₁sub h) (hi : i ∈ I₁sub h) :
    i * n = n * i := by
  obtain ⟨hiI, h12⟩ := mem_I₁sub.1 hi
  have hf12 : mat i ιf₁ ιf₁ = mat i ιf₂ ιf₂ := by
    have b1 := torus_bar_mul hiI ιe₁
    have b2 := torus_bar_mul hiI ιe₂
    simp only [hypPartner_inl] at b1 b2
    rw [h12] at b1
    exact mul_left_cancel₀ ((map_ne_zero h.bar).2 (torus_ne_zero hiI ιe₂)) (b1.trans b2.symm)
  obtain ⟨B, rfl⟩ := hn
  refine (torus_commute_iff hiI _).2 fun a b => ?_
  rw [mat_leviSU]
  have hE : ∀ k : Fin 2, mat i (.inl k) (.inl k) = mat i ιe₁ ιe₁ := fun k => by
    fin_cases k
    · rfl
    · exact h12.symm
  have hF : ∀ k : Fin 2, mat i (.inr (.inr k)) (.inr (.inr k)) = mat i ιf₁ ιf₁ := fun k => by
    fin_cases k
    · rfl
    · exact hf12.symm
  rcases a with k | m | k <;> rcases b with l | n | l
  · rw [hE k, hE l, blk3_inl_inl, mul_comm]
  · simp
  · simp
  · simp
  · fin_cases m
    fin_cases n
    rw [mul_comm]
  · simp
  · simp
  · simp
  · rw [hF k, hF l, blk3_inr_inr_inr_inr, mul_comm]

section BlockScalar

variable {t : hypSU h 2 1} (ht : t ∈ hypTorus h 2 1) {β : K} (hβ : β ≠ β⁻¹)
  (h1 : mat t ιe₁ ιe₁ = β) (h2 : mat t ιe₂ ιe₂ = β) (h3 : mat t ιz ιz = 1)
  (h4 : mat t ιf₁ ιf₁ = β⁻¹) (h5 : mat t ιf₂ ιf₂ = β⁻¹)
include ht hβ h1 h2 h3 h4 h5

theorem mat_eq_blk3_of_comm {g : hypSU h 2 1} (hc : t * g = g * t) :
    mat g = blk3 (xBlock (mat g)) 0 0 (zBlock (mat g)) 0 (yBlock (mat g)) := by
  have hβ1 : β ≠ 1 := fun e => hβ (by rw [e, inv_one])
  have hβ1' : β⁻¹ ≠ 1 := fun e => hβ1 (inv_eq_one.1 e)
  have hk := (torus_commute_iff ht g).1 hc
  have hz : ∀ {a b : HypIndex 2 1} {x y : K}, x ≠ y → mat t a a = x → mat t b b = y →
      mat g a b = 0 := by
    intro a b x y hxy ha hb
    have e := hk a b
    rw [ha, hb] at e
    have : mat g a b * (x - y) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hxy)
  have hE : ∀ i : Fin 2, mat t (.inl i) (.inl i) = β := fun i => by
    fin_cases i
    · exact h1
    · exact h2
  have hZ : ∀ k : Fin 1, mat t (.inr (.inl k)) (.inr (.inl k)) = 1 := fun k => by
    fin_cases k
    exact h3
  have hF : ∀ i : Fin 2, mat t (.inr (.inr i)) (.inr (.inr i)) = β⁻¹ := fun i => by
    fin_cases i
    · exact h4
    · exact h5
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  · rfl
  · exact hz hβ1 (hE i) (hZ l)
  · exact hz hβ (hE i) (hF j)
  · exact hz hβ1.symm (hZ k) (hE j)
  · rfl
  · exact hz hβ1'.symm (hZ k) (hF j)
  · exact hz hβ.symm (hF i) (hE j)
  · exact hz hβ1' (hF i) (hZ l)
  · rfl

theorem commutator_mem_N₁sub {g g' : hypSU h 2 1} (hg : t * g = g * t) (hg' : t * g' = g' * t) :
    ⁅g, g'⁆ ∈ N₁sub h := by
  have hinv : ∀ {x : hypSU h 2 1}, t * x = x * t → t * x⁻¹ = x⁻¹ * t := fun {x} hx => by
    calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
      _ = x⁻¹ * (t * x) * x⁻¹ := by rw [hx]
      _ = x⁻¹ * t := by group
  have hb := fun {x : hypSU h 2 1} (hx : t * x = x * t) =>
    mat_eq_blk3_of_comm ht hβ h1 h2 h3 h4 h5 hx
  have hmul : ∀ {x y : hypSU h 2 1}, t * x = x * t → t * y = y * t →
      xBlock (mat (x * y)) = xBlock (mat x) * xBlock (mat y) := by
    intro x y hx hy
    rw [mat_mul, hb hx, hb hy, blk3_mul]
    rfl
  have hc : ∀ {x y : hypSU h 2 1}, t * x = x * t → t * y = y * t → t * (x * y) = x * y * t :=
    fun {x y} hx hy => by rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  have hdetinv : ∀ {x : hypSU h 2 1}, t * x = x * t →
      (xBlock (mat x)).det * (xBlock (mat x⁻¹)).det = 1 := by
    intro x hx
    rw [← det_mul, ← hmul hx (hinv hx), mul_inv_cancel, mat_one]
    have : xBlock (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = 1 := by
      ext i j
      simp [xBlock, Matrix.one_apply]
    rw [this, det_one]
  have hcomm : mat ⁅g, g'⁆ = blk3 (xBlock (mat ⁅g, g'⁆)) 0 0 (zBlock (mat ⁅g, g'⁆)) 0
      (yBlock (mat ⁅g, g'⁆)) := by
    rw [commutatorElement_def]
    exact hb (hc (hc (hc hg hg') (hinv hg)) (hinv hg'))
  refine mem_N₁sub_of_blk3 hcomm ?_
  rw [commutatorElement_def, hmul (hc (hc hg hg') (hinv hg)) (hinv hg'),
    hmul (hc hg hg') (hinv hg), hmul hg hg', det_mul, det_mul, det_mul]
  have e1 := hdetinv hg
  have e2 := hdetinv hg'
  linear_combination (xBlock (mat g')).det * (xBlock (mat g'⁻¹)).det * e1 + e2

end BlockScalar

end Model

end CFSG.LocalAnalysis.EvenBN.U5
