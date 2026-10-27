module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

namespace WIso

open W192

def mact (M : Matrix (Fin 2) (Fin 2) (ZMod 4)) (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2)

theorem mact_mul (M N : Matrix (Fin 2) (Fin 2) (ZMod 4)) (v : ZMod 4 × ZMod 4) :
    mact (M * N) v = mact M (mact N v) := by
  simp only [mact, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq]
  constructor <;> ring

theorem mact_one (v : ZMod 4 × ZMod 4) : mact 1 v = v := by
  simp [mact]

theorem mact_add (M : Matrix (Fin 2) (Fin 2) (ZMod 4)) (u v : ZMod 4 × ZMod 4) :
    mact M (u + v) = mact M u + mact M v := by
  simp only [mact, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem mact_ext {M N : Matrix (Fin 2) (Fin 2) (ZMod 4)} (h : ∀ v, mact M v = mact N v) : M = N := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  simp only [mact, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1.1
  · exact h2.1
  · exact h1.2
  · exact h2.2

theorem mulVec_eq_mact (M : Matrix (Fin 2) (Fin 2) (ZMod 4)) (v : ZMod 4 × ZMod 4) :
    M.mulVec ![v.1, v.2] = ![(mact M v).1, (mact M v).2] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mact]

theorem toAdd_apply (f : MulAut (Multiplicative (ZMod 4 × ZMod 4))) (v : ZMod 4 × ZMod 4) :
    Multiplicative.toAdd (f (Multiplicative.ofAdd v)) =
      v.1 • Multiplicative.toAdd (f (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4)))) +
        v.2 • Multiplicative.toAdd (f (Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4)))) := by
  let F : (ZMod 4 × ZMod 4) →+ (ZMod 4 × ZMod 4) :=
    { toFun := fun v => Multiplicative.toAdd (f (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp [ofAdd_add, toAdd_mul] }
  have hv : v = v.1 • ((1 : ZMod 4), (0 : ZMod 4)) + v.2 • ((0 : ZMod 4), (1 : ZMod 4)) := by
    ext <;> simp
  show F v = v.1 • F (1, 0) + v.2 • F (0, 1)
  conv_lhs => rw [hv]
  rw [map_add, ZMod.map_smul, ZMod.map_smul]

def matOf (f : MulAut (Multiplicative (ZMod 4 × ZMod 4))) : Matrix (Fin 2) (Fin 2) (ZMod 4) :=
  !![(Multiplicative.toAdd (f (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4))))).1,
      (Multiplicative.toAdd (f (Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4))))).1;
    (Multiplicative.toAdd (f (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4))))).2,
      (Multiplicative.toAdd (f (Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4))))).2]

theorem mact_matOf (f : MulAut (Multiplicative (ZMod 4 × ZMod 4))) (v : ZMod 4 × ZMod 4) :
    mact (matOf f) v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) := by
  rw [toAdd_apply f v]
  ext <;> simp [mact, matOf] <;> ring

def matHom : MulAut (Multiplicative (ZMod 4 × ZMod 4)) →* Matrix (Fin 2) (Fin 2) (ZMod 4) where
  toFun := matOf
  map_one' := mact_ext fun v => by rw [mact_matOf, mact_one]; rfl
  map_mul' f g := mact_ext fun v => by
    rw [mact_mul, mact_matOf, mact_matOf, mact_matOf, MulAut.mul_apply, ofAdd_toAdd]

theorem mact_matHom (f : MulAut (Multiplicative (ZMod 4 × ZMod 4))) (v : ZMod 4 × ZMod 4) :
    mact (matHom f) v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) :=
  mact_matOf f v

theorem matHom_injective : Function.Injective matHom := by
  intro f g h
  refine MulEquiv.ext fun v => ?_
  have := mact_matHom f (Multiplicative.toAdd v)
  rw [h, mact_matHom, ofAdd_toAdd] at this
  exact Multiplicative.toAdd.injective this.symm

def autOfMat (M M' : Matrix (Fin 2) (Fin 2) (ZMod 4)) (h : M' * M = 1) (h' : M * M' = 1) :
    MulAut (Multiplicative (ZMod 4 × ZMod 4)) where
  toFun v := Multiplicative.ofAdd (mact M (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (mact M' (Multiplicative.toAdd v))
  left_inv v := by simp only [toAdd_ofAdd, ← mact_mul, h, mact_one, ofAdd_toAdd]
  right_inv v := by simp only [toAdd_ofAdd, ← mact_mul, h', mact_one, ofAdd_toAdd]
  map_mul' u v := by simp only [toAdd_mul, mact_add, ofAdd_add]

theorem matHom_autOfMat (M M' : Matrix (Fin 2) (Fin 2) (ZMod 4)) (h : M' * M = 1) (h' : M * M' = 1) :
    matHom (autOfMat M M' h h') = M :=
  mact_ext fun v => by rw [mact_matHom]; rfl

theorem matHom_act_r : matHom (act (DihedralGroup.r 1)) = !![0, 1; -1, 1] := by
  decide

theorem matHom_act_sr : matHom (act (DihedralGroup.sr 0)) = !![0, 1; 1, 0] := by
  decide

theorem mulAut_three_fpf {f : MulAut (Multiplicative (ZMod 4 × ZMod 4))} (h3 : f ^ 3 = 1) (h1 : f ≠ 1)
    {v : Multiplicative (ZMod 4 × ZMod 4)} (hv : f v = v) : v = 1 := by
  have hM3 : matHom f ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hM1 : matHom f ≠ 1 := fun h => h1 (matHom_injective (h.trans (map_one matHom).symm))
  have hfix : mact (matHom f) (Multiplicative.toAdd v) = Multiplicative.toAdd v := by
    rw [mact_matHom, ofAdd_toAdd, hv]
  have key := gl24_three_fpf_dec (matHom f) hM3 hM1 ![(Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2]
    (by rw [mulVec_eq_mact, hfix])
  have h01 : (Multiplicative.toAdd v).1 = 0 := by simpa using congrFun key 0
  have h02 : (Multiplicative.toAdd v).2 = 0 := by simpa using congrFun key 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact Prod.ext h01 h02

def dAutFun (i j : ZMod 6) : DihedralGroup 6 → DihedralGroup 6
  | .r k => .r (i * k)
  | .sr k => .sr (j + i * k)

def dAut (i j : ZMod 6) : DihedralGroup 6 →* DihedralGroup 6 where
  toFun := dAutFun i j
  map_one' := by
    rw [DihedralGroup.one_def]
    simp [dAutFun]
  map_mul' a b := by
    cases a <;> cases b <;>
      simp only [dAutFun, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;> congr 1 <;> ring

theorem dAutFun_inv : ∀ i j : ZMod 6, i * i = 1 → ∀ d : DihedralGroup 6,
    dAutFun i j (dAutFun i (-(i * j)) d) = d := by
  decide

theorem dAut_inv {i j : ZMod 6} (h : i * i = 1) (d : DihedralGroup 6) :
    dAut i j (dAut i (-(i * j)) d) = d :=
  dAutFun_inv i j h d

theorem act_faithful (d : DihedralGroup 6) (h : ∀ v, act d v = v) : d = 1 := by
  have key : ∀ d : DihedralGroup 6, (∀ v : ZMod 4 × ZMod 4, dAct d v = v) → d = 1 := by
    decide
  exact key d fun v => Multiplicative.ofAdd.injective
    (show Multiplicative.ofAdd (dAct d v) = Multiplicative.ofAdd v from h (Multiplicative.ofAdd v))

theorem d12_conj : ∀ a y : DihedralGroup 6, a ^ 3 = 1 → a ≠ 1 → y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a⁻¹ := by
  decide

theorem rep_conj (ψ : DihedralGroup 6 →* MulAut (Multiplicative (ZMod 4 × ZMod 4)))
    (hψ : Function.Injective ψ) :
    ∃ Q : MulAut (Multiplicative (ZMod 4 × ZMod 4)), ∃ β : DihedralGroup 6 →* DihedralGroup 6,
      ∀ d, Q * act d = ψ (β d) * Q := by
  have hne : ∀ n : ℕ, (DihedralGroup.r 1 : DihedralGroup 6) ^ n ≠ 1 →
      matHom (ψ (DihedralGroup.r 1)) ^ n ≠ 1 := by
    intro n hn h
    rw [← map_pow, ← map_pow, ← map_one matHom] at h
    exact hn (hψ ((matHom_injective h).trans (map_one ψ).symm))
  have hA : matHom (ψ (DihedralGroup.sr 0)) * matHom (ψ (DihedralGroup.sr 0)) = 1 := by
    rw [← map_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one, map_one]
  have hB6 : matHom (ψ (DihedralGroup.r 1)) ^ 6 = 1 := by
    rw [← map_pow, ← map_pow, DihedralGroup.r_one_pow_n, map_one, map_one]
  have hAB : matHom (ψ (DihedralGroup.sr 0)) * matHom (ψ (DihedralGroup.r 1)) *
      matHom (ψ (DihedralGroup.sr 0)) * matHom (ψ (DihedralGroup.r 1)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      show (DihedralGroup.sr 0 * DihedralGroup.r 1 * DihedralGroup.sr 0 * DihedralGroup.r 1 :
        DihedralGroup 6) = 1 by decide, map_one, map_one]
  obtain ⟨P, hdet, i, hi, j, -, hPB, hPA⟩ := gl24_d12_dec _ _ hA hB6 hAB (hne 2 (by decide))
    (hne 3 (by decide))
  have hPu : IsUnit P.det := by
    rcases hdet with h | h <;> rw [h]
    · exact isUnit_one
    · exact IsUnit.of_mul_eq_one (3 : ZMod 4) (by decide)
  set Pa := autOfMat P P⁻¹ (P.nonsing_inv_mul hPu) (P.mul_nonsing_inv hPu)
  have hPm : matHom Pa = P := matHom_autOfMat P P⁻¹ _ _
  have hr : Pa * ψ (DihedralGroup.r 1) = act (dAut i j (DihedralGroup.r 1)) * Pa := by
    apply matHom_injective
    rw [map_mul, map_mul, hPm, hPB]
    congr 1
    rw [show dAut i j (DihedralGroup.r 1) = DihedralGroup.r 1 ^ i by
      rw [DihedralGroup.r_one_pow]
      show DihedralGroup.r ((i : ZMod 6) * 1) = _
      rw [mul_one], map_pow, map_pow, matHom_act_r]
  have hs : Pa * ψ (DihedralGroup.sr 0) = act (dAut i j (DihedralGroup.sr 0)) * Pa := by
    apply matHom_injective
    rw [map_mul, map_mul, hPm, hPA]
    congr 1
    rw [show dAut i j (DihedralGroup.sr 0) = DihedralGroup.sr 0 * DihedralGroup.r 1 ^ j by
      rw [DihedralGroup.r_one_pow, DihedralGroup.sr_mul_r, zero_add]
      show DihedralGroup.sr ((j : ZMod 6) + (i : ZMod 6) * 0) = _
      rw [mul_zero, add_zero], map_mul, map_mul, map_pow, map_pow, matHom_act_r, matHom_act_sr]
  have hrn : ∀ n : ℕ, Pa * ψ (DihedralGroup.r 1 ^ n) = act (dAut i j (DihedralGroup.r 1 ^ n)) * Pa := by
    intro n
    simp only [map_pow]
    exact SemiconjBy.pow_right hr n
  have hall : ∀ d, Pa * ψ d = act (dAut i j d) * Pa := by
    intro d
    rcases d with k | k
    · have := hrn k.val
      rwa [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] at this
    · have h := hrn k.val
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] at h
      rw [show (DihedralGroup.sr k : DihedralGroup 6) = DihedralGroup.sr 0 * DihedralGroup.r k by
        rw [DihedralGroup.sr_mul_r, zero_add], map_mul, map_mul, map_mul]
      exact SemiconjBy.mul_right hs h
  have hii : (i : ZMod 6) * i = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> decide
  refine ⟨Pa⁻¹, dAut (i : ZMod 6) (-((i : ZMod 6) * (j : ZMod 6))), fun d => ?_⟩
  have h := hall (dAut (i : ZMod 6) (-((i : ZMod 6) * (j : ZMod 6))) d)
  rw [dAut_inv hii] at h
  calc Pa⁻¹ * act d = Pa⁻¹ * (act d * Pa) * Pa⁻¹ := by group
    _ = Pa⁻¹ * (Pa * ψ (dAut (i : ZMod 6) (-((i : ZMod 6) * (j : ZMod 6))) d)) * Pa⁻¹ := by rw [← h]
    _ = ψ (dAut (i : ZMod 6) (-((i : ZMod 6) * (j : ZMod 6))) d) * Pa⁻¹ := by group

end WIso

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
