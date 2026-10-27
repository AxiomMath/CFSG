module

public import CFSG.LieType.Steinberg.Classical.SpinPlus.Unipotent

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open QuadraticMap Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.Steinberg.SpinPlus

variable {K : Type} [Field K]

theorem longMat_plusIdx_mulVec {n : ℕ} (i j : Fin n) (s t : Bool) (w : Fin n ⊕ Fin n → K) :
    longMat K plusIdx i j s t *ᵥ w =
      w (plusIdx j (!t)) • Pi.single (plusIdx i s) 1 -
        w (plusIdx i (!s)) • Pi.single (plusIdx j t) 1 := by
  rw [longMat, Matrix.sub_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq, one_mul,
    one_mul]

theorem longMat_two_three_mulVec_e0 (s t : Bool) :
    longMat K plusIdx (2 : Fin 4) 3 s t *ᵥ Pi.single (.inl 0) 1 = 0 := by
  rw [longMat_plusIdx_mulVec]
  cases s <;> cases t <;> simp [plusIdx]

theorem longMat_zero_one_mulVec_e0 (t : Bool) :
    longMat K plusIdx (0 : Fin 4) 1 true t *ᵥ Pi.single (.inl 0) 1 = 0 := by
  rw [longMat_plusIdx_mulVec]
  cases t <;> simp [plusIdx]

theorem finrank_le_three_of_invariant (W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hW : ∀ w ∈ W, quadPlus 4 K w = 0)
    (h23 : ∀ s t : Bool, ∀ w ∈ W, longMat K plusIdx (2 : Fin 4) 3 s t *ᵥ w ∈ W)
    (h01 : ∀ t : Bool, ∀ w ∈ W, longMat K plusIdx (0 : Fin 4) 1 true t *ᵥ w ∈ W) :
    Module.finrank K W ≤ 3 := by
  have hpol : ∀ x ∈ W, ∀ y ∈ W, polar (quadPlus 4 K) x y = 0 := fun x hx y hy => by
    rw [polar, hW _ (W.add_mem hx hy), hW x hx, hW y hy]
    ring
  have hsq : ∀ w ∈ W, ∀ (y : Fin 4 ⊕ Fin 4 → K) (c : Fin 4 ⊕ Fin 4), y ∈ W →
      polar (quadPlus 4 K) w y = -(w c) ^ 2 → w c = 0 := fun w hw y c hy h => by
    rw [hpol w hw y hy] at h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (neg_eq_zero.mp h.symm)
  have hvan : ∀ w ∈ W, w (.inr 2) = 0 ∧ w (.inr 3) = 0 ∧ w (.inl 2) = 0 ∧ w (.inl 3) = 0 ∧
      w (.inr 0) = 0 := by
    intro w hw
    refine ⟨hsq w hw _ _ (h23 true true _ (h23 true false w hw)) ?_,
      hsq w hw _ _ (h23 true true _ (h23 false true w hw)) ?_,
      hsq w hw _ _ (h23 false true _ (h23 false false w hw)) ?_,
      hsq w hw _ _ (h23 true false _ (h23 false false w hw)) ?_,
      hsq w hw _ _ (h01 false _ (h01 true w hw)) ?_⟩ <;>
    · simp [longMat_plusIdx_mulVec, plusIdx, polar_quadPlus, Pi.single_apply]
      ring
  let c : Fin 3 → Fin 4 ⊕ Fin 4 := ![.inl 0, .inl 1, .inr 1]
  let ρ : W →ₗ[K] (Fin 3 → K) := (LinearMap.funLeft K K c).comp W.subtype
  have hρ : Function.Injective ρ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨w, hw⟩ hρw
    have h0 := congrFun hρw 0
    have h1 := congrFun hρw 1
    have h2 := congrFun hρw 2
    simp only [ρ, c, LinearMap.comp_apply, LinearMap.funLeft_apply, Submodule.subtype_apply,
      Pi.zero_apply] at h0 h1 h2
    obtain ⟨a1, a2, a3, a4, a5⟩ := hvan w hw
    ext x
    rcases x with x | x <;> fin_cases x <;> simp_all
  calc Module.finrank K W ≤ Module.finrank K (Fin 3 → K) :=
        LinearMap.finrank_le_finrank_of_injective hρ
    _ = 3 := by simp

end CFSG.ClassicalInvolution.Q3.Q3T
