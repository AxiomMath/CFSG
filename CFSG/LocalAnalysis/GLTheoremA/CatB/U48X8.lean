module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

noncomputable section

variable {K : Type} [Field K]

@[expose] def dotB (h : UnitaryFieldData 2 3 K) (u v : Fin 4 → K) : K := ∑ i, h.bar (u i) * v i

@[expose] def act (g : GL (Fin 4) K) (v : Fin 4 → K) : Fin 4 → K := (g : Matrix (Fin 4) (Fin 4) K) *ᵥ v

theorem dotB_add_right (h : UnitaryFieldData 2 3 K) (u v w : Fin 4 → K) :
    dotB h u (v + w) = dotB h u v + dotB h u w := by
  simp [dotB, mul_add, Finset.sum_add_distrib]

theorem dotB_smul_right (h : UnitaryFieldData 2 3 K) (u : Fin 4 → K) (c : K) (v : Fin 4 → K) :
    dotB h u (c • v) = c * dotB h u v := by
  simp only [dotB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem dotB_sub_right (h : UnitaryFieldData 2 3 K) (u v w : Fin 4 → K) :
    dotB h u (v - w) = dotB h u v - dotB h u w := by
  simp [dotB, mul_sub, Finset.sum_sub_distrib]

theorem dotB_zero_right (h : UnitaryFieldData 2 3 K) (u : Fin 4 → K) : dotB h u 0 = 0 := by
  simp [dotB]

theorem dotB_act (h : UnitaryFieldData 2 3 K) {g : GL (Fin 4) K}
    (hg : ((g : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) K) = 1)
    (u v : Fin 4 → K) : dotB h (act g u) (act g v) = dotB h u v := by
  have key : ∀ x y : Fin 4 → K, dotB h x y = (fun i => h.bar (x i)) ⬝ᵥ y := fun x y => rfl
  rw [key, key]
  simp only [act]
  have hm : (fun i => h.bar (((g : Matrix (Fin 4) (Fin 4) K) *ᵥ u) i)) =
      ((g : Matrix (Fin 4) (Fin 4) K).map h.bar) *ᵥ (fun i => h.bar (u i)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hm, dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hg,
    Matrix.one_mulVec, dotProduct_comm]

theorem act_mul (g g' : GL (Fin 4) K) (v : Fin 4 → K) : act (g * g') v = act g (act g' v) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 4 → K) : act 1 v = v := by
  simp [act]

theorem act_add (g : GL (Fin 4) K) (v w : Fin 4 → K) : act g (v + w) = act g v + act g w := by
  simp [act, Matrix.mulVec_add]

theorem act_smul (g : GL (Fin 4) K) (c : K) (v : Fin 4 → K) : act g (c • v) = c • act g v := by
  simp [act, Matrix.mulVec_smul]

theorem act_sub (g : GL (Fin 4) K) (v w : Fin 4 → K) : act g (v - w) = act g v - act g w := by
  simp [act, Matrix.mulVec_sub]

@[expose] def Xs (W : Subgroup (GL (Fin 4) K)) : Submodule K (Fin 4 → K) :=
  Submodule.span K {v | ∃ w ∈ W, ∃ u : Fin 4 → K, v = act w u - u}

theorem act_sub_mem_Xs {W : Subgroup (GL (Fin 4) K)} {w : GL (Fin 4) K} (hw : w ∈ W) (u : Fin 4 → K) :
    act w u - u ∈ Xs W :=
  Submodule.subset_span ⟨w, hw, u, rfl⟩

def Rs (W : Subgroup (GL (Fin 4) K)) : Submodule K (Fin 4 → K) where
  carrier := {x | x ∈ Xs W ∧ ∀ w ∈ W, act w x = x}
  add_mem' := fun {x y} hx hy => ⟨(Xs W).add_mem hx.1 hy.1, fun w hw => by
    rw [act_add, hx.2 w hw, hy.2 w hw]⟩
  zero_mem' := ⟨(Xs W).zero_mem, fun w _ => by simp [act]⟩
  smul_mem' := fun c {x} hx => ⟨(Xs W).smul_mem c hx.1, fun w hw => by
    rw [act_smul, hx.2 w hw]⟩

theorem mem_Rs {W : Subgroup (GL (Fin 4) K)} {x : Fin 4 → K} :
    x ∈ Rs W ↔ x ∈ Xs W ∧ ∀ w ∈ W, act w x = x := Iff.rfl

theorem Xs_stable {W : Subgroup (GL (Fin 4) K)} {g : GL (Fin 4) K}
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : ∀ v ∈ Xs W, act g v ∈ Xs W := by
  intro v hv
  have hle : Xs W ≤ (Xs W).comap (Matrix.mulVecLin (g : Matrix (Fin 4) (Fin 4) K)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, u, rfl⟩
    show act g (act w u - u) ∈ Xs W
    rw [act_sub]
    have h1 : act g (act w u) = act (g * w * g⁻¹) (act g u) := by
      calc act g (act w u) = act (g * w) u := (act_mul _ _ _).symm
        _ = act ((g * w * g⁻¹) * g) u := by congr 1; group
        _ = act (g * w * g⁻¹) (act g u) := act_mul _ _ _
    rw [h1]
    exact act_sub_mem_Xs (hg w hw) (act g u)
  exact hle hv

theorem Rs_stable {W : Subgroup (GL (Fin 4) K)} {g : GL (Fin 4) K}
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) (hg' : ∀ w ∈ W, g⁻¹ * w * g ∈ W) :
    ∀ x ∈ Rs W, act g x ∈ Rs W := by
  intro x hx
  refine ⟨Xs_stable hg x hx.1, fun w hw => ?_⟩
  have h1 : g⁻¹ * w * g ∈ W := hg' w hw
  have h2 : act (g⁻¹ * w * g) x = x := hx.2 _ h1
  calc act w (act g x) = act (w * g) x := (act_mul _ _ _).symm
    _ = act (g * (g⁻¹ * w * g)) x := by congr 1; group
    _ = act g (act (g⁻¹ * w * g) x) := act_mul _ _ _
    _ = act g x := by rw [h2]

theorem dotB_eq_zero_of_mem_Rs (h : UnitaryFieldData 2 3 K) {W : Subgroup (GL (Fin 4) K)}
    (hWu : ∀ w ∈ W, ((w : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (w : Matrix (Fin 4) (Fin 4) K) = 1)
    {x : Fin 4 → K} (hx : x ∈ Rs W) {y : Fin 4 → K} (hy : y ∈ Xs W) : dotB h x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, hw, u, rfl⟩ := hz
    have e1 := dotB_act h (hWu w hw) x u
    rw [hx.2 w hw] at e1
    rw [dotB_sub_right, e1, sub_self]
  | zero => exact dotB_zero_right h x
  | add a b _ _ ha hb => rw [dotB_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [dotB_smul_right, ha, mul_zero]

theorem Rs_ne_bot (h : UnitaryFieldData 2 3 K) {W : Subgroup (GL (Fin 4) K)} (hW2 : IsPGroup 2 W)
    (hW1 : W ≠ ⊥) (hWu : ∀ w ∈ W, ((w : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (w : Matrix (Fin 4) (Fin 4) K) = 1) :
    Rs W ≠ ⊥ := by
  classical
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstab : ∀ w : ↥W, ∀ v ∈ Xs W, act (w : GL (Fin 4) K) v ∈ Xs W := fun w v hv =>
    Xs_stable (g := (w : GL (Fin 4) K)) (fun w' hw' => W.mul_mem (W.mul_mem w.2 hw') (W.inv_mem w.2)) v hv
  letI : MulAction ↥W ↥(Xs W) :=
    { smul := fun w x => ⟨act (w : GL (Fin 4) K) x.1, hstab w x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by
        show act ((1 : ↥W) : GL (Fin 4) K) x.1 = x.1
        rw [Subgroup.coe_one, act_one])
      mul_smul := fun w w' x => Subtype.ext (by
        show act ((w * w' : ↥W) : GL (Fin 4) K) x.1 = act (w : GL (Fin 4) K) (act (w' : GL (Fin 4) K) x.1)
        rw [Subgroup.coe_mul, act_mul]) }
  have hXne : Xs W ≠ ⊥ := by
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW1
    have hw1 : (w : GL (Fin 4) K) ≠ 1 := fun e => hw (Subtype.ext e)
    have : ∃ u : Fin 4 → K, act (w : GL (Fin 4) K) u ≠ u := by
      by_contra hcon
      push Not at hcon
      apply hw1
      apply Units.ext
      apply Matrix.ext_of_mulVec_single
      intro i
      rw [Units.val_one, Matrix.one_mulVec]
      exact hcon (Pi.single i 1)
    obtain ⟨u, hu⟩ := this
    intro hbot
    apply hu
    have hmem : act (w : GL (Fin 4) K) u - u ∈ Xs W := act_sub_mem_Xs w.2 u
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  have hcardX : Even (Nat.card (Xs W)) := by
    have hfin : Module.Finite K (Xs W) := inferInstance
    have hr : Module.finrank K (Xs W) ≠ 0 := fun h0 => hXne (Submodule.finrank_eq_zero.1 h0)
    rw [Module.natCard_eq_pow_finrank (K := K), h.card]
    exact Nat.even_pow.2 ⟨⟨32, rfl⟩, hr⟩
  have hcount := hW2.card_modEq_card_fixedPoints (Xs W)
  by_contra hcon
  have hfixed : MulAction.fixedPoints ↥W ↥(Xs W) = {0} := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ w : ↥W, act (w : GL (Fin 4) K) x.1 = x.1 := fun w => by
        have := hx w
        exact congrArg Subtype.val this
      have hxR : x.1 ∈ Rs W := ⟨x.2, fun w hw => hx' ⟨w, hw⟩⟩
      rw [hcon, Submodule.mem_bot] at hxR
      exact Subtype.ext hxR
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      intro w
      exact Subtype.ext (by
        show act ((w : ↥W) : GL (Fin 4) K) 0 = 0
        simp [act])
  have h1 : Nat.card ↥({0} : Set ↥(Xs W)) = 1 := by simp
  rw [hfixed, h1] at hcount
  unfold Nat.ModEq at hcount
  obtain ⟨r, hr⟩ := hcardX
  omega

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8
