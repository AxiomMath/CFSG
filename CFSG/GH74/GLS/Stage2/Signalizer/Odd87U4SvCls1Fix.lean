module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls1Model

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace U4C1

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Alpha0

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def u4A0El : hypSU h 2 0 := hypOf (u4A0 : Matrix (Fin 4) (Fin 4) K) (isU4_A0 h)

theorem u4A0El_mem : (⟨((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K), RingEquiv.refl K⟩ :
    SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0 := by
  refine ⟨1, one_ne_zero, map_one _, ?_⟩
  rw [one_smul]
  exact (mem_hypSU.1 (u4A0El h).2).1

@[expose] noncomputable def u4Alpha0 : MulAut (hypPSU h 2 0) :=
  semilinearAutHom h (by norm_num) (by norm_num) ⟨_, u4A0El_mem h⟩

theorem mem_fixSub_alpha0 (g z : hypSU h 2 0) (hz : z ∈ hypScalars h 2 0)
    (hgz : ((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) =
      (z : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) *
        ((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K)) :
    hypProj h 2 0 g ∈ fixSub (u4Alpha0 h) := by
  rw [mem_fixSub, u4Alpha0, semilinearAutHom_apply]
  have key : (⟨_, conj_mem_hypSU (u4A0El_mem h) g⟩ : hypSU h 2 0) = z * g := by
    apply Subtype.ext
    change ((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K) * glAut (RingEquiv.refl K)
      (g : GL (HypIndex 2 0) K) * ((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K)⁻¹ =
        (z : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K)
    rw [glAut_refl, mul_inv_eq_iff_eq_mul, hgz]
  have hz1 : hypProj h 2 0 z = 1 := by
    rw [← MonoidHom.mem_ker, ker_hypProj]
    exact hz
  rw [key, map_mul, hz1, one_mul]

theorem toHyp_neg_one : toHyp (-1 : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (HypIndex 2 0) (-1 : K) := by
  ext a b
  by_cases hab : a = b <;>
    simp [toHyp, Matrix.scalar_apply, hyp4.injective.eq_iff, hab]

theorem hypOf_neg_one_mem : hypOf (-1 : Matrix (Fin 4) (Fin 4) K) (isU4_neg h) ∈ hypScalars h 2 0 := by
  refine ⟨-1, ?_, by norm_num, ?_⟩
  · simp [UnitaryFieldData.norm]
  · apply Units.ext
    rw [coe_hypOf, toHyp_neg_one, GeneralLinearGroup.coe_scalar]
    simp

theorem mem_fixSub_alpha0_of_comm {X : Matrix (Fin 4) (Fin 4) K} (hX : IsU4 h X)
    (hcomm : u4A0 * X = X * u4A0) : hypProj h 2 0 (hypOf X hX) ∈ fixSub (u4Alpha0 h) := by
  refine mem_fixSub_alpha0 h _ 1 (one_mem _) ?_
  apply Units.ext
  simp only [u4A0El, Units.val_mul, Subgroup.coe_one, one_mul, coe_hypOf]
  rw [← toHyp_mul, ← toHyp_mul, hcomm]

theorem mem_fixSub_alpha0_of_anticomm {X : Matrix (Fin 4) (Fin 4) K} (hX : IsU4 h X)
    (hanti : u4A0 * X = -(X * u4A0)) : hypProj h 2 0 (hypOf X hX) ∈ fixSub (u4Alpha0 h) := by
  refine mem_fixSub_alpha0 h _ (hypOf (-1 : Matrix (Fin 4) (Fin 4) K) (isU4_neg h))
    (hypOf_neg_one_mem h) ?_
  apply Units.ext
  simp only [u4A0El, Units.val_mul, coe_hypOf]
  rw [← toHyp_mul, ← toHyp_mul, ← toHyp_mul, hanti]
  congr 1
  simp

end Alpha0

section IrredStd

variable {p f : ℕ} {K : Type} [Field K]

theorem u4U_mulVec (c : K) (w : Fin 4 → K) :
    (u4U c : Matrix (Fin 4) (Fin 4) K) *ᵥ w = ![w 0 + c * w 2, w 1, w 2, w 3] := by
  funext i
  fin_cases i <;> simp [u4U, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem u4L_mulVec (c : K) (w : Fin 4 → K) :
    (u4L c : Matrix (Fin 4) (Fin 4) K) *ᵥ w = ![w 0, w 1, c * w 0 + w 2, w 3] := by
  funext i
  fin_cases i <;> simp [u4L, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem u4Sw_mulVec (w : Fin 4 → K) :
    (u4Sw : Matrix (Fin 4) (Fin 4) K) *ᵥ w = ![w 1, w 0, w 3, w 2] := by
  funext i
  fin_cases i <;> simp [u4Sw, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem u4_irred4 {τ : K} (hτ0 : τ ≠ 0) (W : Submodule K (Fin 4 → K))
    (hU : ∀ w ∈ W, (u4U τ : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W)
    (hL : ∀ w ∈ W, (u4L τ : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W)
    (hS : ∀ w ∈ W, (u4Sw : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hU' : ∀ w ∈ W, (τ * w 2) • (Pi.single 0 1 : Fin 4 → K) ∈ W := by
    intro w hw
    have h1 := W.sub_mem (hU w hw) hw
    rw [u4U_mulVec] at h1
    convert h1 using 1
    funext i
    fin_cases i <;> simp
  have hL' : ∀ w ∈ W, (τ * w 0) • (Pi.single 2 1 : Fin 4 → K) ∈ W := by
    intro w hw
    have h1 := W.sub_mem (hL w hw) hw
    rw [u4L_mulVec] at h1
    convert h1 using 1
    funext i
    fin_cases i <;> simp
  have hS' : ∀ w ∈ W, ![w 1, w 0, w 3, w 2] ∈ W := fun w hw => by
    rw [← u4Sw_mulVec]
    exact hS w hw
  have hfirst : ∀ w ∈ W, (w 0 ≠ 0 ∨ w 2 ≠ 0) →
      (Pi.single 0 1 : Fin 4 → K) ∈ W ∧ (Pi.single 2 1 : Fin 4 → K) ∈ W := by
    intro w hw hc
    rcases hc with h0 | h2
    · have he2 : (Pi.single 2 1 : Fin 4 → K) ∈ W := by
        have := W.smul_mem (τ * w 0)⁻¹ (hL' w hw)
        rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ0 h0), one_smul] at this
      have he0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
        have := W.smul_mem τ⁻¹ (hU' _ he2)
        simpa [smul_smul, inv_mul_cancel₀ hτ0] using this
      exact ⟨he0, he2⟩
    · have he0 : (Pi.single 0 1 : Fin 4 → K) ∈ W := by
        have := W.smul_mem (τ * w 2)⁻¹ (hU' w hw)
        rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ0 h2), one_smul] at this
      have he2 : (Pi.single 2 1 : Fin 4 → K) ∈ W := by
        have := W.smul_mem τ⁻¹ (hL' _ he0)
        simpa [smul_smul, inv_mul_cancel₀ hτ0] using this
      exact ⟨he0, he2⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.mpr fun w hw => by simpa using hcon w hw)
  have hfirst' : (Pi.single 0 1 : Fin 4 → K) ∈ W ∧ (Pi.single 2 1 : Fin 4 → K) ∈ W := by
    by_cases hc : w 0 ≠ 0 ∨ w 2 ≠ 0
    · exact hfirst w hw hc
    · push Not at hc
      have hc2 : w 1 ≠ 0 ∨ w 3 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hw0
        funext i
        fin_cases i <;> simp [hc.1, hc.2, hcon.1, hcon.2]
      exact hfirst _ (hS' w hw) (by simpa using hc2)
  obtain ⟨he0, he2⟩ := hfirst'
  have he1 : (Pi.single 1 1 : Fin 4 → K) ∈ W := by
    have := hS' _ he0
    convert this using 1
    funext i
    fin_cases i <;> simp
  have he3 : (Pi.single 3 1 : Fin 4 → K) ∈ W := by
    have := hS' _ he2
    convert this using 1
    funext i
    fin_cases i <;> simp
  rw [eq_top_iff]
  intro v _
  have hv : v = v 0 • (Pi.single 0 1 : Fin 4 → K) + v 1 • (Pi.single 1 1 : Fin 4 → K) +
      v 2 • (Pi.single 2 1 : Fin 4 → K) + v 3 • (Pi.single 3 1 : Fin 4 → K) := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)) (W.smul_mem _ he2))
    (W.smul_mem _ he3)

@[expose] def vecW4 (W : Submodule K (HypIndex 2 0 → K)) : Submodule K (Fin 4 → K) where
  carrier := {u | u ∘ hyp4 ∈ W}
  add_mem' {a b} ha hb := by
    have := W.add_mem ha hb
    exact this
  zero_mem' := W.zero_mem
  smul_mem' c u hu := by
    have := W.smul_mem c hu
    exact this

theorem mem_vecW4 {W : Submodule K (HypIndex 2 0 → K)} {u : Fin 4 → K} :
    u ∈ vecW4 W ↔ u ∘ hyp4 ∈ W := Iff.rfl

theorem eq_bot_or_top_of_vecW4 {W : Submodule K (HypIndex 2 0 → K)}
    (hW : vecW4 W = ⊥ ∨ vecW4 W = ⊤) : W = ⊥ ∨ W = ⊤ := by
  rcases hW with h0 | h1
  · left
    rw [eq_bot_iff]
    intro w hw
    have hmem : w ∘ hyp4.symm ∈ vecW4 W := by
      rw [mem_vecW4, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
      exact hw
    rw [h0, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    funext a
    have := congrFun hmem (hyp4 a)
    simpa using this
  · right
    rw [eq_top_iff]
    intro w _
    have hmem : w ∘ hyp4.symm ∈ vecW4 W := by rw [h1]; exact Submodule.mem_top
    rw [mem_vecW4, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at hmem
    exact hmem

theorem vecW4_stable (h : UnitaryFieldData p f K) {W : Submodule K (HypIndex 2 0 → K)}
    {X : Matrix (Fin 4) (Fin 4) K} (hX : IsU4 h X)
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub (u4Alpha0 h) → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W)
    (hfix : hypProj h 2 0 (hypOf X hX) ∈ fixSub (u4Alpha0 h)) :
    ∀ u ∈ vecW4 W, X *ᵥ u ∈ vecW4 W := by
  intro u hu
  have := hW (hypOf X hX) hfix _ hu
  rw [coe_hypOf, toHyp_mulVec] at this
  exact this

theorem u4_cls1_irred_std (h : UnitaryFieldData p f K) (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub (u4Alpha0 h) → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hτ0 : c - h.bar c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  have hτ : h.bar (c - h.bar c) = -(c - h.bar c) := by
    rw [map_sub, h.bar_bar]; ring
  refine eq_bot_or_top_of_vecW4 (u4_irred4 hτ0 (vecW4 W) ?_ ?_ ?_)
  · exact vecW4_stable h (isU4_U h hτ) hW (mem_fixSub_alpha0_of_comm h (isU4_U h hτ) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u4A0, u4U, Matrix.mul_apply, Fin.sum_univ_four]))
  · exact vecW4_stable h (isU4_L h hτ) hW (mem_fixSub_alpha0_of_comm h (isU4_L h hτ) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u4A0, u4L, Matrix.mul_apply, Fin.sum_univ_four]))
  · exact vecW4_stable h (isU4_Sw h) hW (mem_fixSub_alpha0_of_anticomm h (isU4_Sw h) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u4A0, u4Sw, Matrix.mul_apply, Fin.sum_univ_four]))

end IrredStd

end U4C1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
