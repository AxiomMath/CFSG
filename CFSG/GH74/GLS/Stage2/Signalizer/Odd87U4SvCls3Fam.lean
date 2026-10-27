module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Irred

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix
open scoped MatrixGroups

section Fam

variable {F H : Type} [Field F] [Group H]

structure AdFam (e : Fin 3 → F) (Y : H →* Matrix (Fin 3) (Fin 3) F) : Prop where
  iso : ∀ S, (Y S)ᵀ * Matrix.diagonal e * Y S = Matrix.diagonal e
  irr : ∀ W : Submodule F (Fin 3 → F), (∀ S, ∀ v ∈ W, Y S *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  comm : ∀ T : Matrix (Fin 3) (Fin 3) F, (∀ S, T * Y S = Y S * T) →
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F)

variable {e : Fin 3 → F} {Y : H →* Matrix (Fin 3) (Fin 3) F}

theorem AdFam.fixed_vec (hY : AdFam e Y) {v : Fin 3 → F} (hv : ∀ S, Y S *ᵥ v = v) : v = 0 := by
  have hinv : ∀ S, ∀ w ∈ Submodule.span F {v}, Y S *ᵥ w ∈ Submodule.span F {v} := by
    intro S w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, hv S]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  rcases hY.irr _ hinv with h | h
  · have : v ∈ Submodule.span F {v} := Submodule.mem_span_singleton_self v
    rw [h] at this
    exact this
  · exfalso
    have ha : (Pi.single 0 1 : Fin 3 → F) ∈ Submodule.span F {v} := by rw [h]; trivial
    have hb : (Pi.single 1 1 : Fin 3 → F) ∈ Submodule.span F {v} := by rw [h]; trivial
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hb
    have h0 := congrFun hα 0
    have h1 := congrFun hα 1
    have g0 := congrFun hβ 0
    have g1 := congrFun hβ 1
    simp at h0 h1 g0 g1
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp at h0
    have hv1 : v 1 = 0 := h1.resolve_left hα0
    rw [hv1, mul_zero] at g1
    exact zero_ne_one g1

theorem AdFam.fixed_row (hY : AdFam e Y) (he : ∀ i, e i ≠ 0) {r : Fin 3 → F}
    (hr : ∀ S, r ᵥ* Y S = r) : r = 0 := by
  have hDinv := cls3_diagonal_inv_mul he
  have hDinv' := cls3_diagonal_mul_inv he
  set u : Fin 3 → F := (Matrix.diagonal fun i => (e i)⁻¹) *ᵥ r with hu
  have hRu : Matrix.diagonal e *ᵥ u = r := by
    rw [hu, Matrix.mulVec_mulVec, hDinv', Matrix.one_mulVec]
  have hfix : ∀ S, Y S *ᵥ u = u := by
    intro S
    have hT := hr S⁻¹
    have hmul : Y S⁻¹ * Y S = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have key : (Y S⁻¹)ᵀ * Matrix.diagonal e = Matrix.diagonal e * Y S := by
      calc (Y S⁻¹)ᵀ * Matrix.diagonal e
          = (Y S⁻¹)ᵀ * Matrix.diagonal e * (Y S⁻¹ * Y S) := by rw [hmul, Matrix.mul_one]
        _ = ((Y S⁻¹)ᵀ * Matrix.diagonal e * Y S⁻¹) * Y S := by simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal e * Y S := by rw [hY.iso S⁻¹]
    have h1 : Matrix.diagonal e *ᵥ (Y S *ᵥ u) = Matrix.diagonal e *ᵥ u := by
      rw [Matrix.mulVec_mulVec, ← key, ← Matrix.mulVec_mulVec, hRu, Matrix.mulVec_transpose, hT]
    have h3 := congrArg (fun z => (Matrix.diagonal fun i => (e i)⁻¹) *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hDinv, Matrix.one_mul,
      Matrix.one_mulVec] at h3
    exact h3
  have hu0 := hY.fixed_vec hfix
  rw [← hRu, hu0, Matrix.mulVec_zero]

theorem AdFam.dichotomyA (hY : AdFam e Y) (W : Submodule F (Fin 4 → F))
    (hW : ∀ S, ∀ w ∈ W, eFirst (Y S) *ᵥ w ∈ W) :
    (∀ w ∈ W, w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) ∨ (∀ u : Fin 3 → F, cls3LowA u ∈ W) := by
  have hinv : ∀ S, ∀ u ∈ W.comap cls3LowA, Y S *ᵥ u ∈ W.comap cls3LowA := by
    intro S u hu
    rw [Submodule.mem_comap] at hu ⊢
    have h1 := hW S _ hu
    rwa [cls3_eFirst_mulVec_lowA] at h1
  rcases hY.irr (W.comap cls3LowA) hinv with h | h
  · left
    intro w hw
    have hfix : ∀ S, Y S *ᵥ ![w 1, w 2, w 3] = ![w 1, w 2, w 3] := by
      intro S
      have h1 := W.sub_mem (hW S w hw) hw
      have h3 : eFirst (Y S) *ᵥ w - w =
          cls3LowA (Y S *ᵥ ![w 1, w 2, w 3] - ![w 1, w 2, w 3]) := by
        rw [cls3_eFirst_mulVec, cls3LowA_apply]
        funext i
        fin_cases i <;> simp
      rw [h3] at h1
      have h4 : Y S *ᵥ ![w 1, w 2, w 3] - ![w 1, w 2, w 3] ∈ W.comap cls3LowA := h1
      rw [h, Submodule.mem_bot, sub_eq_zero] at h4
      exact h4
    have h5 := hY.fixed_vec hfix
    exact ⟨congrFun h5 0, congrFun h5 1, congrFun h5 2⟩
  · right
    intro u
    have : u ∈ W.comap cls3LowA := by rw [h]; trivial
    exact this

theorem AdFam.dichotomyB (hY : AdFam e Y) (W : Submodule F (Fin 4 → F))
    (hW : ∀ S, ∀ w ∈ W, eLast (Y S) *ᵥ w ∈ W) :
    (∀ w ∈ W, w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) ∨ (∀ u : Fin 3 → F, cls3LowB u ∈ W) := by
  have hinv : ∀ S, ∀ u ∈ W.comap cls3LowB, Y S *ᵥ u ∈ W.comap cls3LowB := by
    intro S u hu
    rw [Submodule.mem_comap] at hu ⊢
    have h1 := hW S _ hu
    rwa [cls3_eLast_mulVec_lowB] at h1
  rcases hY.irr (W.comap cls3LowB) hinv with h | h
  · left
    intro w hw
    have hfix : ∀ S, Y S *ᵥ ![w 0, w 1, w 2] = ![w 0, w 1, w 2] := by
      intro S
      have h1 := W.sub_mem (hW S w hw) hw
      have h3 : eLast (Y S) *ᵥ w - w =
          cls3LowB (Y S *ᵥ ![w 0, w 1, w 2] - ![w 0, w 1, w 2]) := by
        rw [cls3_eLast_mulVec, cls3LowB_apply]
        funext i
        fin_cases i <;> simp
      rw [h3] at h1
      have h4 : Y S *ᵥ ![w 0, w 1, w 2] - ![w 0, w 1, w 2] ∈ W.comap cls3LowB := h1
      rw [h, Submodule.mem_bot, sub_eq_zero] at h4
      exact h4
    have h5 := hY.fixed_vec hfix
    exact ⟨congrFun h5 0, congrFun h5 1, congrFun h5 2⟩
  · right
    intro u
    have : u ∈ W.comap cls3LowB := by rw [h]; trivial
    exact this

theorem AdFam.cent_A (hY : AdFam e Y) (he : ∀ i, e i ≠ 0) {x : Matrix (Fin 4) (Fin 4) F}
    (hx : ∀ S, x * eFirst (Y S) = eFirst (Y S) * x) :
    ∃ c : F, x 1 1 = c ∧ x 2 2 = c ∧ x 3 3 = c ∧ x 1 2 = 0 ∧ x 1 3 = 0 ∧ x 2 1 = 0 ∧ x 2 3 = 0 ∧
      x 3 1 = 0 ∧ x 3 2 = 0 ∧ x 1 0 = 0 ∧ x 2 0 = 0 ∧ x 3 0 = 0 ∧ x 0 1 = 0 ∧ x 0 2 = 0 ∧
      x 0 3 = 0 := by
  have hc := fun S => commute_eFirst (hx S)
  obtain ⟨c, hc'⟩ := hY.comm (Matrix.of fun i j : Fin 3 => x i.succ j.succ) (fun S => (hc S).1)
  have hcol := hY.fixed_vec (fun S => (hc S).2.1)
  have hrow := hY.fixed_row he (fun S => (hc S).2.2)
  have c00 := congrFun (congrFun hc' 0) 0
  have c01 := congrFun (congrFun hc' 0) 1
  have c02 := congrFun (congrFun hc' 0) 2
  have c10 := congrFun (congrFun hc' 1) 0
  have c11 := congrFun (congrFun hc' 1) 1
  have c12 := congrFun (congrFun hc' 1) 2
  have c20 := congrFun (congrFun hc' 2) 0
  have c21 := congrFun (congrFun hc' 2) 1
  have c22 := congrFun (congrFun hc' 2) 2
  have r0 := congrFun hcol 0
  have r1 := congrFun hcol 1
  have r2 := congrFun hcol 2
  have s0 := congrFun hrow 0
  have s1 := congrFun hrow 1
  have s2 := congrFun hrow 2
  simp at c00 c01 c02 c10 c11 c12 c20 c21 c22 r0 r1 r2 s0 s1 s2
  exact ⟨c, c00, c11, c22, c01, c02, c10, c12, c20, c21, r0, r1, r2, s0, s1, s2⟩

theorem AdFam.cent_B (hY : AdFam e Y) (he : ∀ i, e i ≠ 0) {x : Matrix (Fin 4) (Fin 4) F}
    (hx : ∀ S, x * eLast (Y S) = eLast (Y S) * x) :
    ∃ c : F, x 0 0 = c ∧ x 1 1 = c ∧ x 2 2 = c ∧ x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 1 0 = 0 ∧ x 1 2 = 0 ∧
      x 2 0 = 0 ∧ x 2 1 = 0 ∧ x 0 3 = 0 ∧ x 1 3 = 0 ∧ x 2 3 = 0 ∧ x 3 0 = 0 ∧ x 3 1 = 0 ∧
      x 3 2 = 0 := by
  have hc := fun S => commute_eLast (hx S)
  obtain ⟨c, hc'⟩ := hY.comm (Matrix.of fun i j : Fin 3 => x i.castSucc j.castSucc)
    (fun S => (hc S).1)
  have hcol := hY.fixed_vec (fun S => (hc S).2.1)
  have hrow := hY.fixed_row he (fun S => (hc S).2.2)
  have c00 := congrFun (congrFun hc' 0) 0
  have c01 := congrFun (congrFun hc' 0) 1
  have c02 := congrFun (congrFun hc' 0) 2
  have c10 := congrFun (congrFun hc' 1) 0
  have c11 := congrFun (congrFun hc' 1) 1
  have c12 := congrFun (congrFun hc' 1) 2
  have c20 := congrFun (congrFun hc' 2) 0
  have c21 := congrFun (congrFun hc' 2) 1
  have c22 := congrFun (congrFun hc' 2) 2
  have r0 := congrFun hcol 0
  have r1 := congrFun hcol 1
  have r2 := congrFun hcol 2
  have s0 := congrFun hrow 0
  have s1 := congrFun hrow 1
  have s2 := congrFun hrow 2
  simp at c00 c01 c02 c10 c11 c12 c20 c21 c22 r0 r1 r2 s0 s1 s2
  exact ⟨c, c00, c11, c22, c01, c02, c10, c12, c20, c21, r0, r1, r2, s0, s1, s2⟩

end Fam

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
