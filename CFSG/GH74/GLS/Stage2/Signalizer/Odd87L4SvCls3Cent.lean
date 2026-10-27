module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Hom

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Cent

variable {F : Type} [Field F]

theorem cls3_cent_A {e : Fin 3 → F} {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd e ρ)
    (he : ∀ i, e i ≠ 0) (h2 : (2 : F) ≠ 0) {x : Matrix (Fin 4) (Fin 4) F}
    (hx : ∀ S : SL(2, F), x * eFirst (ρ S : Matrix (Fin 3) (Fin 3) F) =
      eFirst (ρ S : Matrix (Fin 3) (Fin 3) F) * x) :
    ∃ c : F, x 1 1 = c ∧ x 2 2 = c ∧ x 3 3 = c ∧ x 1 2 = 0 ∧ x 1 3 = 0 ∧ x 2 1 = 0 ∧ x 2 3 = 0 ∧
      x 3 1 = 0 ∧ x 3 2 = 0 ∧ x 1 0 = 0 ∧ x 2 0 = 0 ∧ x 3 0 = 0 ∧ x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 0 3 = 0 := by
  have hc := fun S => commute_eFirst (hx S)
  obtain ⟨c, hc'⟩ := hρ.comm (Matrix.of fun i j : Fin 3 => x i.succ j.succ) (fun S => (hc S).1)
  have hcol := hρ.fixed_vec h2 (fun S => (hc S).2.1)
  have hrow := hρ.fixed_row he h2 (fun S => (hc S).2.2)
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

theorem cls3_cent_B {e : Fin 3 → F} {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd e ρ)
    (he : ∀ i, e i ≠ 0) (h2 : (2 : F) ≠ 0) {x : Matrix (Fin 4) (Fin 4) F}
    (hx : ∀ S : SL(2, F), x * eLast (ρ S : Matrix (Fin 3) (Fin 3) F) =
      eLast (ρ S : Matrix (Fin 3) (Fin 3) F) * x) :
    ∃ c : F, x 0 0 = c ∧ x 1 1 = c ∧ x 2 2 = c ∧ x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 1 0 = 0 ∧ x 1 2 = 0 ∧
      x 2 0 = 0 ∧ x 2 1 = 0 ∧ x 0 3 = 0 ∧ x 1 3 = 0 ∧ x 2 3 = 0 ∧ x 3 0 = 0 ∧ x 3 1 = 0 ∧ x 3 2 = 0 := by
  have hc := fun S => commute_eLast (hx S)
  obtain ⟨c, hc'⟩ := hρ.comm (Matrix.of fun i j : Fin 3 => x i.castSucc j.castSucc) (fun S => (hc S).1)
  have hcol := hρ.fixed_vec h2 (fun S => (hc S).2.1)
  have hrow := hρ.fixed_row he h2 (fun S => (hc S).2.2)
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

theorem cls3_scalar_of_entries {x : Matrix (Fin 4) (Fin 4) F} {c c' : F}
    (a11 : x 1 1 = c) (a22 : x 2 2 = c) (a33 : x 3 3 = c) (a12 : x 1 2 = 0) (a13 : x 1 3 = 0)
    (a21 : x 2 1 = 0) (a23 : x 2 3 = 0) (a31 : x 3 1 = 0) (a32 : x 3 2 = 0) (a10 : x 1 0 = 0)
    (a20 : x 2 0 = 0) (a30 : x 3 0 = 0) (a01 : x 0 1 = 0) (a02 : x 0 2 = 0) (a03 : x 0 3 = 0)
    (b00 : x 0 0 = c') (b11 : x 1 1 = c') :
    x = Matrix.scalar (Fin 4) c := by
  have hcc : c' = c := b11.symm.trans a11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, *]

end Cent

section Final

variable {F : Type} [Field F] [Finite F]

theorem l4_cls3_cent_std (hodd : Odd (Nat.card F)) {D : GL (Fin 4) F} {d : Fin 4 → F}
    (hd : ∀ i, d i ≠ 0) (hD : ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d)
    (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub (conjAut 4 F D * dualAut 4 F)) →
      ∀ g, x * ι g = ι g * x) :
    x ∈ scalars 4 F := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hdA : ∀ i, (![d 1, d 2, d 3] : Fin 3 → F) i ≠ 0 := fun i => by fin_cases i <;> simp [hd]
  have hdB : ∀ i, (![d 0, d 1, d 2] : Fin 3 → F) i ≠ 0 := fun i => by fin_cases i <;> simp [hd]
  obtain ⟨ρA, hA⟩ := exists_diagAd hodd _ hdA
  obtain ⟨ρB, hB⟩ := exists_diagAd hodd _ hdB
  have hxA : ∀ S : SL(2, F), (x : Matrix (Fin 4) (Fin 4) F) *
      eFirst (ρA S : Matrix (Fin 3) (Fin 3) F) = eFirst (ρA S : Matrix (Fin 3) (Fin 3) F) * x := by
    intro S
    have := congrArg Subtype.val (h (cls3IotaA ρA) (proj_cls3IotaA_mem hD hA) S)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_cls3IotaA] at this
  have hxB : ∀ S : SL(2, F), (x : Matrix (Fin 4) (Fin 4) F) *
      eLast (ρB S : Matrix (Fin 3) (Fin 3) F) = eLast (ρB S : Matrix (Fin 3) (Fin 3) F) * x := by
    intro S
    have := congrArg Subtype.val (h (cls3IotaB ρB) (proj_cls3IotaB_mem hD hB) S)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_cls3IotaB] at this
  obtain ⟨c, a11, a22, a33, a12, a13, a21, a23, a31, a32, a10, a20, a30, a01, a02, a03⟩ :=
    cls3_cent_A hA hdA h2 hxA
  obtain ⟨c', b00, b11, -⟩ := cls3_cent_B hB hdB h2 hxB
  have hx : (x : Matrix (Fin 4) (Fin 4) F) = Matrix.scalar (Fin 4) c :=
    cls3_scalar_of_entries a11 a22 a33 a12 a13 a21 a23 a31 a32 a10 a20 a30 a01 a02 a03 b00 b11
  have hdet : c ^ 4 = 1 := by
    have h1 := x.2
    rw [hx] at h1
    simpa [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_four, pow_succ, mul_assoc] using h1
  have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hdet), hx⟩

end Final

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
