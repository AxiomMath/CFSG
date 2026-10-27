module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section SL2

variable {F : Type} [Field F]

theorem diagGL_one : (diagGL (1 : Fˣ) : GL (Fin 2) F) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL]

theorem sl2_A_mul_WSL (A : SL2 F) (hA : (A : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, -1]) :
    A * WSL = (-1 * WSL) * A := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [hA, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem glConjSL_diagGL_neg_one_WSL : glConjSL (diagGL (-1 : Fˣ)) (WSL : SL2 F) = -1 * WSL := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [glConjSL_coe, diagGL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Conj

variable {F : Type} [Field F] [Finite F]


theorem adjointGroup_le_sup_of_conj {x y : ModGL Tag.G2 F}
    (hx : x ∈ toralCentralizer Tag.G2 F ![-1, 1])
    (h : adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({x * y * x⁻¹} : Set (ModGL Tag.G2 F)))) :
    adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) := by
  have hxA : x ∈ adjointGroup Tag.G2 F := (mem_toralCentralizer.mp hx).1
  set M := toralCentralizer Tag.G2 F ![-1, 1] ⊔
    (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({y} : Set (ModGL Tag.G2 F))) with hM
  have hxM : x ∈ M := Subgroup.mem_sup_left hx
  have hle : toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer ({x * y * x⁻¹} : Set (ModGL Tag.G2 F))) ≤
      M.comap (MulAut.conj x⁻¹).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · show x⁻¹ * a * x⁻¹⁻¹ ∈ M
      rw [inv_inv]
      exact Subgroup.mem_sup_left (mul_mem (mul_mem (inv_mem hx) ha) hx)
    · obtain ⟨hbA, hbC⟩ := hb
      show x⁻¹ * b * x⁻¹⁻¹ ∈ M
      rw [inv_inv]
      refine Subgroup.mem_sup_right
        (Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hxA) hbA) hxA, ?_⟩)
      have hbc : b * (x * y * x⁻¹) = x * y * x⁻¹ * b :=
        Subgroup.mem_centralizer_singleton_iff.mp hbC
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * b * x * y = x⁻¹ * (b * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹ * b) * x := by rw [hbc]
        _ = y * (x⁻¹ * b * x) := by group
  intro g hg
  have h1 : g ∈ M.comap (MulAut.conj x⁻¹).toMonoidHom := hle (h hg)
  have h2 : x⁻¹ * g * x⁻¹⁻¹ ∈ M := h1
  rw [inv_inv] at h2
  have e : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hxM h2) (inv_mem hxM)

theorem exists_partner_m0 (hodd : Odd (Nat.card F)) (h3 : (3 : F) = 0)
    (b : Fin Tag.G2.rank → Fˣ) (hb : b g2i1 = 1 ∨ b g2i1 = -1) :
    ∃ x ∈ toralCentralizer Tag.G2 F ![-1, 1],
      x * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * x⁻¹ =
        rootDiagUnit Tag.G2 (g2tup (-(b g2i0)) (b g2i1)) *
          (g2ChartA F WSL * g2ChartB F WSL) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  have ha0 : a g2i0 = -1 := by rw [ha]; rfl
  have ha1 : a g2i1 = 1 := by rw [ha]; rfl
  have hdn : g2ChartA F (-1) = rootDiagUnit Tag.G2 a := g2ChartA_neg_one hodd ha
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have hmul : rootDiagUnit Tag.G2 (g2tup (-(b g2i0)) (b g2i1)) =
      rootDiagUnit Tag.G2 b * rootDiagUnit Tag.G2 a := by
    rw [← rootDiagUnit_mul]
    congr 1
    refine g2tup_ext ?_ ?_
    · show -(b g2i0) = b g2i0 * a g2i0
      rw [ha0, mul_neg_one]
    · show b g2i1 = b g2i1 * a g2i1
      rw [ha1, mul_one]
  rcases hb with hb | hb
  ·
    let A : SL2 F := ⟨!![1, 1; 1, -1], by
      rw [Matrix.det_fin_two_of]
      linear_combination (-1 : F) * h3⟩
    have hA : (A : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, -1] := rfl
    refine ⟨g2ChartA F A, g2ChartA_mem_toralCentralizer hodd (a := ![-1, 1]) rfl A, ?_⟩
    have hdb : rootDiagUnit Tag.G2 b * g2ChartA F A * (rootDiagUnit Tag.G2 b)⁻¹ = g2ChartA F A := by
      have h := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) 1 g2i1 b A
      rw [one_smul, rootChar_single_g2, hb, diagGL_one, glConjSL_one] at h
      exact h
    have hxd : g2ChartA F A * rootDiagUnit Tag.G2 b * (g2ChartA F A)⁻¹ = rootDiagUnit Tag.G2 b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (mul_inv_eq_iff_eq_mul.mp hdb).symm
    have hAW : A * WSL * A⁻¹ = -1 * WSL := mul_inv_eq_iff_eq_mul.mpr (sl2_A_mul_WSL A hA)
    have hxm : g2ChartA F A * (g2ChartA F WSL * g2ChartB F WSL) * (g2ChartA F A)⁻¹ =
        rootDiagUnit Tag.G2 a * (g2ChartA F WSL * g2ChartB F WSL) := by
      have hc : Commute (g2ChartA F A) (g2ChartB F WSL) := hcomm A WSL
      have hc' : (g2ChartA F A)⁻¹ * g2ChartB F WSL = g2ChartB F WSL * (g2ChartA F A)⁻¹ :=
        (Commute.inv_left hc).eq
      calc g2ChartA F A * (g2ChartA F WSL * g2ChartB F WSL) * (g2ChartA F A)⁻¹
          = g2ChartA F A * g2ChartA F WSL * (g2ChartB F WSL * (g2ChartA F A)⁻¹) := by group
        _ = g2ChartA F A * g2ChartA F WSL * ((g2ChartA F A)⁻¹ * g2ChartB F WSL) := by rw [hc']
        _ = g2ChartA F (A * WSL * A⁻¹) * g2ChartB F WSL := by
            simp only [map_mul, map_inv]; group
        _ = g2ChartA F (-1) * g2ChartA F WSL * g2ChartB F WSL := by
            rw [hAW, map_mul]
        _ = _ := by rw [hdn]; group
    calc g2ChartA F A * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) *
          (g2ChartA F A)⁻¹
        = (g2ChartA F A * rootDiagUnit Tag.G2 b * (g2ChartA F A)⁻¹) *
          (g2ChartA F A * (g2ChartA F WSL * g2ChartB F WSL) * (g2ChartA F A)⁻¹) := by group
      _ = rootDiagUnit Tag.G2 b * (rootDiagUnit Tag.G2 a *
          (g2ChartA F WSL * g2ChartB F WSL)) := by rw [hxd, hxm]
      _ = _ := by rw [hmul]; group
  ·
    refine ⟨g2ChartA F WSL, g2ChartA_mem_toralCentralizer hodd (a := ![-1, 1]) rfl WSL, ?_⟩
    have hK1 : (rootDiagUnit Tag.G2 b)⁻¹ * g2ChartA F WSL * rootDiagUnit Tag.G2 b =
        rootDiagUnit Tag.G2 a * g2ChartA F WSL := by
      have h := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) 1 g2i1 b⁻¹ WSL
      rw [one_smul, rootChar_single_g2, rootDiagUnit_inv, Pi.inv_apply, hb, inv_neg, inv_one,
        glConjSL_diagGL_neg_one_WSL, inv_inv, map_mul, hdn] at h
      exact h
    have hK2 : g2ChartA F WSL * rootDiagUnit Tag.G2 b =
        rootDiagUnit Tag.G2 b * (rootDiagUnit Tag.G2 a * g2ChartA F WSL) := by
      calc g2ChartA F WSL * rootDiagUnit Tag.G2 b
          = rootDiagUnit Tag.G2 b * ((rootDiagUnit Tag.G2 b)⁻¹ * g2ChartA F WSL *
              rootDiagUnit Tag.G2 b) := by group
        _ = _ := by rw [hK1]
    have hxd : g2ChartA F WSL * rootDiagUnit Tag.G2 b * (g2ChartA F WSL)⁻¹ =
        rootDiagUnit Tag.G2 b * rootDiagUnit Tag.G2 a := by
      rw [hK2]
      group
    have hxm : g2ChartA F WSL * (g2ChartA F WSL * g2ChartB F WSL) * (g2ChartA F WSL)⁻¹ =
        g2ChartA F WSL * g2ChartB F WSL := by
      have hc : Commute (g2ChartA F WSL) (g2ChartA F WSL * g2ChartB F WSL) :=
        Commute.mul_right (Commute.refl _) (hcomm WSL WSL)
      exact mul_inv_eq_iff_eq_mul.mpr hc.eq
    calc g2ChartA F WSL * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) *
          (g2ChartA F WSL)⁻¹
        = (g2ChartA F WSL * rootDiagUnit Tag.G2 b * (g2ChartA F WSL)⁻¹) *
          (g2ChartA F WSL * (g2ChartA F WSL * g2ChartB F WSL) * (g2ChartA F WSL)⁻¹) := by group
      _ = rootDiagUnit Tag.G2 b * rootDiagUnit Tag.G2 a *
          (g2ChartA F WSL * g2ChartB F WSL) := by rw [hxd, hxm]
      _ = _ := by rw [hmul]

end Conj

end CFSG.ClassicalInvolution.G2D4Models
