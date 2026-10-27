module

public import CFSG.ClassicalInvolution.Phan.PhanP15Dict
public import CFSG.ClassicalInvolution.Phan.PhanP18Swap
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanG
open scoped MatrixGroups

section Rho

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem FJ'_D_mul {Z : Matrix (Fin 2) (Fin 2) F} (hZ : FJ ε Z) :
    FJ' ε (!![1, 0; 0, -1] * Z) := by
  obtain ⟨h1, h2⟩ := hZ
  refine ⟨?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

theorem exists_rho_perp [Finite F] (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) :
    ∃ ρ ∈ (S.ι 0).range, ∀ a ∈ planeA ε hε h4, spinAction (quadPlus 4 F) ρ a ∈ planeB ε hε h4 := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨v, hvA, hvQ⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_mem_eq_unit hodd
    (restrict_planeA_nondegenerate h2 hε h4) (by rw [finrank_planeA h2 hε h4]) (-1)
  obtain ⟨hvv, hFJ⟩ := (mem_planeA_iff h2).1 hvA
  set κ := (frame0 (F := F)).coords v with hκ
  have hdet : κ.det = -1 := by
    have h1 : quadPlus 4 F ((frame0 (F := F)).incl κ) = κ.det := Frame.Q_incl _ _
    rw [← hvv] at h1
    rw [← h1]
    simpa using hvQ
  have hMdet : (!![1, 0; 0, -1] * κ : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_mul, hdet]
    simp [Matrix.det_fin_two_of]
  let Msl : SL(2, F) := ⟨!![1, 0; 0, -1] * κ, hMdet⟩
  have hr : (frame0 (F := F)).La Msl ∈ (S.ι 0).range.map (spinAction (quadPlus 4 F)) := by
    rw [hS.map_range 0]
    exact ⟨Msl, rfl⟩
  obtain ⟨ρ, hρ, hρM⟩ := hr
  refine ⟨ρ, hρ, fun a ha => ?_⟩
  obtain ⟨haa, haFJ⟩ := (mem_planeA_iff h2).1 ha
  rw [hρM, haa, Frame.La_apply_incl]
  refine incl_mem_planeB_of_FJ' ε hε h4 ?_
  change FJ' ε (!![1, 0; 0, -1] * κ * (frame0 (F := F)).coords a)
  rw [Matrix.mul_assoc]
  exact FJ'_D_mul (hFJ.mul haFJ)

end Rho

section Perp

variable {p e : ℕ} [Fact p.Prime]

theorem mem_mul_of_perp (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {h : spinGroup (quadPlus 4 (GaloisField p e))}
    (hperp : ∀ a ∈ planeA M.ε M.hε M.h4, ∀ a' ∈ planeA M.ε M.hε M.h4,
      polar (quadPlus 4 (GaloisField p e)) (spinAction (quadPlus 4 (GaloisField p e)) h a) a' = 0) :
    ∃ y ∈ parab M.S {1, 2, 3}, ∃ ρ ∈ parab M.S {0}, ∃ z ∈ parab M.S {1, 2, 3},
      h = y * ρ * z := by
  have h2 := two_ne_zero_gf hp2 e
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  obtain ⟨ρ, hρ, hρB⟩ := exists_rho_perp M.spec h2 hodd
  have hρperp : ∀ a ∈ planeA M.ε M.hε M.h4, ∀ a' ∈ planeA M.ε M.hε M.h4,
      polar (quadPlus 4 (GaloisField p e)) (spinAction (quadPlus 4 (GaloisField p e)) ρ a) a' = 0 :=
    fun a ha a' ha' => polar_planeB_planeA h2 ha' (hρB a ha)
  obtain ⟨y, hy1, hy2⟩ := exists_spin_fix_map hodd (nondegenerate_polarBilin_quadPlus 4 _)
    (restrict_planeA_nondegenerate h2 M.hε M.h4)
    (by
      rw [finrank_planeA h2 M.hε M.h4, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
        Fintype.card_fin]
      norm_num)
    ρ h hρperp hperp
  have hyfix : y ∈ fixA M.ε M.hε M.h4 := hy1
  have hz : h⁻¹ * (y * ρ) ∈ fixA M.ε M.hε M.h4 := fun a ha => by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hy2 a ha,
      ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  refine ⟨y, fixA_le_parab M hp2 hq hyfix, ρ, ?_, (h⁻¹ * (y * ρ))⁻¹,
    inv_mem (fixA_le_parab M hp2 hq hz), by group⟩
  exact Lsup_le_parab (S := M.S) {0} (by rw [Lsup_singleton]; exact hρ)

end Perp

end CFSG.ClassicalInvolution.PhanP
