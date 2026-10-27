module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKNode
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKMultN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKMultCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKTri
public import CFSG.ClassicalInvolution.Q3.Q3MFODSim

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (spinAction quadPlus map_spinAction upperSL2)
open CFSG.ClassicalInvolution.ModelFacts.D4Rigid (fr ne23)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Spin₈" => spinGroup (quadPlus 4 (GaloisField 3 1))

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

private theorem fk_node_data {f : SL(2, 𝔽₃) →* Spin₈} (hf : Function.Injective f)
    (N : Module.End 𝔽₃ V₈)
    (hx : ∀ (c : 𝔽₃) (v : V₈), spinAction Q₄ (f (upperSL2 c)) v = v + c • N v)
    (φ : MulAut Spin₈) (A : V₈ ≃ₗ[𝔽₃] V₈)
    (hφ : ∀ x, spinAction Q₄ (φ x) = A * spinAction Q₄ x * A⁻¹)
    (hn : f.range.map φ.toMonoidHom = f.range) :
    ∃ (h : Spin₈) (ε : 𝔽₃), h ∈ f.range ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ v, A (N (A.symm v)) = ε • spinAction Q₄ h (N ((spinAction Q₄ h).symm v))) ∧
      (ε = -1 ↔ FKSwap φ f.range) := by
  obtain ⟨h, e, hh, he, hφu, hsw⟩ := fk_swap_cases f hf φ fun x hx => by
    rw [← hn]
    exact Subgroup.mem_map_of_mem _ hx
  refine ⟨h, e, hh, he, fun v => ?_, hsw⟩
  have key : A * spinAction Q₄ (f (upperSL2 1)) * A⁻¹ =
      spinAction Q₄ h * spinAction Q₄ (f (upperSL2 e)) * (spinAction Q₄ h)⁻¹ := by
    rw [← hφ, hφu, map_mul, map_mul, map_inv]
  have hv := LinearEquiv.congr_fun key v
  have e1 : (A * spinAction Q₄ (f (upperSL2 1)) * A⁻¹) v =
      v + A (N (A.symm v)) := by
    show A (spinAction Q₄ (f (upperSL2 1)) (A.symm v)) = _
    rw [hx, map_add, one_smul, LinearEquiv.apply_symm_apply]
  have e2 : (spinAction Q₄ h * spinAction Q₄ (f (upperSL2 e)) * (spinAction Q₄ h)⁻¹) v =
      v + e • spinAction Q₄ h (N ((spinAction Q₄ h).symm v)) := by
    show spinAction Q₄ h (spinAction Q₄ (f (upperSL2 e)) ((spinAction Q₄ h).symm v)) = _
    rw [hx, map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [e1, e2] at hv
  exact add_left_cancel hv

private theorem fk_one_ne_neg_one : (1 : 𝔽₃) ≠ -1 :=
  (CFSG.ClassicalInvolution.Q3.Q3MFOD.neg_one_ne_one_of_card_three
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three).symm

theorem fk_mult_swap (φ : MulAut Spin₈) (A : V₈ ≃ₗ[𝔽₃] V₈) (μ : 𝔽₃) (hμ : μ ≠ 0)
    (hA : ∀ v, Q₄ (A v) = μ * Q₄ v)
    (hφ : ∀ x, spinAction Q₄ (φ x) = A * spinAction Q₄ x * A⁻¹)
    (h2 : (fkNode 2).map φ.toMonoidHom = fkNode 2) (h3 : (fkNode 3).map φ.toMonoidHom = fkNode 3) :
    μ = 1 ↔ (FKSwap φ (fkNode 2) ↔ FKSwap φ (fkNode 3)) := by
  rw [fkNode_two] at h2 ⊢
  rw [fkNode_three] at h3 ⊢
  have hx2 : ∀ (c : 𝔽₃) (v : V₈),
      spinAction Q₄ ((fr 𝔽₃).longSL2 ne23 true false (upperSL2 c)) v = v + c • fkN2 v := by
    intro c v
    rw [CFSG.LieType.Universal.Spin.HypFrame.longSL2_upperSL2]
    exact fk_spinAction_x2 c v
  have hx3 : ∀ (c : 𝔽₃) (v : V₈),
      spinAction Q₄ ((fr 𝔽₃).longSL2 ne23 true true (upperSL2 c)) v = v + c • fkN3 v := by
    intro c v
    rw [CFSG.LieType.Universal.Spin.HypFrame.longSL2_upperSL2]
    exact fk_spinAction_x3 c v
  obtain ⟨h₂, ε₂, hh₂, hε₂, hAN₂, hsw₂⟩ :=
    fk_node_data (fk_longSL2_injective ne23 true false) fkN2 hx2 φ A hφ h2
  obtain ⟨h₃, ε₃, hh₃, hε₃, hAN₃, hsw₃⟩ :=
    fk_node_data (fk_longSL2_injective ne23 true true) fkN3 hx3 φ A hφ h3
  have hb : (fr 𝔽₃).longSL2 ne23 true true (upperSL2 1) ∈
      ((fr 𝔽₃).longSL2 ne23 true true).range := ⟨_, rfl⟩
  have ha : (fr 𝔽₃).longSL2 ne23 true false (upperSL2 1) ∈
      ((fr 𝔽₃).longSL2 ne23 true false).range := ⟨_, rfl⟩
  have c₂₃ : ∀ v, spinAction Q₄ h₂ (fkN3 v) = fkN3 (spinAction Q₄ h₂ v) := by
    intro v
    have h := LinearEquiv.congr_fun (fk_nodes_comm hh₂ hb) v
    simp only [LinearEquiv.mul_apply, hx3, map_add, map_smul, one_smul] at h
    exact add_left_cancel h
  have c₃₂ : ∀ v, spinAction Q₄ h₃ (fkN2 v) = fkN2 (spinAction Q₄ h₃ v) := by
    intro v
    have h := LinearEquiv.congr_fun (fk_nodes_comm ha hh₃) v
    simp only [LinearEquiv.mul_apply, hx2, map_add, map_smul, one_smul] at h
    exact (add_left_cancel h).symm
  have hμ' := fk_mult_core A (spinAction Q₄ h₂) (spinAction Q₄ h₃) fkN2 fkN3 μ ε₂ ε₃ hμ hA
    (map_spinAction Q₄ h₂) (map_spinAction Q₄ h₃) hε₂ hε₃ fkN2_mul_fkN3 hAN₂ hAN₃ c₂₃ c₃₂
    (fun v => LinearEquiv.congr_fun (fk_nodes_comm hh₂ hh₃) v)
  rw [hμ', ← hsw₂, ← hsw₃]
  rcases hε₂ with rfl | rfl <;> rcases hε₃ with rfl | rfl <;>
    simp [fk_one_ne_neg_one, fk_one_ne_neg_one.symm]

end CFSG.OddStandard.SmallF3.Omega
