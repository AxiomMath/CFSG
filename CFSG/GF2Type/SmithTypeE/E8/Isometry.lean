module

public import CFSG.GF2Type.SmithTypeE.E8.FactsForm

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

section Schur


theorem ffForm_nondegenerate : F.ffForm.Nondegenerate :=
  ⟨fun x hx => F.ff_nondeg hx, fun y hy => F.ff_nondeg (fun x => by
    rw [F.ff_comm]
    exact hy x)⟩

theorem eq_ff_or_zero (B : LinearMap.BilinForm (ZMod 2) (Fin e7Data.d →₀ ZMod 2))
    (hB : ∀ (g : ↥(adjointGroup .E7 (ZMod 2))) (x y : Fin e7Data.d →₀ ZMod 2),
      B (e7Rep56 (ZMod 2) g x) (e7Rep56 (ZMod 2) g y) = B x y) :
    B = F.ffForm ∨ B = 0 := by
  let T : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2) :=
    (F.ffForm.toDual ffForm_nondegenerate).symm.toLinearMap ∘ₗ B
  have hT : ∀ x y, F.ffForm (T x) y = B x y := by
    intro x y
    have h1 : (F.ffForm.toDual ffForm_nondegenerate) (T x) = B x :=
      (F.ffForm.toDual ffForm_nondegenerate).apply_symm_apply (B x)
    have h2 := LinearMap.BilinForm.toDual_def ffForm_nondegenerate (m := T x) (n := y)
    rw [h1] at h2
    exact h2.symm
  have hcomm : ∀ (g : ↥(adjointGroup .E7 (ZMod 2))) (x : Fin e7Data.d →₀ ZMod 2),
      T (e7Rep56 (ZMod 2) g x) = e7Rep56 (ZMod 2) g (T x) := by
    intro g x
    rw [← sub_eq_zero]
    refine F.ff_nondeg (fun y => ?_)
    have e1 : F.ffForm (T (e7Rep56 (ZMod 2) g x)) y = B (e7Rep56 (ZMod 2) g x) y := hT _ _
    have e2 : F.ffForm (e7Rep56 (ZMod 2) g (T x)) y = B x (e7Rep56 (ZMod 2) g⁻¹ y) := by
      have h3 := F.ff_rep g (T x) (e7Rep56 (ZMod 2) g⁻¹ y)
      rw [F.rep_inv_apply] at h3
      exact h3.trans (hT x _)
    have e3 : B (e7Rep56 (ZMod 2) g x) y = B x (e7Rep56 (ZMod 2) g⁻¹ y) := by
      have h4 := hB g⁻¹ (e7Rep56 (ZMod 2) g x) y
      rw [F.rep_inv_apply'] at h4
      exact h4.symm
    show F.ffForm (T (e7Rep56 (ZMod 2) g x) - e7Rep56 (ZMod 2) g (T x)) y = 0
    rw [map_sub, LinearMap.sub_apply, e1, e2, e3, sub_self]
  have hfix : ∀ u : ↥(adjointGroup .E7 (ZMod 2)),
      (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) →
        e7Rep56 (ZMod 2) u (T e7Y56) = T e7Y56 := by
    intro u hu
    rw [← hcomm, e7Rep56_posUnipotent_e7Y56 u hu]
  have hbasis : ∀ a : Fin e7Data.d, ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
      e7Rep56 (ZMod 2) g e7Y56 = Finsupp.single a 1 := fun a =>
    F.mem_weightVec_iff.1 (F.single_mem_weightVec a)
  rcases eq_zero_or_eq_e7Y56 (T e7Y56) hfix with h0 | h1
  · right
    have hT0 : T = 0 := by
      refine Finsupp.lhom_ext fun a b => ?_
      obtain ⟨g, hg⟩ := hbasis a
      have h5 : T (Finsupp.single a 1) = 0 := by
        rw [← hg, hcomm, h0, map_zero]
      rw [← Finsupp.smul_single_one, map_smul, h5, smul_zero, LinearMap.zero_apply]
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [← hT x y, hT0]
    simp
  · left
    have hT1 : T = LinearMap.id := by
      refine Finsupp.lhom_ext fun a b => ?_
      obtain ⟨g, hg⟩ := hbasis a
      have h5 : T (Finsupp.single a 1) = Finsupp.single a 1 := by
        rw [← hg, hcomm, h1]
      rw [← Finsupp.smul_single_one, map_smul, h5]
      rfl
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [← hT x y, hT1]
    rfl

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem isometry8 [IsSimpleGroup G] {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))} (hE : SmithE8Equiv S φ ψ) (u v : S.Qt) :
    F.ff (φ u) (φ v) = polar S.q u v := by
  let B' : LinearMap.BilinForm (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
    S.q.polarBilin.compl₁₂ (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)
      (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)
  have hB : ∀ (g : ↥(adjointGroup .E7 (ZMod 2))) (x y : Fin e7Data.d →₀ ZMod 2),
      B' (e7Rep56 (ZMod 2) g x) (e7Rep56 (ZMod 2) g y) = B' x y := by
    intro g x y
    have hg : ∀ w : Fin e7Data.d →₀ ZMod 2,
        φ.symm (e7Rep56 (ZMod 2) g w) = (((ψ.symm g : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (φ.symm w) := by
      intro w
      have h1 := hE (ψ.symm g) (φ.symm w)
      rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      rw [← h1, LinearEquiv.symm_apply_apply]
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, polarBilin_apply_apply, hg]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (ψ.symm g : S.Mbar).1.2 _ _
  have hBu : ∀ u v : S.Qt, B' (φ u) (φ v) = polar S.q u v := by
    intro u v
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      polarBilin_apply_apply]
  rcases eq_ff_or_zero B' hB with h | h
  · have h1 : B' (φ u) (φ v) = F.ff (φ u) (φ v) := by rw [h]; rfl
    rw [← hBu u v]
    exact h1.symm
  · exfalso
    have hz : ∀ x y : S.Qt, polar S.q x y = 0 := by
      intro x y
      rw [← hBu, h]
      rfl
    have hx0 : φ.symm e7Y56 = 0 := S.q_nondegenerate.1 _ fun y => by
      rw [polarBilin_apply_apply, hz]
    exact F.wt_ne_zero_core F.e7Y56_mem_weightVec (by simpa using congrArg φ hx0)

end Schur

end CFSG.GF2Type.SmithTypeE.E8
