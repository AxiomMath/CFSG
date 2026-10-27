module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Par
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.L1Data
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Data
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayerAux

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
  CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec4.E27
open scoped commutatorElement

section Leaves


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem layer_linear_model_odd (P : D4ParOdd ℓ f X σ) (hq1 : ℓ ^ f % 3 = 1) {x : C0 σ}
    (hx : IsClassX σ x) : LayerLinearModel σ x := by
  classical
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g₀, hg₀⟩ := hx
  have hv3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hv1 : g₀ * x * g₀⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hq4 : 4 ≤ ℓ ^ f := by
    have := P.five_le
    omega
  haveI : Fact ℓ.Prime := ⟨P.prime⟩
  haveI : CharP X ℓ := P.charP
  haveI : CharP (AlgebraicClosure X) ℓ :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective ℓ
  have hσ3 : σ ^ 3 = 1 := P.sigma_pow_three
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) ℓ] at h'
    exact P.ne_three ((Nat.prime_dvd_prime_iff_eq P.prime Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three (AlgebraicClosure X) h3L
  obtain ⟨x₀, k, hk, hxk, hmodel⟩ := exists_threeA_layer_linear (ℓ := ℓ) (f := f) P.one_le
    P.ne_three hq1 hq4 P.card P.frob hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hg₀ hv3 hv1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj P.one_le P.card P.frob (isPointIrreducible_gA hζ)
    hk' hk hzk hxk
  apply layerLinearModel_of_conj σ (c * g₀) x
  have : c * g₀ * x * (c * g₀)⁻¹ = x₀ := by
    rw [← hc]
    group
  rw [this]
  exact hmodel

theorem layer_unitary_model_odd (P : D4ParOdd ℓ f X σ) (hq2 : ℓ ^ f % 3 = 2) {x : C0 σ}
    (hx : IsClassX σ x) : LayerUnitaryModelP σ ℓ f x := by
  classical
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g₀, hg₀⟩ := hx
  have hv3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hv1 : g₀ * x * g₀⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hq2' : 2 < ℓ ^ f := by
    have := P.five_le
    omega
  haveI : Fact ℓ.Prime := ⟨P.prime⟩
  haveI : CharP X ℓ := P.charP
  haveI : CharP (AlgebraicClosure X) ℓ :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective ℓ
  have hσ3 : σ ^ 3 = 1 := P.sigma_pow_three
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) ℓ] at h'
    exact P.ne_three ((Nat.prime_dvd_prime_iff_eq P.prime Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three (AlgebraicClosure X) h3L
  obtain ⟨x₀, k, hk, hxk, hmodel⟩ := exists_threeA_layer_unitaryP (ℓ := ℓ) (f := f) P.one_le
    P.ne_three hq2 hq2' P.card P.frob hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hg₀ hv3 hv1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj P.one_le P.card P.frob (isPointIrreducible_gA hζ)
    hk' hk hzk hxk
  apply layerUnitaryModelP_of_conj σ ℓ f (c * g₀) x
  have : c * g₀ * x * (c * g₀)⁻¹ = x₀ := by
    rw [← hc]
    group
  rw [this]
  exact hmodel

end Leaves

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
