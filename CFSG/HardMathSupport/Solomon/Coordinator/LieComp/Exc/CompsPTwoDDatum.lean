module

public import CFSG.RankThree.Lattice.SteinbergBIGenFixedRootData
public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Basic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusData
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
public import CFSG.LieType.Chevalley.CorootCoordinates
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeCentralCover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.AlgebraicGroups CFSG.Open CFSG.RankThree.Chevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDDatum

section Orbits

variable {τ : Tag}

theorem thetaOrbit_of_fixed {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)}
    {α : Fin τ.rank → ℤ} (h : θ (toReal α) = toReal α) : thetaOrbit θ α = {α} := by
  have hpow : ∀ k : ℕ, (θ ^ k) (toReal α) = toReal α := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, h]
  ext β
  constructor
  · rintro ⟨k, hk⟩
    rw [hpow] at hk
    exact toReal_injective hk.symm
  · rintro rfl
    exact self_mem_thetaOrbit _ _

theorem thetaOrbit_of_swap {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)}
    {α α' : Fin τ.rank → ℤ} (h1 : θ (toReal α) = toReal α') (h2 : θ (toReal α') = toReal α) :
    thetaOrbit θ α = {α, α'} := by
  have hpow : ∀ k : ℕ, (θ ^ k) (toReal α) = toReal α ∨ (θ ^ k) (toReal α) = toReal α' := by
    intro k
    induction k with
    | zero => exact Or.inl (by simp)
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      rcases ih with h | h
      · exact Or.inr (by rw [h, h1])
      · exact Or.inl (by rw [h, h2])
  ext β
  constructor
  · rintro ⟨k, hk⟩
    rcases hpow k with h | h
    · exact Or.inl (toReal_injective (hk.symm.trans h))
    · exact Or.inr (toReal_injective (hk.symm.trans h))
  · rintro (rfl | rfl)
    · exact self_mem_thetaOrbit _ _
    · exact ⟨1, by rw [pow_one, h1]⟩

end Orbits

section OrbitMap

variable
  {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M] (D : GenFixedRootDatum τ p₀ k M)

theorem map_iterateFrobenius_zero (X : SL2 k) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ 0) X = X :=
  Subtype.ext (by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, iterateFrobenius_def])

theorem orbitMap_single {O : Set (Fin τ.rank → ℤ)} (hO : GenFixedRootDatum.orbitCard O = 1)
    (A : SL2 (D.orbitField O)) :
    D.orbitMap O A = rootSL2 τ k (GenFixedRootDatum.orbitRoot O)
      (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) := by
  simp only [GenFixedRootDatum.orbitMap, hO, List.range_one, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  have h0 : thetaPowVec D.θ 0 (GenFixedRootDatum.orbitRoot O) = GenFixedRootDatum.orbitRoot O := thetaPowVec_eq (by simp)
  rw [h0, mul_zero, map_iterateFrobenius_zero]

theorem orbitMap_pair {O : Set (Fin τ.rank → ℤ)} (hO : GenFixedRootDatum.orbitCard O = 2)
    {β β' : Fin τ.rank → ℤ} (hβ : GenFixedRootDatum.orbitRoot O = β) (hβ' : D.θ (toReal β) = toReal β')
    (A : SL2 (D.orbitField O)) :
    D.orbitMap O A = rootSL2 τ k β (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) *
      rootSL2 τ k β' (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ D.e)
        (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A)) := by
  have hr : List.range 2 = [0, 1] := rfl
  simp only [GenFixedRootDatum.orbitMap, hO, hr, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  have h0 : thetaPowVec D.θ 0 (GenFixedRootDatum.orbitRoot O) = β := by
    rw [hβ]
    exact thetaPowVec_eq (by simp)
  have h1 : thetaPowVec D.θ 1 (GenFixedRootDatum.orbitRoot O) = β' := by
    rw [hβ]
    exact thetaPowVec_eq (by simpa using hβ'.symm)
  rw [h0, h1, mul_zero, map_iterateFrobenius_zero]

end OrbitMap

section Gens

variable {K : Type*} [Field K] {G : Type*} [Group G]

theorem map_uSL' {K' : Type*} [Field K'] (f : K →+* K') (c : K) :
    Matrix.SpecialLinearGroup.map f (uSL c) = uSL (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem map_vSL' {K' : Type*} [Field K'] (f : K →+* K') (c : K) :
    Matrix.SpecialLinearGroup.map f (vSL c) = vSL (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL]

theorem sl2_hom_mem_of_gens (φ : SL(2, K) →* G) (H : Subgroup G)
    (hu : ∀ t, φ (uSL t) ∈ H) (hv : ∀ t, φ (vSL t) ∈ H) (A : SL(2, K)) : φ A ∈ H := by
  have hA : A ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hu c
    · exact hv c
  | one => rw [map_one]; exact H.one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact H.mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact H.inv_mem hx

end Gens

section Cartan

open CFSG.Timmesfeld CFSG.Timmesfeld.LevisSpin

theorem cartanD_fork_values {m : ℕ} (hm : 4 ≤ m) :
    CFSG.LieType.Universal.Spin.cartanD m ⟨m - 2, by omega⟩ ⟨m - 3, by omega⟩ = -1 ∧
    CFSG.LieType.Universal.Spin.cartanD m ⟨m - 3, by omega⟩ ⟨m - 2, by omega⟩ = -1 ∧
    CFSG.LieType.Universal.Spin.cartanD m ⟨m - 1, by omega⟩ ⟨m - 3, by omega⟩ = -1 ∧
    CFSG.LieType.Universal.Spin.cartanD m ⟨m - 3, by omega⟩ ⟨m - 1, by omega⟩ = -1 ∧
    CFSG.LieType.Universal.Spin.cartanD m ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ = 0 ∧
    CFSG.LieType.Universal.Spin.cartanD m ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [cartanD_apply]
      simp only [Fin.mk.injEq]
      split_ifs <;> omega

theorem cartanD_swap {m : ℕ} (hm : 4 ≤ m) (j k : Fin m) :
    CFSG.LieType.Universal.Spin.cartanD m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ j)
      (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
  simp only [cartanD_apply, Equiv.swap_apply_def, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> (try simp only [Fin.val_mk] at *) <;> first | omega | simp_all

end Cartan

end CompsPTwoDDatum

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
