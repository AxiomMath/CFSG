module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexBorelParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitaryPoint
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzukiCenter

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization

universe u

local instance finite_projective_general_linear
    {K : Type u} [Field K] [Finite K] (n : ℕ) :
    Finite (Matrix.ProjGenLinGroup (Fin n) K) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

local instance finite_projective_special_unitary
    {K : Type u} [Field K] [Finite K] {n : ℕ} (J : HermitianForm n K) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_injective
    (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin n) K)) Subtype.coe_injective

theorem linear_borel_index_and_whole_involution_parameter
    (f : ℕ) (hf : 2 ≤ f)
    (B : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField f)))
    (hB : IsBorelSubgroup B) :
    B.index = (2 ^ f) ^ 1 + 1 ∧
      Nat.card {x : Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField f) //
        x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 := by
  let K := BinaryGaloisField f
  let Omega := ℙ K (Fin 2 → K)
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  let : Finite G := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨rho, b, S, _hnatural, hN, _hregular, htwo⟩ :=
    pgl_sylow_normalizer_action f hf
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hN' : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G b := by
    rw [hN]
    ext g
    rfl
  let : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a c d e hac hde
    exact htwo a c d e hac hde
  let : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hdegree : Nat.card Omega = (2 ^ f) ^ 1 + 1 := by
    rw [pow_one, Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)]
    rw [show Nat.card K = 2 ^ f from GaloisField.card 2 f (by omega)]
  have hdata := bender_pgl2_borel_full f hf S
  have hZcard : Nat.card (Subgroup.center (S : Subgroup G)) = 2 ^ f := hdata.2.2.2.1
  have hScard : Nat.card (S : Subgroup G) = 2 ^ f := by
    simpa only [pow_one] using hdata.2.2.2.2
  have hZtop : Subgroup.center (S : Subgroup G) = ⊤ :=
    (Subgroup.center (S : Subgroup G)).eq_top_of_card_eq (hZcard.trans hScard.symm)
  have hcentral : ∀ x : (S : Subgroup G), IsInvolution x →
      x ∈ Subgroup.center (S : Subgroup G) := by
    intro x _
    rw [hZtop]
    exact Subgroup.mem_top x
  have hcount : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      2 ^ f - 1 := by
    rw [CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.point_involution_card_of_sylow_center
      S b hN' hcentral hdata.2.2.1, hZcard]
  exact (borel_index_and_whole_involution_card_of_native_action
    S b (2 ^ f) 1 hN' hdegree hcount B hB).2

theorem suzuki_borel_index_and_whole_involution_parameter
    (m : ℕ) (hm : 1 ≤ m) (B : Subgroup (SuzukiMatrixGroup m))
    (hB : IsBorelSubgroup B) :
    B.index = (2 ^ (2 * m + 1)) ^ 2 + 1 ∧
      Nat.card {x : SuzukiMatrixGroup m // x ∈ B ∧ IsInvolution x} =
        2 ^ (2 * m + 1) - 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  obtain ⟨rho, b, S, _hnatural, hN, _hregular, htwo⟩ :=
    suzuki_sylow_normalizer_action m (by omega)
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hN' : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G b := by
    rw [hN]
    ext g
    rfl
  let : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a c d e hac hde
    exact htwo a c d e hac hde
  let : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hdegree : Nat.card Omega = (2 ^ (2 * m + 1)) ^ 2 + 1 :=
    (External.suzukiMatrixGroup_ovoid_action_data m pi
      (fun x => iterateFrobeniusEquiv_def K 2 (m + 1) x)).2.2.2
  have hdata := bender_suzukiMatrixGroup_borel m (by omega) S
  have hZcard : Nat.card (Subgroup.center (S : Subgroup G)) = 2 ^ (2 * m + 1) :=
    hdata.2.2.2.1
  have hcount : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      2 ^ (2 * m + 1) - 1 := by
    rw [CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.point_involution_card_of_sylow_center
      S b hN' (CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.suzuki_sylow_involutions_mem_center
        m hm S) hdata.2.2.1, hZcard]
  exact (borel_index_and_whole_involution_card_of_native_action
    S b (2 ^ (2 * m + 1)) 2 hN' hdegree hcount B hB).2

theorem unitary_borel_index_and_whole_involution_parameter
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hB : IsBorelSubgroup B) :
    B.index = (2 ^ f) ^ 3 + 1 ∧
      Nat.card {x : ProjectiveSpecialUnitaryMatrixGroup J // x ∈ B ∧ IsInvolution x} =
        2 ^ f - 1 := by
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  obtain ⟨hdegree, rho, b, B0, S, _hinj, _hnatural, hB0, hN,
    _hrank, _hSE, htwo, hcount, _hScard, _hZcard, _hsquare, _hcentral, _hreg⟩ :=
    unitary_natural_action_whole_point_parameter J f hf hKcard hfixed hJ
  let : MulAction G Omega := MulAction.compHom Omega rho
  let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  let : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hN' : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G b := hN.trans hB0
  have hcount' : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      2 ^ f - 1 := hB0 ▸ hcount
  exact (borel_index_and_whole_involution_card_of_native_action
    S b (2 ^ f) 3 hN' hdegree hcount' B hB).2

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
