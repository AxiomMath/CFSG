module

public import CFSG.ClassicalInvolution.ModelFacts.D4RigidWeights
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Center
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (spinAction quadPlus)
open CFSG.ClassicalInvolution.ModelFacts.D4Rigid (fr ne23 idx)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

@[expose] noncomputable def fkN2 : Module.End 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) where
  toFun v μ := (if μ = Sum.inl 2 then v (Sum.inl 3) else 0) -
    (if μ = Sum.inr 3 then v (Sum.inr 2) else 0)
  map_add' v w := by
    funext μ
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[expose] noncomputable def fkN3 : Module.End 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) where
  toFun v μ := (if μ = Sum.inl 2 then v (Sum.inr 3) else 0) -
    (if μ = Sum.inl 3 then v (Sum.inr 2) else 0)
  map_add' v w := by
    funext μ
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem fkN2_apply (v : Fin 4 ⊕ Fin 4 → 𝔽₃) (μ : Fin 4 ⊕ Fin 4) :
    fkN2 v μ = (if μ = Sum.inl 2 then v (Sum.inl 3) else 0) -
      (if μ = Sum.inr 3 then v (Sum.inr 2) else 0) := by
  rfl

theorem fkN3_apply (v : Fin 4 ⊕ Fin 4 → 𝔽₃) (μ : Fin 4 ⊕ Fin 4) :
    fkN3 v μ = (if μ = Sum.inl 2 then v (Sum.inr 3) else 0) -
      (if μ = Sum.inl 3 then v (Sum.inr 2) else 0) := by
  rfl

theorem fk_spinAction_x2 (c : 𝔽₃) (v : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    spinAction Q₄ ((fr 𝔽₃).longRoot ne23 true false (.ofAdd c)) v = v + c • fkN2 v := by
  funext μ
  rw [CFSG.ClassicalInvolution.ModelFacts.D4Rigid.spinAction_longRoot_apply ne23 true false c v μ]
  rcases μ with i | i <;> fin_cases i <;> simp [fkN2_apply, idx] <;> ring

theorem fk_spinAction_x3 (c : 𝔽₃) (v : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    spinAction Q₄ ((fr 𝔽₃).longRoot ne23 true true (.ofAdd c)) v = v + c • fkN3 v := by
  funext μ
  rw [CFSG.ClassicalInvolution.ModelFacts.D4Rigid.spinAction_longRoot_apply ne23 true true c v μ]
  rcases μ with i | i <;> fin_cases i <;> simp [fkN3_apply, idx] <;> ring

theorem fkN2_mul_fkN3 (v : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    fkN2 (fkN3 v) = -(v (Sum.inr 2)) • (Pi.single (Sum.inl 2) 1 : Fin 4 ⊕ Fin 4 → 𝔽₃) := by
  funext μ
  rw [fkN2_apply, fkN3_apply, fkN3_apply]
  rcases μ with i | i <;> fin_cases i <;>
    simp [Pi.smul_apply, Pi.single_apply, smul_eq_mul] <;> ring

theorem fk_longSL2_injective {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    Function.Injective ((fr 𝔽₃).longSL2 hij s t) := by
  intro A B h
  apply ((fr 𝔽₃).toFrame hij s t).La_injective
  have hA := DFunLike.congr_fun
    (CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2 (fr 𝔽₃) hij s t) A
  have hB := DFunLike.congr_fun
    (CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2 (fr 𝔽₃) hij s t) B
  simp only [MonoidHom.comp_apply] at hA hB
  rw [← hA, ← hB, h]

theorem fk_nodes_comm {a b : spinGroup Q₄}
    (ha : a ∈ ((fr 𝔽₃).longSL2 ne23 true false).range)
    (hb : b ∈ ((fr 𝔽₃).longSL2 ne23 true true).range) :
    spinAction Q₄ a * spinAction Q₄ b = spinAction Q₄ b * spinAction Q₄ a := by
  rcases ha with ⟨A, rfl⟩
  rcases hb with ⟨B, rfl⟩
  have hA := DFunLike.congr_fun
    (CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2 (fr 𝔽₃) ne23 true false) A
  have hB := DFunLike.congr_fun
    (CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2 (fr 𝔽₃) ne23 true true) B
  simp only [MonoidHom.comp_apply] at hA hB
  rw [hA, hB]
  have hswap : (fr 𝔽₃).toFrame ne23 true true =
      ((fr 𝔽₃).toFrame ne23 true false).swap := by
    rfl
  rw [hswap]
  exact ((fr 𝔽₃).toFrame ne23 true false).La_comm_La_swap A B

end CFSG.OddStandard.SmallF3.Omega
