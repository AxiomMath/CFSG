module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.B2LieEvenVanish
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def cartanE6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0;
     0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
     0, -1, -1, 2, -1, 0;
     0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, -1, 2]

@[expose] def reflMat (i : Fin 6) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  fun j k => (if j = k then 1 else 0) - (if k = i then ((cartanE6 j i : ℤ) : ZMod 3) else 0)

theorem reflMat_mul_self (i : Fin 6) : reflMat i * reflMat i = 1 := by
  fin_cases i <;> decide

@[expose] def reflGL (i : Fin 6) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3) :=
  ⟨reflMat i, reflMat i, reflMat_mul_self i, reflMat_mul_self i⟩

@[expose] def W3 : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)) :=
  Subgroup.closure (Set.range reflGL)

@[expose] def rootRefl (i : Fin 6) (α : Fin 6 → ℤ) : Fin 6 → ℤ :=
  fun j => if j = i then α i - ∑ k, α k * cartanE6 k i else α j

@[expose] def rootsE6 : Set (Fin 6 → ℤ) :=
  ⋂₀ {S | (∀ i, Pi.single i (1 : ℤ) ∈ S) ∧ ∀ α ∈ S, ∀ i, rootRefl i α ∈ S}

@[expose] def cartanForm (α β : Fin 6 → ℤ) : ℤ :=
  ∑ i, α i * ∑ j, cartanE6 i j * β j

@[expose] def IsRootConnected (C : Set (Fin 6 → ℤ)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C,
    Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ cartanForm a b ≠ 0) x y

@[expose] noncomputable def rootRankQ (C : Set (Fin 6 → ℤ)) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ ((fun α : Fin 6 → ℤ => fun i => ((α i : ℤ) : ℚ)) '' C))

@[expose] def RootGood (F : Set (Fin 6 → ZMod 3)) : Prop :=
  ∃ C ⊆ rootsE6, IsRootConnected C ∧ 3 ≤ rootRankQ C ∧
    ∀ α ∈ C, ∀ f ∈ F, ∑ i, ((α i : ℤ) : ZMod 3) * f i = 0

@[expose] def fixVec (R : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 3))) :
    Set (Fin 6 → ZMod 3) :=
  {v | ∀ g ∈ R, Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) v = v}

@[expose] def X2E6WeylCore : Prop :=
  (∀ R : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)), R ≤ W3 →
      IsElemAbelian 3 R → ∀ r : ℕ, Nat.card R = 3 ^ r →
        r ≤ 3 ∧ (2 ≤ r → Nat.card (fixVec R) ≤ 3 ^ (4 - r))) ∧
  (∀ R : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)), R ≤ W3 →
      IsElemAbelian 3 R → ∀ r : ℕ, Nat.card R = 3 ^ r → r = 1 →
      ∀ U : AddSubgroup (Fin 6 → ZMod 3), (U : Set (Fin 6 → ZMod 3)) ⊆ fixVec R →
        3 ^ (5 - r) ≤ Nat.card U →
        ∃ F : AddSubgroup (Fin 6 → ZMod 3), (F : Set (Fin 6 → ZMod 3)) ⊆ U ∧
          Nat.card F = 9 ∧ RootGood (F : Set (Fin 6 → ZMod 3)))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
