module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix

namespace GenLocU4Basic

variable {K : Type} [Field K] [Finite K]

@[expose] def IsUnitaryU (q : ℕ) (x : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (x.map (· ^ q))ᵀ * x = 1

@[expose] def IsInnerDiagU4 {q : ℕ} (φ : MulAut ↥(StatedSU 4 q K)) : Prop :=
  ∃ x : GL (Fin 4) K, IsUnitaryU q (x : Matrix (Fin 4) (Fin 4) K) ∧ ∀ g : ↥(StatedSU 4 q K),
    (((φ g : ↥(StatedSU 4 q K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (x : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

@[expose] def IsGraphU4 {q : ℕ} (A : GL (Fin 4) K) (φ : MulAut ↥(StatedSU 4 q K)) : Prop :=
  IsUnitaryU q (A : Matrix (Fin 4) (Fin 4) K) ∧ ∀ g : ↥(StatedSU 4 q K),
    (((φ g : ↥(StatedSU 4 q K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ q) *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

end GenLocU4Basic

end CFSG.GH74.Generic.BProg.B2
