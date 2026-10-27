module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenOdd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

structure TwoParLat (S : Type) [Group S] (T P₁ P₂ : Subgroup S) : Prop where
  sylow : IsSylowTwoOf T ⊤
  normT : Subgroup.normalizer (T : Set S) = T
  lt₁ : T < P₁
  lt₂ : T < P₂
  atom₁ : ∀ Q : Subgroup S, T ≤ Q → Q ≤ P₁ → Q = T ∨ Q = P₁
  atom₂ : ∀ Q : Subgroup S, T ≤ Q → Q ≤ P₂ → Q = T ∨ Q = P₂
  ne : P₁ ≠ P₂
  top₁ : P₁ ≠ ⊤
  top₂ : P₂ ≠ ⊤
  hover : ∀ Y : Subgroup S, T ≤ Y → Y = T ∨ Y = P₁ ∨ Y = P₂ ∨ Y = ⊤
  gen₁ : P₁ ≤ pElementSubgroup 2 P₁
  gen₂ : P₂ ≤ pElementSubgroup 2 P₂
  ct₁ : CharTwo P₁
  ct₂ : CharTwo P₂

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
