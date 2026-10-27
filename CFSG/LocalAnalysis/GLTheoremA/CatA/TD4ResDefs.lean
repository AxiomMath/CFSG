module

public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.Open.GLADefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescTD4

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo
open CFSG.PGLModel (projImage)

@[expose] def TriD4InvCentRankOne :
    Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) →
    ∀ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf t = 2 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsElemAbelian 3 E →
      (∀ e ∈ E, e * t = t * e) → Nat.card E ≤ 3

@[expose] def PGLThreeInvGood : Prop :=
  (∀ n : ℕ, 2 ≤ n → Even n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
    ∀ x s : projImage (Sec4.glPi true 3 (2 ^ n) F), x ^ 3 = 1 → x ≠ 1 → orderOf s = 2 →
      x * s = s * x →
      GLAPLayer 3 (Subgroup.centralizer ({x} : Set (projImage (Sec4.glPi true 3 (2 ^ n) F)))) ≠
        ⊥) ∧
  (∀ n : ℕ, 2 ≤ n → Odd n → ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
    ∀ x s : projImage (Sec4.glPi false 3 (2 ^ n) F), x ^ 3 = 1 → x ≠ 1 → orderOf s = 2 →
      x * s = s * x →
      GLAPLayer 3 (Subgroup.centralizer ({x} : Set (projImage (Sec4.glPi false 3 (2 ^ n) F)))) ≠
        ⊥)

end CFSG.LocalAnalysis.GLTheoremA.HDescTD4
