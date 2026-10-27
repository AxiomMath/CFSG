module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthMain
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl_adj (hF : Nat.card F = 2) (i j : Fin m) (hij : i.val + 1 = j.val) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(rankOne (rootDatum m F).rootGroup i ⊔ rankOne (rootDatum m F).rootGroup j) :=
  OrdinaryProofs.RankTwoCoverSL.sl_adj hF i j hij

theorem sl_orth (hF : Nat.card F = 2) (i j : Fin m) (hij : i.val + 2 ≤ j.val) :
    ∃ xi ∈ (rootDatum m F).rootGroup (Pi.single i 1),
    ∃ yi ∈ (rootDatum m F).rootGroup (-Pi.single i 1),
    ∃ xj ∈ (rootDatum m F).rootGroup (Pi.single j 1),
    ∃ yj ∈ (rootDatum m F).rootGroup (-Pi.single j 1),
      (xi * yi) ^ 3 = 1 ∧ xi * yi ≠ 1 ∧ (xj * yj) ^ 3 = 1 ∧ xj * yj ≠ 1 ∧
      xj * yj ∉ Subgroup.zpowers (xi * yi) ∧
      ∀ k, ∀ x ∈ (rootDatum m F).rootGroup (Pi.single k 1),
        ∀ y ∈ (rootDatum m F).rootGroup (-Pi.single k 1),
        (x * y) ^ 3 = 1 → x * y ≠ 1 → ∀ g : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
          ∀ e : ℕ, g * (x * y) ^ e * g⁻¹ ≠ xi * yi * (xj * yj) :=
  OrdinaryProofs.RankTwoCoverSLOrthMain.sl_orth hF i j hij

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
