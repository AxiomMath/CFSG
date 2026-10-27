module

public import CFSG.HardMathSupport.Lang.AnisoF4.SpPairEven
public import CFSG.HardMathSupport.Lang.AnisoF4.Sp4Swap

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_symplecticBlockStandardPair_rankOne_even_swap [CharP F 2] (hF : 4 ≤ Nat.card F)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j : Fin D.rank}
    (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ W, SymplecticBlockStandardPair F W (rankOne D.rootGroup i) (rankOne D.rootGroup j) := by
  obtain ⟨W, hW⟩ := exists_symplecticBlockStandardPair_rankOne_even hF hE hdiv hcij hcji
  exact ⟨W, symplecticBlockStandardPair_swap hW⟩

end CFSG.HardMathSupport.Lang.AnisoF4
