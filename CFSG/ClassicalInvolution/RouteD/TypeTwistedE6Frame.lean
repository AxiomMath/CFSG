module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.Steinberg.Exceptional CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

structure SU6Frame (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) where
  R₁ : Subgroup (Su (GaloisField p (2 * f)) p f 6)
  S₂ : Subgroup (Su (GaloisField p (2 * f)) p f 6)
  S₃ : Subgroup (Su (GaloisField p (2 * f)) p f 6)
  R₁_mem : R₁ ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 6)
  commutes_R₁_S₃ : Commutes R₁ S₃
  gen : R₁ ⊔ S₂ ⊔ S₃ = ⊤
  ι₄ : unitaryGroup (frobQ p f) (frobQ_frobQ p f hf) →* Su (GaloisField p (2 * f)) p f 6
  ι₄_injective : Function.Injective ι₄
  ι₄_long : (unitaryModel (frobQ p f) (frobQ_frobQ p f hf)).lb.range.map ι₄ = R₁
  ι₄_short : (unitaryModel (frobQ p f) (frobQ_frobQ p f hf)).sb.range.map ι₄ = S₂
  ι₃ : SL(3, GaloisField p (2 * f)) →* Su (GaloisField p (2 * f)) p f 6
  ι₃_injective : Function.Injective ι₃
  ι₃_B23 : (WeakCT.B23 (GaloisField p (2 * f))).map ι₃ = S₂
  ι₃_B12 : (WeakCT.B12 (GaloisField p (2 * f))).map ι₃ = S₃
  R₁_center : ∀ r ∈ R₁, r ∈ Subgroup.center _ → r = 1
  S₂_center : ∀ s ∈ S₂, s ∈ Subgroup.center _ → s = 1

end CFSG.ClassicalInvolution.RouteD
