module

public import CFSG.LieType.Steinberg.Minuscule.E6TorusLang
import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Torus
import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Aux

public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.Classical2 CFSG.RankThree.E6 CFSG.RankThree.PartOne.KLCE
  CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.RankThree.PartOne.TCX.E
  CFSG.LieType.SemisimpleCentralizers.HeldLang
open scoped MatrixGroups


variable {k Ω : Type} [Field k] [Finite k] [CharP k 2]
  [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
  [Algebra (ZMod 2) k] [Algebra.IsAlgebraic (ZMod 2) k]

theorem e6IsogenyAlgebraic_minBC_algebraic_square
    (ι : k →+* Ω)
    (Ψ : SL(3, k) →* e6Data_valid.minGroup k)
    (ρ : SL(3, k) →* adjointGroup .E6 k)
    (hρ : ρ = (e6IsogenyT k).comp Ψ) :
    e6IsogenyAlgebraic.comp ((minBC e6Data_valid ι).comp Ψ) =
      (baseChangeGL ι).comp ((adjointGroup .E6 k).subtype.comp ρ) := by
  classical
  apply MonoidHom.ext
  intro A
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hρ]
  rw [e6IsogenyAlgebraic_minBC_algebraic]
  congr 1
  have hmin : minBC e6Data_valid (RingHom.id k) (Ψ A) = Ψ A := by
    rw [minBC_id]
    rfl
  have hid := e6IsogenyAlgebraic_minBC (k := k) (Ω := k)
    (ι := RingHom.id k) (x := Ψ A)
  rw [hmin] at hid
  change e6IsogenyAlgebraic (Ψ A) = ((e6Isogeny k (Ψ A) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k)
  simpa [e6ScToBar, baseChangeGL_id, e6IsogenyT] using hid

end CFSG.ClassicalInvolution.WeakCT

end
