module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniElementary

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

abbrev pGroupFrattiniCommGroup {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    CommGroup (Ambient ⧸ frattini Ambient) := by
  let : IsMulCommutative (Ambient ⧸ frattini Ambient) :=
    pGroup_frattini_quotient_commutative hprime hpgroup
  exact { (inferInstance : Group (Ambient ⧸ frattini Ambient)) with mul_comm := mul_comm' }

abbrev elementaryZModModule {Elementary : Type groupUniverse} [CommGroup Elementary]
    {prime : ℕ} (hexponent : ∀ element : Elementary, element ^ prime = 1) :
    Module (ZMod prime) (Additive Elementary) :=
  AddCommGroup.zmodModule (fun element => hexponent element.toMul)

@[expose] def elementaryAutLinear {Elementary : Type groupUniverse} [CommGroup Elementary]
    (prime : ℕ) [Module (ZMod prime) (Additive Elementary)] :
    MulAut Elementary →* (Additive Elementary ≃ₗ[ZMod prime] Additive Elementary) where
  toFun automorphism := LinearEquiv.ofLinearMap
    ((MulEquiv.toAdditive automorphism).toAddMonoidHom.toZModLinearMap prime)
    ((MulEquiv.toAdditive automorphism.symm).toAddMonoidHom.toZModLinearMap prime)
    (by ext element; exact automorphism.apply_symm_apply element)
    (by ext element; exact automorphism.symm_apply_apply element)
  map_one' := by
    ext element
    rfl
  map_mul' := by
    intro first second
    ext element
    rfl

theorem elementaryAutLinear_injective {Elementary : Type groupUniverse} [CommGroup Elementary]
    (prime : ℕ) [Module (ZMod prime) (Additive Elementary)] :
    Function.Injective (elementaryAutLinear (Elementary := Elementary) prime) := by
  intro first second heq
  apply MulEquiv.ext
  intro element
  exact congrArg (fun linearAutomorphism : Additive Elementary ≃ₗ[ZMod prime] Additive Elementary =>
    (linearAutomorphism (Additive.ofMul element)).toMul) heq

theorem pGroup_frattini_linear_action {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    let _ : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
    ∃ module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)),
      let _ := module
      ∃ linearAction : MulAut (Ambient ⧸ frattini Ambient) →*
          (Additive (Ambient ⧸ frattini Ambient) ≃ₗ[ZMod prime]
            Additive (Ambient ⧸ frattini Ambient)),
        Function.Injective linearAction := by
  dsimp only
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent hprime hpgroup)
  refine ⟨module, ?_⟩
  exact ⟨elementaryAutLinear prime, elementaryAutLinear_injective prime⟩

end CFSG.LargeEvenClassification.Helpers
