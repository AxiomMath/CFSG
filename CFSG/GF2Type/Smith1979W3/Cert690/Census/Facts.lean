module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Defs
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB1

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

structure GrpFacts (minus : Bool) (D : GrpData) : Prop where
  enumO : EnumCert (oGensC minus) D.O.toList
  enumOm : EnumCert (omegaGensC minus) D.Om.toList
  codeO : codeSubgroup (oGensC minus) = O₀ minus
  codeOm : codeSubgroup (omegaGensC minus) = Ω₀ minus
  zero : D.O[0]! = Code.one
  idx : ∀ i < D.O.size, D.idx.getD D.O[i]! D.O.size = i
  invI_lt : ∀ i < D.O.size, D.invI[i]! < D.O.size
  mul_invI : ∀ i < D.O.size, Code.mul D.O[i]! D.O[D.invI[i]!]! = Code.one

@[expose] def InIdx (D : GrpData) (A : Array ℕ) (x : V₀ ≃ₗ[ZMod 2] V₀) : Prop :=
  ∃ i ∈ A, i < D.O.size ∧ Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) D.O[i]!

@[expose] noncomputable def idxSub (D : GrpData) (gens : Array ℕ) :
    Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  codeSubgroup (gens.toList.map fun i => D.O[i]!)

@[expose] noncomputable def GrpFacts.elt {minus : Bool} {D : GrpData} (hD : GrpFacts minus D) (i : ℕ) :
    V₀ ≃ₗ[ZMod 2] V₀ :=
  hD.enumO.elem D.O[i]!

end CFSG.GF2Type.Smith1979W3.Cert690

end
