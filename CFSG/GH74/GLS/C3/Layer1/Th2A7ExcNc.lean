module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcLift
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.BackAuxSA
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GH74.GLS.C3.Layer1.U1aRank
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

section Witness

variable {G : Type} [Group G]

@[expose] def IsExcA7Witness (x : G) (K : Subgroup G) (T S : Subgroup G) (a : G) : Prop :=
  IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ IsSylowOf 2 (T ⊓ NxK x K) (NxK x K) ∧
    IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) ∧
    IsSylowOf 2 S ⊤ ∧ T < S ∧ a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T ∧
    S = T ⊔ zpowers a ∧
    (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom = ⊥ ∧
    (∀ p ∈ T ⊓ K, ∀ q ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom, p * q = q * p) ∧
    T = (T ⊓ K) ⊔ (T ⊓ K).map (MulAut.conj a).toMonoidHom ∧
    Nonempty (↥(T ⊓ K) ≃* DihedralGroup 4) ∧
    Nonempty (↥(T ⊓ CxK x K) ≃* Multiplicative (ZMod 4))

theorem isExceptionalA7Triple_iff {x y : G} {K : Subgroup G} :
    IsExceptionalA7Triple x y K ↔ Is2TerminalU2Triple x y K ∧
      Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧
      ∃ (T S : Subgroup G) (a : G), IsExcA7Witness x K T S a := Iff.rfl

end Witness

end CFSG.GH74.GLS
