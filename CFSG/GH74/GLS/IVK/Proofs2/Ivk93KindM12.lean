module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Kinds

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P34

@[expose] def Ivk93KindM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.m12 S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) →
      PerfInJ H → HasTwoInvolutionClasses (HBar H) →
      FUS H ∧ NativeSporadic.IsSporadic ↥(generalizedFitting (HBar H)) .M12

theorem Ivk93KindM12.toKind (h : Ivk93KindM12) : Ivk93Kind Kind.m12 :=
  fun G _ _ z S hctx H hne hCH hV hs hn hPerf h2 =>
    Or.inr (h G z S hctx H hne hCH hV hs hn hPerf h2).1

end CFSG.GH74.GLS.IVK.Proofs2
