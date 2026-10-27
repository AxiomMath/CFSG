module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def isExcEnnolaIdx (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ q, e = .F4 q) ∨ (∃ q, e = .E7 q) ∨ (∃ q, e = .E8 q) ∨ (∃ q, e = .twistedE6 q)

@[expose] def CompIdxEnnolaAt (p : ℕ) (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ innAutDerived S → β ^ p = 1 → β ≠ 1 →
    ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
      ∃ i : TauCeti.CFSGIndex, Nonempty (↥K ⧸ Subgroup.center ↥K ≃* i.Group) ∧
        ∃ j : ℕ, Odd j ∧ IdxOver d.characteristic (fieldSize d ^ j) i

@[expose] def LieCompIdxEnnola (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ∣ fieldSize d.1 + 1 → P d.1 →
    CompIdxEnnolaAt p d.1 (TauCeti.CFSGIndex.lie d).Group

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
