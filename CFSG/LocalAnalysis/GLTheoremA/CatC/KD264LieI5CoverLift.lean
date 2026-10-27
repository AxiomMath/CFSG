module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLin
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.LieType.SemisimpleCentralizers.HeldLang

@[expose] def KD264I5CoverLiftExc : Prop :=
  ∀ (e : TauCeti.ValidLieTypeIndex) (k : ℕ), i5FieldBound e.1 k →
    (∃ q : TauCeti.PrimePower, e.1 = .E6 q ∨ e.1 = .twistedE6 q) →
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group) →
      ∀ β : MulAut K, β ^ 3 = 1 →
        onCenterQuotient β ∉ innAutDerived (K ⧸ Subgroup.center K) →
        ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
          Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
            IsI5UniversalCover e L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x)

theorem kd264I5CoverLift_of_inputs (hSU : I5SUClosed) (hE : KD264I5CoverLiftExc) : KD264I5CoverLift := by
  intro e k hk K _ _ hK eK β hβ3 hout
  obtain ⟨d, hd⟩ := e
  cases d with
  | A n q =>
    obtain ⟨h3n, h3q, rfl⟩ := hk
    obtain ⟨eK'⟩ := eK
    exact kd264I5CoverLift_linear n q hd h3n h3q K hK eK' β hβ3 hout
  | twistedA n q =>
    obtain ⟨h3n, h3q, rfl⟩ := hk
    obtain ⟨eK'⟩ := eK
    exact kd264I5CoverLift_unitary hSU n q hd h3n h3q K hK eK' β hβ3 hout
  | E6 q => exact hE ⟨_, hd⟩ k hk ⟨q, Or.inl rfl⟩ K hK eK β hβ3 hout
  | twistedE6 q => exact hE ⟨_, hd⟩ k hk ⟨q, Or.inr rfl⟩ K hK eK β hβ3 hout
  | _ => exact hk.elim

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
