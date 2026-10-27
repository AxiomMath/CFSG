module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Plus
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem d4_ord3_of_alt {Y : Type} [Group Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hm : LieModel Y .trialityD4 0 r f)
    (halt : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (r ^ f) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (r ^ f)) →
      ∀ b : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), orderOf b = 3 →
        Ord3Alt r b)
    (b : MulAut Y) (hb : orderOf b = 3) :
    (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
      ∃ s : ℕ, HHObsAt 3 s Y b ∧ (s = 2 → NoR 2 Y) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 hr hf (twistedChevalleyModel_of_lieModel hm)
  refine ord3_disj_of_alt (noR_two_of_lieModel_D4 hr hr2 hf hm) (ord3Alt_of_congr e ?_)
  exact halt K hK σ hσ _ (by rw [orderOf_congr, hb])

end CFSG.OddStandard.GH71.S55
