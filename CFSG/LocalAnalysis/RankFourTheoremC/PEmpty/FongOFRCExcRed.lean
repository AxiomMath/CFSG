module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
import CFSG.Blueprint.LieModelAPI
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def IsExceptionalTag (t : StatedLieTag) : Prop :=
  t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4 ∨
    t = .twistedG2 ∨ t = .twistedF4

section


@[expose] def UntwDescent (t : StatedLieTag) (τ : Tag) : Prop :=
  ∀ {ℓ f p : ℕ}, ℓ.Prime → p.Prime → 5 ≤ p → ℓ ≠ p → StatedLieAdmissible t 0 ℓ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 → α ∉ inner (adjointGroup τ K) →
        p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = ℓ ^ (f / p) ∧
          CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ k)) ≤
            CFSG.Open.pRank p (fixedSubgroup α)

@[expose] def UntwCrossRankStep (τ : Tag) : Prop :=
  ∀ {ℓ f₀ p : ℕ}, ℓ.Prime → 1 ≤ f₀ → p.Prime → 5 ≤ p → ℓ ≠ p →
    ∀ (K k : Type) [Field K] [Finite K] [Field k] [Finite k],
      Nat.card K = ℓ ^ (p * f₀) → Nat.card k = ℓ ^ f₀ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) →
        2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ k))

@[expose] def ExcCrossRankStepAt (t : StatedLieTag) : Prop :=
  match t with
  | .G2 => UntwCrossRankStep Tag.G2
  | .F4 => UntwCrossRankStep Tag.F4
  | .E6 => UntwCrossRankStep Tag.E6
  | .E7 => UntwCrossRankStep Tag.E7
  | .E8 => UntwCrossRankStep Tag.E8
  | .twistedE6 => OuterFixedRankCrossAt .twistedE6
  | .trialityD4 => OuterFixedRankCrossAt .trialityD4
  | .twistedG2 => OuterFixedRankCrossAt .twistedG2
  | .twistedF4 => OuterFixedRankCrossAt .twistedF4
  | _ => True

theorem outerFixedRankCrossAt_of_untwStep {t : StatedLieTag} {τ : Tag}
    (hmodel : ∀ (K : Type) [Group K] (ℓ f : ℕ),
      ChevalleyExceptionalModel K t ℓ f → UntwistedChevalleyModel K τ (ℓ ^ f))
    (ht : t ∈ chevalleyExceptionalTags) (hdesc : UntwDescent t τ) (hstep : UntwCrossRankStep τ) :
    OuterFixedRankCrossAt t := by
  intro K _ _ n ℓ f hadm hmodel' hT p hp hp5 hℓ hdivL α hαp hαin hrk
  obtain ⟨-, hch⟩ := (LieModel.chevalleyExceptional_iff ht).1 hmodel'
  obtain ⟨hℓp, -⟩ := hadm
  obtain ⟨M, _, _, hM, ⟨e⟩⟩ := hmodel K ℓ f hch
  have hp1 : 1 < p := hp.one_lt
  let θ : K ≃* adjointGroup τ M := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hβin : MulAut.congr θ α ∉ inner (adjointGroup τ M) := fun hin =>
    hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
  obtain ⟨hpf, k, hk, hkfin, hkcard, hrank⟩ := hdesc hℓp hp hp5 hℓ hch.1 M hM (MulAut.congr θ α)
    hβp hβin
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · subst h
      have := hch.1.2.1
      omega
    · exact h
  have hkcard' : Nat.card k = ℓ ^ f₀ := by rwa [Nat.mul_div_cancel_left _ hp.pos] at hkcard
  have hrkM : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ M)) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 θ]
    exact hrk
  have h2 := hstep hℓp hf₀ hp hp5 hℓ M k hM hkcard' hrkM
  have h3 : CFSG.Open.pRank p (fixedSubgroup (MulAut.congr θ α)) ≤
      CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α (MulAut.congr θ α) fun x => by
      simp [MulAut.congr_apply]
  omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
