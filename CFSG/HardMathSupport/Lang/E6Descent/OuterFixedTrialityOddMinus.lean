module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOdd
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddMinusFold
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnMain

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.GH74.GLS.Stage2.OddAut
open CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GH74.GLS.SP (foldFix)

theorem card_fixSub_minusToral {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hs : D4MinusToral p f hp K σ s) :
    ∃ m : ℕ, m ∣ (p ^ f) ^ 2 - 1 ∧
      Nat.card ↥(fixedSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) =
        ((p ^ f) ^ 3 * m) * (1 + (p ^ f) ^ 3) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have hA : A2Std σ₄ b ((p ^ f) ^ 4) := un_a2Std hp2 hf hq hK₄ hσ₄ hb3 hb1
  have hεσ : ∀ c, ε (σ₄ c) = σ₄ (ε c) := un_eps_sigma hσ₄ hε
  have hεε : ∀ c, (ε * ε) (σ₄ c) = σ₄ ((ε * ε) c) := fun c => by
    show ε (ε (σ₄ c)) = σ₄ (ε (ε c))
    rw [hεσ, hεσ]
  have hφ₄ := a2_hφ_of_class (σ := σ₄) (d := b) hs₄
  have hcomm := unTau_comm_phi σ₄ ε (fun c => (hεσ c).symm) b (un_eps_unit hq hε hb3) s₄ hs₄
  have hcommε := unField_comm_phi σ₄ (ε * ε) hεε b (un_eps_sq_unit hq hε hb3) s₄ hs₄
  obtain ⟨m, hm, hX⟩ := un_polarity_core_card hA _ hφ₄ hp2 hf rfl ε hε hcomm hcommε
  obtain ⟨e', -⟩ := un_fixfix_equiv hA _ ε hcomm
  refine ⟨m, hm, ?_⟩
  rw [← card_fixSub_eq_card_fixedSubgroup, Nat.card_congr e.toEquiv, ← hX]
  exact (Nat.card_congr e'.toEquiv).symm

theorem minusToralBound : MinusToralBound := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ s hs hN
  obtain ⟨m, hm, hcard⟩ := card_fixSub_minusToral hp hp2 hf hq hK hσ hs
  rw [hcard]
  refine (Dvd.dvd.trans ?_ (CFSG.HardMathSupport.Lang.Proving.pgu3_order_dvd_G2 (p ^ f)))
  rw [add_comm 1]
  exact mul_dvd_mul (mul_dvd_mul_left _ hm) dvd_rfl

end CFSG.HardMathSupport.Lang.E6Descent
