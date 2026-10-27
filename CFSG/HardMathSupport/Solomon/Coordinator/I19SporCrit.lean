module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

section Crit

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem i19s_vacuous (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center K = ⊥)
    (hout : Nat.card (Outer K) ≤ 2) (h : ¬ p ^ 2 ∣ Nat.card K) :
    IsLocallyBalancedAbs p 2 K := by
  intro D hD hcard
  exfalso
  have hcop : Nat.Coprime p (Nat.card (Outer K)) :=
    coprime_of_le_two hp hp2 Nat.card_pos.ne' hout
  have hDp : IsPGroup p D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  obtain ⟨E, -, hEc⟩ := exists_elemAbelian_of_le_inner hcen (le_inner_of_isPGroup hcop hDp) hD
  exact h (hEc.trans hcard ▸ Subgroup.card_subgroup_dvd_card E)

end Crit

section Sporadic

theorem i19s_balanced_of_onePair {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hbr : Nonempty (NativeSporadic.Carrier name ≃* (TauCeti.CFSGIndex.sporadic name).Group))
    (hpair : SporadicOnePairHolds name p) (hOut : SporadicOuterLeTwo)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group)) :
    IsLocallyBalancedAbs p 2 S := by
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨h1, h2⟩ := hpair
  have he' : Nonempty (S ≃* NativeSporadic.Carrier name) := ⟨he.some.trans hbr.some.symm⟩
  have := hS
  have h1' := h1 S he'
  have h2' := h2 S he'
  have hone := isLocallyOneBalancedAbs_of_parts hp hp2 hcen (hOut S hS hnab name he) h1' h2'
  exact hone.isLocallyBalancedAbs hp (by norm_num)

end Sporadic

end CFSG.HardMathSupport.Solomon.Coordinator
