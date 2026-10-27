module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

noncomputable def adjointQuotientEquiv (τ : Tag) (F : Type) [Field F] [Finite F] :
    AdjointQuotient τ F ≃* adjointGroup τ F :=
  (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := F))).trans
    QuotientGroup.quotientBot

theorem wcOn_of_untwisted_model {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime]
    (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (h : UntwistedChevalleyModel K τ (ℓ ^ f))
    (H : ∀ (F : Type) [Field F] [Finite F], Nat.card F = ℓ ^ f → ¬ p ∣ Nat.card F →
      WCOn p (adjointGroup τ F)) : WCOn p K := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have hp : p.Prime := Fact.out
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hcard]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  exact WCOn.of_mulEquiv (e.trans (adjointQuotientEquiv τ F)) (H F hcard hpq)

theorem eq_three_or_five_le' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by norm_num)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
