module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ} {S : Type*} [Group S] [Finite S]

@[expose] def NoElemAbelianSquareAut (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D ≠ p ^ 2

theorem exists_square_of_aut (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hout : Nat.card (Outer S) ≤ 2) {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) : ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hcop : Nat.Coprime p (Nat.card (Outer S)) :=
    coprime_of_le_two hp hp2 Nat.card_pos.ne' hout
  have hDp : IsPGroup p D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_of_le_inner hcen (le_inner_of_isPGroup hcop hDp) hD
  exact ⟨E, hE, hEc.trans hcard⟩

theorem noElemAbelianSquareAut_of_not_dvd (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hout : Nat.card (Outer S) ≤ 2) (h2 : ¬ p ^ 2 ∣ Nat.card S) :
    NoElemAbelianSquareAut p S := by
  intro D hD hcard
  obtain ⟨E, -, hEc⟩ := exists_square_of_aut hp hp2 hcen hout hD hcard
  exact h2 (hEc ▸ Subgroup.card_subgroup_dvd_card E)

theorem isLocallyBalancedAbs_two_of_noElemAbelianSquareAut {K : Type*} [Group K]
    (h : NoElemAbelianSquareAut p K) : IsLocallyBalancedAbs p 2 K :=
  fun D hD hcard _ _ _ => absurd hcard (h D hD)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
