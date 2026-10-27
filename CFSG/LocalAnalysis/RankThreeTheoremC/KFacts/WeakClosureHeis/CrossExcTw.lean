module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar Polynomial
open CFSG.RankThree.Chevalley
  (exhaustionPhi exact_E_type_and_triality_cross_prime_factor_exhaustion)
open CFSG.RankThree.PartOne.K128
  (sylowShape_D4 pRank_le_one_D4_twelve dvd_phiNat_of_dvd_cycloVal)

private theorem degCountTw_eq_two' {e : ℕ} (h : degCountTw e = 2) : e = 3 ∨ e = 4 := by
  have h60 := le_sixty_of_degCountTw_pos (e := e) (by omega)
  have key : ∀ e ≤ 60, degCountTw e = 2 → e = 3 ∨ e = 4 := by decide
  exact key e h60 h

section TwistedE6

private theorem sdAt_twistedE6_group {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    [Finite (twistedE6RootGroup F σ)] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpℓ : p ≠ ℓ) :
    SylowDichotomyAt (twistedE6RootGroup F σ) p := by
  have hpq : ¬ p ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h3 : 3 ≤ degCountTw e
  · rcases eq_of_three_le_degCountTw h3 with rfl | rfl | rfl
    ·
      obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_one hℓ hf F hF σ hσ hp (by omega) he
      exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
    ·
      obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_two hℓ hf F hF σ hσ hp (by omega) he
      exact SylowDichotomyAt.of_elemAbelian hp hE hc (by norm_num)
    ·
      have h7 : 7 ≤ p := by
        haveI : Fact p.Prime := ⟨hp⟩
        have hne : (((ℓ ^ f : ℕ)) : ZMod p) ≠ 0 := fun h0 =>
          hpq ((ZMod.natCast_eq_zero_iff _ _).1 h0)
        have hdvd := ZMod.orderOf_dvd_card_sub_one hne
        rw [he] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      obtain ⟨m, hm⟩ :=
        exists_sylowTorus_twistedE6 hℓ hf F hF σ hσ hp h7 hpq (by rw [he]; exact h3)
      refine SylowDichotomyAt.of_sylow_comm fun S => ?_
      exact IsMulCommutative.of_comm fun a b =>
        Subtype.ext (mul_comm_of_sylowTorus hm S.isPGroup' a.2 b.2)
  ·
    apply SylowDichotomyAt.of_card_elemAbelian_le hp
    by_cases h1 : degCountTw e ≤ 1
    · exact (rankLE1_twistedE6 hℓ hf F hF σ hσ hp hpq (by rw [he]; exact h1)).rankLE2
    · rcases degCountTw_eq_two' (e := e) (by omega) with rfl | rfl
      · exact (sylowTorus_twistedE6_three hℓ hf F hF σ hσ hp he).rankLE2 hp le_rfl
      · exact (sylowTorus_twistedE6_four hℓ hf F hF σ hσ hp he).rankLE2 hp le_rfl

theorem sdLieCross_twistedE6 : SDLieCrossAt .twistedE6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm
  haveI : Finite (twistedE6RootGroup F σ) := Finite.of_equiv K e.toEquiv
  exact SylowDichotomyAt.of_mulEquiv hp e (sdAt_twistedE6_group hℓ hf F hF σ hσ hp h5 hpℓ)

end TwistedE6

section TrialityD4

theorem sdLieCross_trialityD4 : SDLieCrossAt .trialityD4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ hpK
  have hch := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have hℓ : ℓ.Prime := hch.1.1
  have hf : 1 ≤ f := hch.1.2.1
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hch.2
  have hF3 : Nat.card F = (ℓ ^ f) ^ 3 := hF
  haveI : Finite (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := Finite.of_equiv K e.toEquiv
  refine SylowDichotomyAt.of_mulEquiv hp e (SylowDichotomyAt.of_card_elemAbelian_le hp ?_)
  obtain ⟨m, hm, hd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega)
    (Ne.symm hpℓ) hch).1 hpK).2.2.2.2 rfl
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  by_cases h12 : m = 12
  ·
    subst h12
    have h24 : (ℓ ^ f) ^ 2 ≤ (ℓ ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
    have h1 : (p : ℤ) ∣ (((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub h24]
      push_cast
      simpa only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one,
        Nat.cast_pow] using hd
    exact rankLE2_of_pRank_le_one hp
      (pRank_le_one_D4_twelve hℓ hf F hF3 σ hσ hp h5 (Int.natCast_dvd_natCast.1 h1))
  ·
    have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
    exact rankLE2_of_sylowShape hp
      (sylowShape_D4 hf F hF3 σ hσ hm' hp h5 (dvd_phiNat_of_dvd_cycloVal hq1 hm' hd))

end TrialityD4

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
