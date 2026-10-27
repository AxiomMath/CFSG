module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial Matrix
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def regimeAThree (idx : TauCeti.ValidLieTypeIndex) (_p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ 2 ≤ m

theorem crossCharTwoFamAt_A_ge_two (hHeis : LinHeisenbergBalance) :
    CrossCharTwoFamAt .A regimeAThree := by
  rintro ⟨d, hv⟩ _ p hp hp5 hc ⟨m, q, hd, hm2⟩ hnexc
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hfour : 3 ≤ m + 1 := by omega
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) (Or.inl hfour)).2.1
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpF : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).mp (hp.dvd_of_dvd_pow hdvd))
  have hnp : p ∣ Nat.card (GaloisField q.p q.exponent) - 1 → m + 1 ≠ p := by
    intro hdiv hmp
    have hq1 : q.card % p = 1 := by
      rw [hcardF] at hdiv
      have h2 : 2 ≤ q.card := by
        have := q.prime_p.two_le
        have h3 : q.p ≤ q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact Nat.le_self_pow q.exponent_pos.ne' _
        omega
      obtain ⟨k, hk⟩ := hdiv
      have h4 : q.card = 1 + p * k := by omega
      rw [h4, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hp.one_lt
    exact (hnexc ⟨.A m q, hv⟩ (Or.inl ⟨q, by simp [← hmp], hq1⟩)).false (MulEquiv.refl _)
  have e' := LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) (GaloisField q.p q.exponent)
  exact IsLocallyBalancedAbs.of_mulEquiv (e.trans e')
    (isLocallyBalancedAbs_two_projectiveSL (n := m + 1) hfour hp hp5 hpF hnp hHeis
      (fun hpq1 => innerPlaneBalance_projectiveSL_nonsplit hfour hp hp5 hpF hpq1))

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
