module

public import CFSG.HardMathSupport.Solomon.Coordinator.WeakModel
public import CFSG.HardMathSupport.Solomon.Coordinator.U38Main
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem w3_pp_eq_eight {p e : ℕ} (hp : p.Prime) (he : p ^ e = 8) : p = 2 ∧ e = 3 := by
  have he0 : e ≠ 0 := by
    rintro rfl
    norm_num at he
  have hp2 : p = 2 := by
    have hd : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← he]
      exact dvd_pow_self p he0
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  subst hp2
  refine ⟨rfl, Nat.pow_right_injective le_rfl ?_⟩
  change 2 ^ e = 2 ^ 3
  rw [he]

theorem u38_isLocallyBalancedAbs' {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp : p = 2) (hf : f = 3) : IsLocallyBalancedAbs 3 2 (primeFormP h (idGram K 3)) := by
  subst hp hf
  exact U38.u38_isLocallyBalancedAbs h

theorem dvd_card_galoisField_sub_one {p : ℕ} (hp : 1 < p) (Q : TauCeti.PrimePower)
    [Fact Q.p.Prime] (hQ : Q.card % p = 1) : p ∣ Nat.card (GaloisField Q.p Q.exponent) - 1 := by
  rw [GaloisField.card _ _ Q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hQ, Nat.mod_eq_of_lt hp]))

theorem unitary_catalogue_model {S : Type} [Group S] (r : ℕ) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r Q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r Q, hv⟩).Group) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData Q.p Q.exponent K),
      ¬(r + 1 = 3 ∧ Q.p ^ Q.exponent = 2) ∧ Nonempty (S ≃* primeFormP h (idGram K (r + 1))) := by
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv e
  obtain ⟨⟨hℓ, hf, -, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData Q.p Q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  refine ⟨K, inferInstance, h, fun h2 => hq (by rw [h2.1, h2.2]), ⟨?_⟩⟩
  exact (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm

theorem weakLThreeEpsThree_holds : WeakLThreeEpsThree := by
  intro S _ _ hS hnab idx hidx he
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  change CFSG.HardMathSupport.Timmesfeld.LocalTwo.IsLpEpsIndex 3 d at hidx
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    exact isWeaklyLocallyBalancedAbs_of_mulEquiv
      (e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)))
      (weakBalance_projectiveSL Nat.prime_three (by norm_num)
        (dvd_card_galoisField_sub_one (by norm_num) Q hQ))
  · subst hd
    obtain ⟨K, _, h, hne, ⟨e'⟩⟩ := unitary_catalogue_model 2 Q hv e
    have hpq : 3 ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    by_cases h8 : Q.p ^ Q.exponent = 8
    · obtain ⟨hp2, he3⟩ := w3_pp_eq_eight Q.prime_p h8
      exact isWeaklyLocallyBalancedAbs_of_mulEquiv e'
        (i1910_weakAbs_of_abs (u38_isLocallyBalancedAbs' h hp2 he3))
    · exact isWeaklyLocallyBalancedAbs_of_mulEquiv e'
        (weakBalance_primeFormP h Nat.prime_three (by norm_num) hne (fun h' => h8 h'.2) hpq)

theorem weakLFiveEpsFive_holds : WeakLFiveEpsFive := by
  intro S _ _ hS hnab idx hidx he
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  change CFSG.HardMathSupport.Timmesfeld.LocalTwo.IsLpEpsIndex 5 d at hidx
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    exact isWeaklyLocallyBalancedAbs_of_mulEquiv
      (e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 4 Q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 _)))
      (weakBalance_projectiveSL Nat.prime_five (by norm_num)
        (dvd_card_galoisField_sub_one (by norm_num) Q hQ))
  · subst hd
    obtain ⟨K, _, h, -, ⟨e'⟩⟩ := unitary_catalogue_model 4 Q hv e
    have hpq : 5 ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    exact isWeaklyLocallyBalancedAbs_of_mulEquiv e'
      (weakBalance_primeFormP h Nat.prime_five (by norm_num) (by norm_num) (by norm_num) hpq)

theorem u3EightTwoBalanceThree_holds : U3EightTwoBalanceThree := by
  intro S _ _ hS hnab idx hidx he
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  obtain ⟨Q, hd, hQ8⟩ := hidx
  change d = _ at hd
  subst hd
  obtain ⟨K, _, h, -, ⟨e'⟩⟩ := unitary_catalogue_model 2 Q hv e
  have h8 : Q.p ^ Q.exponent = 8 := by rw [← TauCeti.PrimePower.card_def]; exact hQ8
  obtain ⟨hp2, he3⟩ := w3_pp_eq_eight Q.prime_p h8
  exact IsLocallyBalancedAbs.of_mulEquiv e' (u38_isLocallyBalancedAbs' h hp2 he3)

end CFSG.HardMathSupport.Solomon.Coordinator
