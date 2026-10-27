module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinTwo
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Assembly.LowTwoRank

theorem not_dvd_two_mul_gcd_pred {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 * Nat.gcd 3 (p - 1) := by
  intro h
  have h2 := hp.two_le
  rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  · have := Nat.le_of_dvd (by omega) (h'.trans (Nat.gcd_dvd_right 3 (p - 1)))
    omega

theorem not_dvd_two_mul_gcd_succ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 * Nat.gcd 3 (p + 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  · have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).1 (h'.trans (Nat.gcd_dvd_right 3 (p + 1)))
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem kFactLinThreeOut : KFactLinThreeOut := by
  intro K _ _ d ⟨e⟩ p hp hp2 ⟨q, hqp, hq1, hd⟩
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : StatedClassicalModel K .PSL 3 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  have hbound := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) (le_refl 3) q.prime_p q.exponent_pos hm).1
  rw [hqp, hq1] at hbound
  intro hdvd
  have := not_dvd_two_mul_gcd_pred hp hp2
  simp only [CFSG.RankThree.OuterOrder.determinantParameter, mul_one, pow_one] at hbound this
  exact this (hdvd.trans hbound)

theorem kFactUnitaryThreeOut : KFactUnitaryThreeOut := by
  intro K _ _ d ⟨e⟩ p hp hp2 ⟨q, hqp, hq1, hd⟩
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hbound := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) (le_refl 3) q.prime_p q.exponent_pos hm).1
  rw [hqp, hq1] at hbound
  intro hdvd
  have := not_dvd_two_mul_gcd_succ hp hp2
  simp only [CFSG.RankThree.OuterOrder.determinantParameter, mul_one, pow_one] at hbound this
  exact this (hdvd.trans hbound)

theorem kFactLieCharOut : KFactLieCharOut :=
  kFactLieCharOut_of kFactLinThreeOut kFactUnitaryThreeOut

end CFSG.AGLEmbeddingD2
