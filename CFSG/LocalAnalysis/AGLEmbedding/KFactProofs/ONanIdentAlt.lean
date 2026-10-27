module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbedding.AltBeta
public import CFSG.LocalAnalysis.AGLEmbedding.AltSix

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Cyclic

variable {K : Type*} [Group K] [Finite K] {n p : ℕ}

theorem not_sq_dvd_factorial_of_lt (hp : p.Prime) (hn0 : 0 < n) (hn : n < 2 * p) :
    ¬ p ^ 2 ∣ Nat.factorial n := by
  have hp2 := hp.two_le
  have hnp : n < p ^ 2 := by nlinarith
  rw [hp.pow_dvd_factorial_iff (b := 2) (Nat.log_lt_of_lt_pow hn0.ne' hnp)]
  have hdiv : n / p < 2 := Nat.div_lt_of_lt_mul (by omega)
  simpa using hdiv

theorem isCyclic_sylow_of_lt (hp : p.Prime) (hn0 : 0 < n) (hn : n < 2 * p)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) : IsCyclic (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : Nat.card K ∣ Nat.factorial n := by
    have h1 : Nat.card K = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
    have h2 := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
    rw [h1]
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using h2
  have hnd : ¬ p ^ 2 ∣ Nat.card K := fun h =>
    not_sq_dvd_factorial_of_lt hp hn0 hn (h.trans hdvd)
  have hf : (Nat.card K).factorization p ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact hnd ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 hlt)
  refine isCyclic_of_card_dvd_prime (p := p) ?_
  have hT : Nat.card (T : Subgroup K) = p ^ (Nat.card K).factorization p :=
    Sylow.card_eq_multiplicity T
  rw [hT]
  exact (pow_dvd_pow p hf).trans (dvd_of_eq (pow_one p))

end Cyclic

theorem smallIdentAlt : SmallIdentAlt := by
  intro K _ _ n hn5 ⟨e⟩ p hp hp2 T hT hΓ _
  rcases lt_trichotomy n (2 * p) with hlt | heq | hgt
  · exact absurd (isCyclic_sylow_of_lt hp (by omega) hlt e T) hT
  · subst heq
    exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact absurd (glbCore_one_eq_top hp hp2 (by omega) e T) hΓ

theorem oneLieIdentAlt : OneLieIdentAlt := by
  intro K _ _ n hn5 ⟨e⟩ p hp hp2 T hT hΓ hAut
  exfalso
  by_cases hsmall : n ≤ 2 * p
  · apply hAut
    by_cases h6 : n = 6
    · subst h6
      rw [SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)]
      exact pRank_top_mulAut_alternatingGroup_six_le hp hp2
    · exact (pRank_top_mulAut_le hn5 h6 e hp).trans (Nat.div_le_of_le_mul (by omega))
  · exact hΓ (glbCore_one_eq_top hp hp2 (by omega) e T)

end CFSG.AGLEmbedding
