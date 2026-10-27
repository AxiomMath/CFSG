module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS07AutRankU38

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

section Arith

theorem not_sq_dvd_u38 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : ¬ p ^ 2 ∣ 99283968 := by
  intro hd
  have hN : (99283968 : ℕ) = 2 ^ 10 * 3 ^ 6 * 7 * 19 := by norm_num
  rw [hN] at hd
  have hpd : p ∣ 2 ^ 10 * 3 ^ 6 * 7 * 19 := (dvd_pow_self p two_ne_zero).trans hd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
    · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h
      subst hp7
      norm_num at hd
  · have hp19 : p = 19 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).1 h
    subst hp19
    norm_num at hd

end Arith

section Certs


theorem card_mulAut_dvd_u38 {S : Type} [Group S] [Finite S] (h : catalogIs S S9.isU3eight) :
    Nat.card (MulAut S) ∣ 99283968 := by
  obtain ⟨κ, hκ⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.u38_aut_inj h
  rw [Nat.card_congr (MonoidHom.ofInjective hκ).toEquiv,
    ← CFSG.RankThree.PartTwo.Sec4.Item434U38.card_U38G]
  exact Subgroup.card_subgroup_dvd_card κ.range

theorem kDescFam_u38_of_ne_three (p : ℕ) (h3 : p ≠ 3) : KDescFam p fU38 := by
  intro hp hp2 Y _ _ K B hK hc hcB
  have hdvd := card_mulAut_dvd_u38 (S := ↥K ⧸ Subgroup.center ↥K) hc
  refine (false_of_not_sq_dvd hp hK hcB (MulEquiv.refl _) ?_).elim
  intro hsq
  exact not_sq_dvd_u38 hp hp2 h3 (hsq.trans hdvd)

end Certs

end CFSG.LocalAnalysis.GLTheoremA
