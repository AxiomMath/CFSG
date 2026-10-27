module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits

private theorem not_dvd_of_dvd_two_mul_three {m a b p : ℕ} (hm : m ∣ 2 ^ a * 3 ^ b) (hp : p.Prime)
    (hp5 : 5 ≤ p) : ¬ p ∣ m := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 (h.trans hm) with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
    omega

section SUTwo

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

include hF in
theorem su_short_isPerfect {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    Group.IsPerfect ↥(rankOne (rootDatum hF n).rootGroup k) := by
  have hσ := unitaryInvolution_involutive hF
  have h4 : 4 ≤ Nat.card F := by rw [hF]; norm_num
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := sl2_isPerfect h4
  exact Group.IsPerfect.ofSurjective (f := (rankOneShortEquiv (hσ := hσ) hk).symm.toMonoidHom)
    (rankOneShortEquiv (hσ := hσ) hk).symm.surjective

include hF in
theorem su_last_even_card (he : Even n) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) :
    Nat.card ↥(rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n)
      k) = 6 := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  set e := (rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm
  have h2 : Nat.card (fixedSubfield F 2 1) = 2 := by
    rw [card_fixedSubfield hF]
    norm_num
  rw [Nat.card_congr e.toEquiv, card_sl2, h2]
  norm_num

include hF in
theorem su_last_odd_card (hn : ¬Even n) {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) :
    Nat.card ↥(rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n)
      k) = 216 := by
  rw [Nat.card_congr (rankOneLastOddEquiv hF hn hk).toEquiv, card_SU_three hF]
  norm_num

include hF in
theorem su_last_not_dvd {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card ↥(rankOne (rootDatum hF n).rootGroup k) := by
  by_cases he : Even n
  · exact not_dvd_of_dvd_two_mul_three (a := 1) (b := 1)
      ((dvd_of_eq (su_last_even_card hF he hk)).trans (by norm_num)) hp hp5
  · exact not_dvd_of_dvd_two_mul_three (a := 3) (b := 3)
      ((dvd_of_eq (su_last_odd_card hF he hk)).trans (by norm_num)) hp hp5

include hF in
theorem twoLevi_su : TwoLevi (rootDatum hF n) (fun _ _ => False) := by
  refine TwoLevi.of_pair (fun i => ?_) (fun i j hij _ hi hj => ?_)
  · by_cases hk : i.val + 1 < n / 2
    · exact Or.inl (commutator_eq_self_of_isPerfect (su_short_isPerfect hF hk))
    · exact Or.inr (su_last_not_dvd hF hk)
  · exfalso
    have hi' : ¬ i.val + 1 < n / 2 := fun hk =>
      hi (commutator_eq_self_of_isPerfect (su_short_isPerfect hF hk))
    have hj' : ¬ j.val + 1 < n / 2 := fun hk =>
      hj (commutator_eq_self_of_isPerfect (su_short_isPerfect hF hk))
    refine hij (Fin.ext ?_)
    have h1 : i.val < n / 2 := i.isLt
    have h2 : j.val < n / 2 := j.isLt
    omega

include hF in
theorem parabCore_su_two (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ 1) F)) : ParabCore Y 2 := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  exact (borelQuotient_su hF (by omega) ζ hζ e).parabCore_two (by rw [hF]; norm_num)
    (twoLevi_su hF)

end SUTwo

theorem parabCore_of_model_psu_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 1) : ParabCore Y 2 := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact parabCore_su_two hcard hn e

end CFSG.AGLEmbedding.ParabPrime
