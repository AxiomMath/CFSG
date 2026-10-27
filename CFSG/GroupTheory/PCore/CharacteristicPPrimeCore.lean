module

public import CFSG.Foundations.Basic

public section

namespace CFSG

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem characteristic_p_normal_prime_complement_trivial (hH : IsCharacteristicP p H) :
    (∀ N : Subgroup H, N.Normal → ¬ p ∣ Nat.card N → N = ⊥) ∧ pPrimeCore p H = ⊥ := by
  have hp : p.Prime := Fact.out
  have hQn : (pCore p H).Normal := pCore_normal
  have hQp : IsPGroup p (pCore p H) := pCore_isPGroup
  have hinf : ∀ N : Subgroup H, ¬ p ∣ Nat.card N → N ⊓ pCore p H = ⊥ := by
    intro N hN
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQp
    have hd1 : Nat.card (N ⊓ pCore p H : Subgroup H) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (N ⊓ pCore p H : Subgroup H) ∣ p ^ k :=
      hk ▸ Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (Nat.card N) (p ^ k) :=
      Nat.Coprime.pow_right k ((hp.coprime_iff_not_dvd.2 hN).symm)
    exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hmain : ∀ N : Subgroup H, N.Normal → ¬ p ∣ Nat.card N → N = ⊥ := by
    intro N hNn hN
    have hcomm : ⁅N, pCore p H⁆ = ⊥ := by
      have h1 : ⁅N, pCore p H⁆ ≤ N := by
        have := hNn
        exact Subgroup.commutator_le_left N _
      have h2 : ⁅N, pCore p H⁆ ≤ pCore p H := by
        have := hQn
        exact Subgroup.commutator_le_right N _
      exact le_bot_iff.1 (hinf N hN ▸ le_inf h1 h2)
    have hle : N ≤ pCore p H :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans hH
    have h := hinf N hN
    rwa [inf_of_le_left hle] at h
  refine ⟨hmain, hmain _ pPrimeCore_normal ?_⟩
  exact (hp.coprime_iff_not_dvd).1 pPrimeCore_coprime_card

end CFSG
