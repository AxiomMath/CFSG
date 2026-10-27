module

public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

namespace CFSG.LargeExtraspecial.AS35YT

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Blueprint

theorem ordBC_two_eq' (m : ℕ) :
    ordBC m 2 = 2 ^ (m * m) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1) := by
  simp [ordBC]

theorem exists_dvd_of_dvd_ordBC {m k p : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (h : p ∣ ordBC m 2) : ∃ i ∈ Finset.Icc 1 m, k ∣ 2 * i := by
  rw [ordBC_two_eq'] at h
  have hp2 : ¬ p ∣ 2 ^ (m * m) := fun h2 =>
    hp.ne_two hk ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h2))
  have h1 := (Nat.Prime.dvd_mul hp.prime).mp h
  rcases h1 with h1 | h1
  · exact absurd h1 hp2
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp h1
  exact ⟨i, hi, (hp.dvd_sub_one_iff hk _).mp hpi⟩

theorem ordA_ne_ordBC {n m : ℕ} (hn : 2 ≤ n) : ordA n 2 ≠ ordBC m 2 := by
  intro h
  have hA := A2Mod.Ord.profile_A (n := n) (by omega)
  rw [h] at hA
  have hN := (hA.transfer (A2Mod.Ord.profile_BC m)).1
  have h2 := A2Mod.Ord.two_mul_tri n
  rw [hN] at h2
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := n + 1) (by omega) (by omega)
    obtain ⟨i, hi, hdvd⟩ := exists_dvd_of_dvd_ordBC hp (by omega)
      (h ▸ A2Mod.Ord.dvd_ordA_two (by omega) le_rfl hp.dvd)
    obtain ⟨hi1, him⟩ := Finset.mem_Icc.mp hi
    have hcop : Nat.Coprime (n + 1) 2 := by
      rw [Nat.coprime_two_right]
      exact ⟨j, by omega⟩
    have hle : n + 1 ≤ i := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left hdvd)
    have hle' : (n + 1) * (n + 1) ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  ·
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := n) hn (by omega)
    obtain ⟨i, hi, hdvd⟩ := exists_dvd_of_dvd_ordBC hp (by omega)
      (h ▸ A2Mod.Ord.dvd_ordA_two hn (by omega) hp.dvd)
    obtain ⟨hi1, him⟩ := Finset.mem_Icc.mp hi
    have hcop : Nat.Coprime n 2 := by
      rw [Nat.coprime_two_right]
      exact ⟨j, hj⟩
    have hle : n ≤ i := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left hdvd)
    have hle' : n * n ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

theorem lieModel_PSL_false_of_PSp {X : Type} [Group X] {k m : ℕ} (h : LieModel X .PSL k 2 1)
    (h' : LieModel X .PSp m 2 1) : False := by
  obtain ⟨hk, hX⟩ := A2Mod.Ord.card_of_lieModel_PSL h
  obtain ⟨-, hX'⟩ := A2Mod.Ord.card_of_lieModel_PSp h'
  exact ordA_ne_ordBC (n := k - 1) (m := m) (by omega) (hX.symm.trans hX')

end CFSG.LargeExtraspecial.AS35YT
