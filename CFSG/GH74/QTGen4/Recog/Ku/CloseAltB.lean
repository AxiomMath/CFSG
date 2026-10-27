module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.I4Basic
public import CFSG.Quasithin.Recognition.HSTypeAutA5
public import Certificates.Data.A5

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.GorensteinWalter CFSG.Quasithin.I4 CFSG.Quasithin.HSType

theorem not_eight_dvd_card {C : Type*} [Group C] [Finite C] (D : Sylow 2 C)
    (hD : Nat.card (D : Subgroup C) = 4) : ¬ 8 ∣ Nat.card C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h8
  have e := Subgroup.card_mul_index (D : Subgroup C)
  rw [hD] at e
  have hodd : ¬ 2 ∣ Subgroup.index (D : Subgroup C) := Sylow.not_dvd_index D
  rw [← e] at h8
  obtain ⟨m, hm⟩ := h8
  exact hodd ⟨m, by omega⟩

theorem range_eq_alt {C : Type*} [Group C] [Finite C] {n : ℕ} (θ : C →* Equiv.Perm (Fin n))
    (hθ : Function.Injective θ) (hA : alternatingGroup (Fin n) ≤ θ.range)
    (hidx : Nat.card (alternatingGroup (Fin n)) * 2 = Nat.card (Equiv.Perm (Fin n)))
    (h8 : ¬ 8 ∣ Nat.card C) (h8' : 8 ∣ Nat.card (alternatingGroup (Fin n)) * 2) :
    θ.range = alternatingGroup (Fin n) := by
  have hcard : Nat.card θ.range = Nat.card C :=
    (Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv).symm
  have hpos : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hA
  have hdvd := Subgroup.card_subgroup_dvd_card θ.range
  rw [← hidx, hk] at hdvd
  have hk2 : k ∣ 2 := (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge hA (le_of_eq (by rw [hk, mul_one]))).symm
  · exfalso
    apply h8
    rw [← hcard, hk]
    exact h8'

theorem eight_dvd_odd_mul (q : ℕ) (hq : Odd q) : 8 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  rw [h1]
  obtain ⟨m, hm⟩ := (Nat.even_mul_succ_self k).two_dvd
  rw [hm]
  exact ⟨(2 * k + 1) * m, by ring⟩

end CFSG.GH74.QTGen4.Ku
