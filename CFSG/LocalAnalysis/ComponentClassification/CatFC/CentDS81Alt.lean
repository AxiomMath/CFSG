module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8TAlt
public import CFSG.Sporadic.Co2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem autCentralizer_conj_eq_centralizer_singleton {X : Type} [Group X] (τ : X) :
    CFSG.EvenSporadicStandard.HSStd.autCentralizer (MulAut.conj τ) =
      centralizer ({τ} : Set X) := by
  ext g
  show MulAut.conj τ g = g ↔ g ∈ centralizer ({τ} : Set X)
  rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem five_pow_four_dvd_factorial_of_dvd {m : ℕ} (h : 23 ∣ m.factorial) :
    5 ^ 4 ∣ m.factorial := by
  have hm : 23 ≤ m := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 23)).1 h
  exact dvd_trans (by decide : 5 ^ 4 ∣ Nat.factorial 23) (Nat.factorial_dvd_factorial hm)


theorem not_co2_quotient_alternating {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n : ℕ}
    (hn : 5 ≤ n) (θ : X ≃* alternatingGroup (Fin n)) (τ : X) (hτ : orderOf τ = 2) :
    ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
      Carrier .Co2) := by
  rintro ⟨e⟩
  have hG : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  have hshape : IsCo2Shape (Nat.card ↥(centralizer ({τ} : Set X))) :=
    isCo2Shape_of_quotient e hG
  have hX : Nat.card X = n.factorial / 2 := by
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hC23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X)) :=
    dvd_trans (by norm_num : (23 : ℕ) ∣ 42305421312000) hshape.dvd
  have hCX : Nat.card ↥(centralizer ({τ} : Set X)) ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card _
  have h2fact : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hhalf : n.factorial / 2 ∣ n.factorial := ⟨2, (Nat.div_mul_cancel h2fact).symm⟩
  have h23fact : 23 ∣ n.factorial := by
    rw [hX] at hCX
    exact dvd_trans (dvd_trans hC23 hCX) hhalf
  have hn23 : 23 ≤ n := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 23)).1 h23fact
  have hn6 : n ≠ 6 := by omega
  have h5fact : 5 ^ 4 ∣ n.factorial := five_pow_four_dvd_factorial_of_dvd h23fact
  have hτ2 : τ * τ = 1 := by
    have h := pow_orderOf_eq_one τ
    rw [hτ, pow_two] at h
    exact h
  have hσ2 : MulAut.conj τ * MulAut.conj τ = 1 := by
    have h : MulAut.conj (τ * τ) = MulAut.conj τ * MulAut.conj τ := map_mul MulAut.conj τ τ
    rw [← h, hτ2, map_one]
  by_cases hσ1 : MulAut.conj τ = 1
  ·
    have htop : centralizer ({τ} : Set X) = ⊤ := by
      have h := autCentralizer_conj_eq_centralizer_singleton τ
      rw [hσ1] at h
      rw [← h]
      ext g
      show (1 : MulAut X) g = g ↔ _
      simp
    have hCeq : Nat.card ↥(centralizer ({τ} : Set X)) = Nat.card X := by
      rw [htop, Subgroup.card_top]
    have h5X : 5 ^ 4 ∣ Nat.card X := by
      rw [hX]
      have h2X : 5 ^ 4 ∣ 2 * (n.factorial / 2) := by
        rw [Nat.mul_div_cancel' h2fact]
        exact h5fact
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h2X
    have h5C : 5 ^ 4 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
      rw [hCeq]
      exact h5X
    exact hshape.not_dvd_pow_five_four h5C
  ·
    obtain ⟨a, -, -, hacard⟩ :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.card_autCentralizer_alt n hn hn6 θ
        (MulAut.conj τ) hσ2 hσ1
    rw [autCentralizer_conj_eq_centralizer_singleton] at hacard
    have h23 : 23 ∣ (n - 2 * a).factorial * 2 ^ a * a.factorial := by
      rw [← hacard]
      exact dvd_mul_of_dvd_right hC23 2
    have h5prod : 5 ^ 4 ∣ (n - 2 * a).factorial * 2 ^ a * a.factorial := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 23)).1 h23 with h | h
      · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 23)).1 h with h' | h'
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
            (five_pow_four_dvd_factorial_of_dvd h') _) _
        · exfalso
          have h23_2 : 23 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h'
          norm_num at h23_2
      · exact dvd_mul_of_dvd_right (five_pow_four_dvd_factorial_of_dvd h) _
    rw [← hacard] at h5prod
    exact hshape.not_dvd_pow_five_four
      (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5prod)

theorem ds81_alternating {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n : ℕ} (hn : 5 ≤ n)
    (θ : X ≃* alternatingGroup (Fin n)) (τ : X) (hτ : orderOf τ = 2)
    (_hchar : IsCharacteristicP 2 ↥(centralizer ({τ} : Set X)))
    (_hab : IsMulCommutative (pCore 2 ↥(centralizer ({τ} : Set X)))) :
    ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
      Carrier .Co2) :=
  not_co2_quotient_alternating hn θ τ hτ

end CFSG.ComponentClassification.CatFC.DS81
