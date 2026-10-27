module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup CFSG
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
  (cycleType_eq_replicate_two)

theorem inner_numeric8_false : ∀ m < 8, ∀ j < 9, 1 ≤ m → m % 2 = 0 →
    j.factorial * (2 ^ m * m.factorial) ≠ 80640 := by
  decide +kernel

theorem inner_numeric8 {n m : ℕ} (hm : 1 ≤ m) (hm2 : m % 2 = 0)
    (h : (n - 2 * m).factorial * (2 ^ m * m.factorial) = 80640) : False := by
  have hQ : 0 < 2 ^ m * m.factorial := by positivity
  have hm8 : m < 8 := by
    by_contra hc
    have h1 : (8 : ℕ).factorial ≤ m.factorial := Nat.factorial_le (by omega)
    have h2 : 2 ^ 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 8 * (8 : ℕ).factorial ≤ 2 ^ m * m.factorial := Nat.mul_le_mul h2 h1
    have h4 : 2 ^ m * m.factorial ≤ (n - 2 * m).factorial * (2 ^ m * m.factorial) :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    norm_num [Nat.factorial] at h3
    omega
  have hj9 : n - 2 * m < 9 := by
    by_contra hc
    have h1 : (9 : ℕ).factorial ≤ (n - 2 * m).factorial := Nat.factorial_le (by omega)
    have h2 : (9 : ℕ).factorial * 1 ≤ (n - 2 * m).factorial * (2 ^ m * m.factorial) :=
      Nat.mul_le_mul h1 hQ
    norm_num [Nat.factorial] at h2
    omega
  obtain ⟨j, hj⟩ : ∃ j, n - 2 * m = j := ⟨_, rfl⟩
  rw [hj] at h hj9
  exact inner_numeric8_false m hm8 j hj9 hm hm2 h

theorem outer_numeric8_false : ∀ r < 7, ∀ j < 8, 1 ≤ r → j % 2 = 0 →
    2 ^ (r - 1) * r.factorial * j.factorial ≠ 20160 := by
  decide +kernel

theorem outer_numeric8 {n r : ℕ} (hr : 1 ≤ r) (hn : 2 * r ≤ n) (hne : n % 2 = 0)
    (h : 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 20160) : False := by
  have hQ : 0 < 2 ^ (r - 1) * r.factorial := by positivity
  have hr7 : r < 7 := by
    by_contra hc
    have h1 : (7 : ℕ).factorial ≤ r.factorial := Nat.factorial_le (by omega)
    have h2 : 2 ^ 6 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 6 * (7 : ℕ).factorial ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul h2 h1
    have h4 : 2 ^ (r - 1) * r.factorial ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    norm_num [Nat.factorial] at h3
    omega
  have hj8 : n - 2 * r < 8 := by
    by_contra hc
    have h1 : (8 : ℕ).factorial ≤ (n - 2 * r).factorial := Nat.factorial_le (by omega)
    have h2 : (n - 2 * r).factorial ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      Nat.le_mul_of_pos_left _ hQ
    norm_num [Nat.factorial] at h1
    omega
  have hjeven : (n - 2 * r) % 2 = 0 := by omega
  obtain ⟨j, hj⟩ : ∃ j, n - 2 * r = j := ⟨_, rfl⟩
  rw [hj] at h hj8 hjeven
  exact outer_numeric8_false r hr7 j hj8 hr hjeven h

theorem card_alternatingGroup_fin_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem alt_not_centralizer_Z2_alt8 {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) (z : S) (hz : orderOf z = 2) :
    ¬ Nonempty (↥(centralizer ({z} : Set S)) ≃* Multiplicative (ZMod 2) ×
      alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  have hC : Nat.card (centralizer ({z} : Set S)) = 2 * 20160 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_alternatingGroup_fin_eight,
      natCard_multiplicative_zmod_two]
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact h
  have hgg : θ z * θ z = 1 := by rw [← map_mul, hzz, map_one]
  have hg2 : (θ z : Equiv.Perm (Fin n)) * (θ z : Equiv.Perm (Fin n)) = 1 := by
    have h := congrArg Subtype.val hgg
    simpa using h
  have hg1 : (θ z : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    have hz1 : z = 1 := θ.injective (by rw [map_one]; exact Subtype.ext (by simpa using h))
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨m, hm1, -, hc⟩ := cycleType_eq_replicate_two (θ z : Equiv.Perm (Fin n)) hg2 hg1
  have hmeven : m % 2 = 0 :=
    even_of_cycleType_replicate _ hc (Equiv.Perm.mem_alternatingGroup.1 (θ z).2)
  have hF := two_mul_card_centralizer_alt (by omega) (θ z) hg2 hg1 hm1 hc
  have hT := card_centralizer_singleton_mulEquiv_alt θ z
  have hFF : (n - 2 * m).factorial * (2 ^ m * m.factorial) = 80640 := by
    rw [← hF, hT, hC]
  exact inner_numeric8 hm1 hmeven hFF

theorem alt_not_fixedSubgroup_alt8 {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 7 ≤ n)
    (hne : n % 2 = 0) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} (hσ : orderOf σ = 2) :
    ¬ Nonempty (↥(fixedSubgroup σ) ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  have hFix : Nat.card (fixedSubgroup σ) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_eight]
  obtain ⟨r, hr1, hr2, hr⟩ := card_fixedSubgroup_alt hn θ hσ
  rw [hFix] at hr
  exact outer_numeric8 hr1 hr2 hne hr.symm

end CFSG.EvenSporadicStandard.M24Std.KForm
