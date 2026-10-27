module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup

private theorem exists_three_elt_centralizer_le {n : ℕ} (hn6 : 6 ≤ n) (hn8 : n ≤ 8) :
    ∃ x : alternatingGroup (Fin n), orderOf x = 3 ∧
      Nat.card ↥(centralizer ({x} : Set (alternatingGroup (Fin n)))) ≤ 36 := by
  let a0 : Fin n := ⟨0, by omega⟩
  let a1 : Fin n := ⟨1, by omega⟩
  let a2 : Fin n := ⟨2, by omega⟩
  let a3 : Fin n := ⟨3, by omega⟩
  let a4 : Fin n := ⟨4, by omega⟩
  let a5 : Fin n := ⟨5, by omega⟩
  let c1 : Equiv.Perm (Fin n) := Equiv.swap a0 a1 * Equiv.swap a0 a2
  let c2 : Equiv.Perm (Fin n) := Equiv.swap a3 a4 * Equiv.swap a3 a5
  let s : Equiv.Perm (Fin n) := c1 * c2
  have hc1 : c1.IsThreeCycle := by
    rw [show c1 = Equiv.swap a0 a1 * Equiv.swap a0 a2 from rfl]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (by simp [a0, a1, Fin.ext_iff]) (by simp [a0, a2, Fin.ext_iff])
      (by simp [a1, a2, Fin.ext_iff])
  have hc2 : c2.IsThreeCycle := by
    rw [show c2 = Equiv.swap a3 a4 * Equiv.swap a3 a5 from rfl]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (by simp [a3, a4, Fin.ext_iff]) (by simp [a3, a5, Fin.ext_iff])
      (by simp [a4, a5, Fin.ext_iff])
  have hdisj : Equiv.Perm.Disjoint c1 c2 := by
    have hA : Equiv.Perm.Disjoint (Equiv.swap a0 a1) (Equiv.swap a3 a4) :=
      Equiv.Perm.disjoint_swap_swap (by simp [a0, a1, a3, a4, Fin.ext_iff])
    have hB : Equiv.Perm.Disjoint (Equiv.swap a0 a1) (Equiv.swap a3 a5) :=
      Equiv.Perm.disjoint_swap_swap (by simp [a0, a1, a3, a5, Fin.ext_iff])
    have hC : Equiv.Perm.Disjoint (Equiv.swap a0 a2) (Equiv.swap a3 a4) :=
      Equiv.Perm.disjoint_swap_swap (by simp [a0, a2, a3, a4, Fin.ext_iff])
    have hD : Equiv.Perm.Disjoint (Equiv.swap a0 a2) (Equiv.swap a3 a5) :=
      Equiv.Perm.disjoint_swap_swap (by simp [a0, a2, a3, a5, Fin.ext_iff])
    rw [show c1 = Equiv.swap a0 a1 * Equiv.swap a0 a2 from rfl,
      show c2 = Equiv.swap a3 a4 * Equiv.swap a3 a5 from rfl]
    exact (hA.mul_right hB).mul_left (hC.mul_right hD)
  have hcyc : s.cycleType = ({3, 3} : Multiset ℕ) := by
    rw [show s = c1 * c2 from rfl, hdisj.cycleType_mul, hc1.cycleType, hc2.cycleType]
    decide
  have hsign : s.sign = 1 := by
    rw [show s = c1 * c2 from rfl, Equiv.Perm.sign_mul, hc1.sign, hc2.sign]
    norm_num
  have hsord : orderOf s = 3 := by
    rw [show s = c1 * c2 from rfl, hdisj.orderOf, hc1.orderOf, hc2.orderOf, Nat.lcm_self]
  have hcent : Nat.card ↥(centralizer ({s} : Set (Equiv.Perm (Fin n)))) =
      Nat.factorial (n - 6) * 9 * 2 := by
    rw [Equiv.Perm.nat_card_centralizer, hcyc]
    simp [Fintype.card_fin, Nat.factorial]
  let x : alternatingGroup (Fin n) := ⟨s, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  have hxord : orderOf x = 3 := by
    rw [← Subgroup.orderOf_coe x]
    exact hsord
  have hle' : Nat.card ↥(centralizer ({x} : Set (alternatingGroup (Fin n)))) ≤
      Nat.card ↥(centralizer ({s} : Set (Equiv.Perm (Fin n)))) := by
    let φ : ↥(centralizer ({x} : Set (alternatingGroup (Fin n)))) →
        ↥(centralizer ({s} : Set (Equiv.Perm (Fin n)))) :=
      fun c => ⟨(c.1 : Equiv.Perm (Fin n)), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
        have hc' := congrArg (fun g : alternatingGroup (Fin n) =>
          (g : Equiv.Perm (Fin n))) hc
        simpa using hc'⟩
    apply Nat.card_le_card_of_injective φ
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : ↥(centralizer ({s} : Set (Equiv.Perm (Fin n)))) =>
      (c : Equiv.Perm (Fin n))) hab
  refine ⟨x, hxord, ?_⟩
  have h1 : Nat.card ↥(centralizer ({x} : Set (alternatingGroup (Fin n)))) ≤
      Nat.factorial (n - 6) * 9 * 2 := hle'.trans_eq hcent
  interval_cases n <;> norm_num at h1 ⊢ <;> omega

theorem false_of_alternating {L : Type*} [Group L] [Finite L] {n : ℕ}
    (e : L ≃* alternatingGroup (Fin n)) (hn : 5 ≤ n) (h3 : (Nat.card L).factorization 3 = 2)
    (hC : CentHyp L) : False := by
  haveI : Nontrivial (Fin n) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  have hcard : Nat.card L = Nat.factorial n / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rw [hcard] at h3
  by_cases h5 : n = 5
  · subst n
    have h9 : 9 ∣ Nat.factorial 5 / 2 := by
      have h2le : 2 ≤ (Nat.factorial 5 / 2).factorization 3 := by omega
      exact (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 2) (n := Nat.factorial 5 / 2)
        (by norm_num) (by norm_num)).mpr h2le
    exact (by norm_num : ¬ (9 : ℕ) ∣ Nat.factorial 5 / 2) h9
  by_cases h8 : n ≤ 8
  · have hn6 : 6 ≤ n := by omega
    have hA : CentHyp (alternatingGroup (Fin n)) := CentHyp.of_mulEquiv e.symm hC
    obtain ⟨x, hxord, hxcard⟩ := exists_three_elt_centralizer_le hn6 h8
    rcases hA.card_centralizer hxord with hc | hc <;> omega
  · push_neg at h8
    have hn9 : 9 ≤ n := by omega
    have h9dvd : Nat.factorial 9 ∣ Nat.factorial n := Nat.factorial_dvd_factorial hn9
    have h54 : 54 ∣ Nat.factorial n := dvd_trans (by norm_num : 54 ∣ Nat.factorial 9) h9dvd
    have h2dvd : 2 ∣ Nat.factorial n := dvd_trans (by norm_num : 2 ∣ Nat.factorial 9) h9dvd
    have hn_eq : Nat.factorial n = 2 * (Nat.factorial n / 2) :=
      (Nat.mul_div_cancel' h2dvd).symm
    have h27 : 27 ∣ Nat.factorial n / 2 := by
      have h54' : 2 * 27 ∣ 2 * (Nat.factorial n / 2) := by
        rw [← hn_eq]
        simpa using h54
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2)).mp h54'
    have hne : Nat.factorial n / 2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hn_eq
      exact Nat.factorial_ne_zero n hn_eq
    have h3le : 3 ≤ (Nat.factorial n / 2).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 3) (n := Nat.factorial n / 2)
        (by norm_num) hne).mp (by simpa using h27)
    omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
