module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Model7Inv

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem s7_model7_cycleType_swap_0_2_1_4 :
    (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 4).cycleType = {2, 2} :=
  Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem s7_model7_cycleType_swap_1_2_3_4 :
    (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4).cycleType = {2, 2} :=
  Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem s7_model7_cycleType_swap_1_2_3_4_5_6 :
    (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4 * Equiv.swap 5 6).cycleType = {2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4)
      (Equiv.swap 5 6) :=
    (Equiv.Perm.disjoint_swap_swap (x := 1) (y := 2) (z := 5) (t := 6) (by decide)).mul_left
      (Equiv.Perm.disjoint_swap_swap (x := 3) (y := 4) (z := 5) (t := 6) (by decide))
  have h56 : (Equiv.swap (5 : Fin 7) 6).IsSwap :=
    Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  rw [hd.cycleType_mul, s7_model7_cycleType_swap_1_2_3_4,
    Equiv.Perm.isSwap_iff_cycleType.mp h56]
  decide

theorem s7_sym7_swap_of_threeTransp {D' : Set (Sym 7)} (hne : D'.Nonempty)
    (hinv : ∀ d ∈ D', d ^ 2 = 1 ∧ d ≠ 1) (hnorm : ∀ d ∈ D', ∀ g : Sym 7, g * d * g⁻¹ ∈ D')
    (h3 : ∀ d ∈ D', ∀ e ∈ D', (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1) :
    ∀ d ∈ D', d.cycleType = {2} := by
  intro d hd
  rcases s7_sym7_involution d (hinv d hd).1 (hinv d hd).2 with h2 | ⟨h22, _⟩ | ⟨h222, _⟩
  · exact h2
  · exfalso
    have hc1 : IsConj d (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (h22.trans s7_sym7_cycleType_two.symm)
    obtain ⟨g1, hg1⟩ := isConj_iff.mp hc1
    have hπ1 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 ∈ D' := by
      have h := hnorm d hd g1
      rwa [hg1] at h
    have hc2 : IsConj d (Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 4) :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr
        (h22.trans s7_model7_cycleType_swap_0_2_1_4.symm)
    obtain ⟨g2, hg2⟩ := isConj_iff.mp hc2
    have hπ2 : Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 4 ∈ D' := by
      have h := hnorm d hd g2
      rwa [hg2] at h
    rcases h3 _ hπ1 _ hπ2 with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exfalso
    have hc1 : IsConj d (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 * Equiv.swap 4 5) :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (h222.trans s7_sym7_cycleType_three.symm)
    obtain ⟨g1, hg1⟩ := isConj_iff.mp hc1
    have hπ1 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 * Equiv.swap 4 5 ∈ D' := by
      have h := hnorm d hd g1
      rwa [hg1] at h
    have hc2 : IsConj d (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4 * Equiv.swap 5 6) :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr
        (h222.trans s7_model7_cycleType_swap_1_2_3_4_5_6.symm)
    obtain ⟨g2, hg2⟩ := isConj_iff.mp hc2
    have hπ2 : Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4 * Equiv.swap 5 6 ∈ D' := by
      have h := hnorm d hd g2
      rwa [hg2] at h
    rcases h3 _ hπ1 _ hπ2 with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section3
