module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma linesA8_mem_alt_four_swaps (a b c d e f g h : Fin 8)
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (hgh : g ≠ h) :
    Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h ∈
      alternatingGroup (Fin 8) := by
  simp only [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd, Equiv.Perm.sign_swap hef, Equiv.Perm.sign_swap hgh]
  decide

private lemma linesA8_cycleType_two_swaps (a b c d : Fin 8) (hab : a ≠ b) (hcd : c ≠ d)
    (h : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d)) :
    (Equiv.swap a b * Equiv.swap c d).cycleType = {2, 2} := by
  rw [Equiv.Perm.Disjoint.cycleType_mul h, (Equiv.Perm.isCycle_swap hab).cycleType,
    (Equiv.Perm.isCycle_swap hcd).cycleType, Equiv.Perm.card_support_swap hab,
    Equiv.Perm.card_support_swap hcd]
  norm_num [Multiset.replicate_succ]

private lemma linesA8_cycleType_four_swaps (a b c d e f g h : Fin 8)
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (hgh : g ≠ h)
    (h1 : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d))
    (h2 : Equiv.Perm.Disjoint (Equiv.swap a b * Equiv.swap c d) (Equiv.swap e f))
    (h3 : Equiv.Perm.Disjoint (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f)
      (Equiv.swap g h)) :
    (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h).cycleType =
      {2, 2, 2, 2} := by
  rw [Equiv.Perm.Disjoint.cycleType_mul h3, Equiv.Perm.Disjoint.cycleType_mul h2,
    Equiv.Perm.Disjoint.cycleType_mul h1, (Equiv.Perm.isCycle_swap hab).cycleType,
    (Equiv.Perm.isCycle_swap hcd).cycleType, (Equiv.Perm.isCycle_swap hef).cycleType,
    (Equiv.Perm.isCycle_swap hgh).cycleType, Equiv.Perm.card_support_swap hab,
    Equiv.Perm.card_support_swap hcd, Equiv.Perm.card_support_swap hef,
    Equiv.Perm.card_support_swap hgh]
  norm_num [Multiset.replicate_succ]

private def linesA8_s0 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7,
    linesA8_mem_alt_four_swaps 0 1 2 3 4 5 6 7 (by decide) (by decide) (by decide) (by decide)⟩

private def linesA8_s0' : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 6 * Equiv.swap 5 7,
    linesA8_mem_alt_four_swaps 0 1 2 3 4 6 5 7 (by decide) (by decide) (by decide) (by decide)⟩

private lemma linesA8_cycleType_s0 :
    (linesA8_s0 : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  have h := linesA8_cycleType_four_swaps 0 1 2 3 4 5 6 7 (by decide) (by decide) (by decide)
    (by decide)
    (Equiv.Perm.disjoint_swap_swap (by decide))
    (Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide)))
    (Equiv.Perm.Disjoint.mul_left
      (Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
        (Equiv.Perm.disjoint_swap_swap (by decide)))
      (Equiv.Perm.disjoint_swap_swap (by decide)))
  simpa [linesA8_s0] using h

private lemma linesA8_cycleType_s0' :
    (linesA8_s0' : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  have h := linesA8_cycleType_four_swaps 0 1 2 3 4 6 5 7 (by decide) (by decide) (by decide)
    (by decide)
    (Equiv.Perm.disjoint_swap_swap (by decide))
    (Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide)))
    (Equiv.Perm.Disjoint.mul_left
      (Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
        (Equiv.Perm.disjoint_swap_swap (by decide)))
      (Equiv.Perm.disjoint_swap_swap (by decide)))
  simpa [linesA8_s0'] using h

private lemma linesA8_cycleType_s0_mul_s0' :
    ((linesA8_s0 * linesA8_s0' : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType =
      {2, 2} := by
  have hcoe : ((linesA8_s0 * linesA8_s0' : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)) = Equiv.swap 4 7 * Equiv.swap 5 6 := by decide +kernel
  rw [hcoe]
  exact linesA8_cycleType_two_swaps 4 7 5 6 (by decide) (by decide)
    (Equiv.Perm.disjoint_swap_swap (by decide))

theorem linesA8_exists_partner {σ : alternatingGroup (Fin 8)}
    (hσ : (σ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}) :
    ∃ σ' : alternatingGroup (Fin 8), (σ' : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} ∧
      ((σ * σ' : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_cycleType_two_two_two_two linesA8_cycleType_s0 hσ)
  refine ⟨g * linesA8_s0' * g⁻¹, ?_, ?_⟩
  · have hcoe : ((g * linesA8_s0' * g⁻¹ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        (g : Equiv.Perm (Fin 8)) * (linesA8_s0' : Equiv.Perm (Fin 8)) *
          (g : Equiv.Perm (Fin 8))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, Equiv.Perm.cycleType_conj, linesA8_cycleType_s0']
  · have hgroup : σ * (g * linesA8_s0' * g⁻¹) =
        g * (linesA8_s0 * linesA8_s0') * g⁻¹ := by
      rw [hg.symm]; group
    have hcoe : ((σ * (g * linesA8_s0' * g⁻¹) : alternatingGroup (Fin 8)) :
        Equiv.Perm (Fin 8)) = (g : Equiv.Perm (Fin 8)) *
          ((linesA8_s0 * linesA8_s0' : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) *
            (g : Equiv.Perm (Fin 8))⁻¹ := by
      rw [hgroup]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, Equiv.Perm.cycleType_conj, linesA8_cycleType_s0_mul_s0']

end CFSG.EvenSporadicStandard.HNRecog.Section3
