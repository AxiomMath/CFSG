module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Base6

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem symCent_tt (n : ℕ) {σ : Sym (n + 6)} (hσ : σ.cycleType = {2, 2, 2}) :
    Nonempty (↥(Subgroup.centralizer ({σ} : Set (Sym (n + 6)))) ≃* (Z 2 × Sym 4) × Sym n) := by
  have hτ : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 * Equiv.swap 4 5).cycleType =
      {2, 2, 2} := by
    have h1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3).cycleType = {2, 2} :=
      Equiv.Perm.cycleType_swap_mul_swap_of_nodup
        (x := (0 : Fin 6)) (y := 1) (z := 2) (t := 3) (by decide)
    have h2 : (Equiv.swap (4 : Fin 6) 5).cycleType = {2} :=
      Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
    have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3)
        (Equiv.swap 4 5) :=
      (Equiv.Perm.disjoint_swap_swap (x := (0 : Fin 6)) (y := 1) (z := 4) (t := 5)
        (by decide)).mul_left
        (Equiv.Perm.disjoint_swap_swap (x := (2 : Fin 6)) (y := 3) (z := 4) (t := 5)
          (by decide))
    rw [Equiv.Perm.Disjoint.cycleType_mul hd, h1, h2]
    decide
  have hτsum : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 *
      Equiv.swap 4 5).cycleType.sum = 6 := by
    rw [hτ]
    decide
  obtain ⟨e₁⟩ := symCent_extend n 6 hτsum (σ := σ) (hσ.trans hτ.symm)
  obtain ⟨e₂⟩ := symCent_base_six hτ
  exact ⟨e₁.trans (MulEquiv.prodCongr e₂ (MulEquiv.refl (Sym n)))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
