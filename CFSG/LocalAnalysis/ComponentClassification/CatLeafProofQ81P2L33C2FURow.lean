module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FUInner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog

namespace PSUTwo

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem not_isPGroup_fixed (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) (β : MulAut (PU h n))
    (hβ : orderOf β = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  intro hP
  have hO := pPrimeCore_fixed_eq_bot h hn hq β hβ
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  rcases (even_unitary_involution_matrix_lifts h hC hn hq β hβ).1 with hid | hbar
  · obtain ⟨y, hy, hy1, hym⟩ := exists_fixed_odd_of_refl h hn hq β hβ hid
    have hodd : Odd (2 ^ f + 1) :=
      (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩).add_one
    exact false_of_fixed hO hP hy hy1 hodd hym
  · obtain ⟨y, hy, hy1, hym⟩ := exists_fixed_order_three_of_bar h hn hq β hβ hbar
    exact false_of_fixed hO hP hy hy1 (by decide) hym

end PSUTwo

theorem twoNilpFor_psu : PSURow := by
  intro Y _ _ hY _ _ a ha hP
  exfalso
  obtain ⟨n, f, ⟨hprime, hf, hn, hq⟩, K, _, _, hK, ⟨e⟩⟩ := hY
  have hq' : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => hq (by rw [h3.1, h3.2])
  have h : UnitaryFieldData 2 f K := ⟨hprime, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n) (K := K))
  let ψ : Y ≃* PSUTwo.PU h n := e.trans ((unitaryPSUEquiv h (by omega)).symm.trans χ.symm)
  have : Finite (PSUTwo.PU h n) := Finite.of_equiv _ ψ.toEquiv
  exact PSUTwo.not_isPGroup_fixed h hn hq' (MulAut.congr ψ a) ((orderOf_congr ψ a).trans ha)
    (isPGroup_fixedPoints_congr ψ a hP)

end CFSG.ComponentClassification.HarrisLit.L33.C2
