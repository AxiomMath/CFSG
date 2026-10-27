module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Plane
import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem u62lb_exists_dmatU (D : primeFormUnitary h (idGram K 6))
    (hD : ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ∃ δ : Fin 6 → Kˣ, D = dmatU h δ := by
  set M : Matrix (Fin 6) (Fin 6) K := ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  have hdiag : Matrix.diagonal (Matrix.diag M) = M := hD.diagonal_diag
  have hdet : M.det = ∏ i, M i i := by
    conv_lhs => rw [← hdiag]
    rw [det_diagonal]
    rfl
  have hu : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Units.isUnit (D : GL (Fin 6) K))
  have hne : ∀ i, M i i ≠ 0 := fun i => by
    have h0 : ∏ j, M j j ≠ 0 := by
      rw [← hdet]
      exact hu.ne_zero
    exact (Finset.prod_ne_zero_iff.1 h0) i (Finset.mem_univ i)
  refine ⟨fun i => Units.mk0 (M i i) (hne i), Subtype.ext (Units.ext ?_)⟩
  exact hdiag.symm

theorem u62lb_coreFree_dmatU
    (hA : ∀ N : Subgroup (primeFormP h (idGram K 6)), TorusInv h N →
      Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (hB : ∀ g : MulAut (primeFormP h (idGram K 6)), Nat.Coprime 3 (orderOf g) →
      (∀ (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1), g (diagP h μ hμ) = diagP h μ hμ) → g = 1)
    (δ : Fin 6 → Kˣ) :
    CoreFreeAt 3 (primeFormConjHom h (idGram K 6) (dmatU h δ)) := by
  refine ⟨fun N _ hNn hcop => hA N (fun μ hμ x hx => ?_) hcop, fun g hg _ hfix => ?_⟩
  · exact hNn _ (diagP_mem_fixSub h δ μ hμ) x hx
  · exact hB g hg fun μ hμ => hfix _ (diagP_mem_fixSub h δ μ hμ)

theorem u62lb_coreFree_of_pow_three
    (hA : ∀ N : Subgroup (primeFormP h (idGram K 6)), TorusInv h N →
      Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (hB : ∀ g : MulAut (primeFormP h (idGram K 6)), Nat.Coprime 3 (orderOf g) →
      (∀ (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1), g (diagP h μ hμ) = diagP h μ hμ) → g = 1)
    (A : primeFormUnitary h (idGram K 6)) (hA3 : A ^ 3 = 1) :
    CoreFreeAt 3 (primeFormConjHom h (idGram K 6) A) := by
  obtain ⟨Q, hQ⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three
    (by norm_num : 3 ∣ 2 ^ 1 + 1) (Subgroup.zpowers A)
    (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow_self A i j).eq)
    (fun x hx => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hA3, _root_.one_zpow])
  obtain ⟨δ, hδ⟩ := u62lb_exists_dmatU h (Q⁻¹ * A * Q) (hQ A (Subgroup.mem_zpowers A))
  have hc := u62lb_coreFree_dmatU h hA hB δ
  rw [← hδ, map_mul, map_mul, map_inv] at hc
  exact (coreFreeAt_conj_iff (primeFormConjHom h (idGram K 6) A)
    (primeFormConjHom h (idGram K 6) Q)⁻¹).1 (by rwa [inv_inv])

end CFSG.HardMathSupport.Dickson.Bal207

end
