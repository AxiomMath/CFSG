module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFacts

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups modelUniv)

variable {p f : ℕ} [Fact p.Prime]

section FactsMinus

variable {m : ℕ}

variable (p f) in
theorem finrank_minus (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank (GaloisField p f)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

theorem not_dvd_card_center_minus (hp2 : p ≠ 2) (hm : 4 ≤ m) :
    ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadMinus m (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))) := by
  have hirr := minusCoeffs_irr p f
  have : Finite (spinGroup (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus hm hirr
  exact ModelFacts.OrthAut.not_dvd_card_center_spin _ (range_spinMatrix_quadMinus hm hirr) hZ hcomap
    (fun x hx => ModelFacts.OrthAut.spin_mul_self_eq_one
      ((mem_ker_spinMatrix_quadMinus_iff hirr x).mp hx)) hp2

theorem orthFacts_minusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthFacts (fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
      (GaloisField p f) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f m (by omega)]
    omega
  have hf1 : 1 ≤ f := by omega
  have hadm : StatedLieAdmissible .POmegaMinus m p f := ⟨Fact.out, hf1, by omega⟩
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m (GaloisField p f) (minusCoeffs_irr p f)
  have hG := orthGeom_model (K' := GaloisField p (2 * f)) hK hK' hodd hQ hdim
  have : Finite (spinGroup (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (minusCoeffs_irr p f))
  exact (Exotic.centralQuot_minus hp2 hq hadm).orthFacts h4
    (not_dvd_card_center_minus hp2 (by omega)) hG

theorem orthFacts_minus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthFacts (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D)
      (GaloisField p f) :=
  orthFacts_minusDatum hp2 hm hq

end FactsMinus

end CFSG.ClassicalInvolution.RouteD.Gaps
