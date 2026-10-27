module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeOmTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega Module

namespace I294Large

theorem four_le_pRank_of_commOrRank {r : ℕ} (h5 : 5 ≤ r) {G : Type} [Group G] [Finite G]
    (h : CommOrRank r G) (hS : ∃ S : Sylow r G, ¬ IsMulCommutative (S : Subgroup G)) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  rcases h with hc | hrk
  · obtain ⟨S, hS⟩ := hS
    exact (hS (hc S)).elim
  · omega

end I294Large

theorem i294LargeModelPOmegaOdd_holds : I294LargeModelPOmegaOdd := by
  intro r hr h5 K _ _ hrK hodd n hn hS
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hp2 : r ≠ 2 := by omega
  have hpq : ¬ r ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hodd' : Odd (Fintype.card K) := by rwa [← Nat.card_eq_fintype_card]
  have h2 : ringChar K ≠ 2 := fun h => by
    have := FiniteField.even_card_of_char_two h
    rw [Nat.odd_iff] at hodd'
    omega
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := n)
    (Ring.two_ne_zero h2) hn
  have hdim : finrank K (Fin n ⊕ Fin n ⊕ Unit → K) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_odd hp2 hodd' hpq hdim hQnd
  exact I294Large.four_le_pRank_of_commOrRank h5
    (I294Large.CommOrRank.of_projOmega (CFSG.LieType.Universal.Spin.coe_quadOdd n K) hQnd hT hr hp2
      (I294Large.CommOrRank.of_sylow_sigmaModel hr (one_le_weirA hpq) hN)) hS

theorem i294LargeModelPOmegaPlus_holds : I294LargeModelPOmegaPlus := by
  intro r hr h5 K _ _ hrK n hn hS
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hp2 : r ≠ 2 := by omega
  have hpq : ¬ r ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
    (by omega)
  have hdim : finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_quadPlus_space n
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even hp2 hpq (by omega) hdim hQnd
    (ε := 1) (Or.inl ⟨rfl, isPlusType_quadPlus K n⟩)
  exact I294Large.four_le_pRank_of_commOrRank h5
    (I294Large.CommOrRank.of_projOmega (CFSG.LieType.Universal.Spin.coe_quadPlus n K) hQnd hT hr
      hp2 (I294Large.CommOrRank.of_sylow_sigmaModel hr (one_le_weirA hpq) hN)) hS

theorem i294LargeModelPOmegaMinus_holds : I294LargeModelPOmegaMinus := by
  intro r hr h5 K _ _ hrK n hn b c hirr hS
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hp2 : r ≠ 2 := by omega
  have hpq : ¬ r ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) hn
    hirr
  have hdim : finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * n :=
    finrank_quadMinus_space (by omega)
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even hp2 hpq (by omega) hdim hQnd
    (ε := -1) (Or.inr ⟨rfl, isMinusType_quadMinus (by omega) hirr⟩)
  exact I294Large.four_le_pRank_of_commOrRank h5
    (I294Large.CommOrRank.of_projOmega (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c) hQnd hT
      hr hp2 (I294Large.CommOrRank.of_sylow_sigmaModel hr (one_le_weirA hpq) hN)) hS

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
