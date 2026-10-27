module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmegaE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmegaPairs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmegaTwo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (coe_quadOdd coe_quadPlus coe_quadMinus)

theorem a2l_rowPOmegaOdd_three (hC : HypA2.ChevOddInChev2) {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 4 ≤ n) (hm : LieModel X .POmegaOdd n 3 1) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hK : Nat.card K = 3 := by rw [hcard]; norm_num
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  obtain ⟨S, v, hv0, hv⟩ := a2l_summand_odd (K := K) hn
  have hd := a2lDatum_projElementary_of_summand_three hC hK S hv0 hv
  exact a2lDatum_of_mulEquiv (e.trans (statedProjEquiv (coe_quadOdd n K)
    (commutator_orthogonalGroup_quadOdd h2 (by omega)))).symm hd

theorem a2l_rowPOmegaPlus_three (hC : HypA2.ChevOddInChev2) {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 5 ≤ n) (hm : LieModel X .POmegaPlus n 3 1) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hK : Nat.card K = 3 := by rw [hcard]; norm_num
  obtain ⟨S, v, hv0, hv⟩ := a2l_summand_plus (K := K) hn
  have hd := a2lDatum_projElementary_of_summand_three hC hK S hv0 hv
  exact a2lDatum_of_mulEquiv (e.trans (statedProjEquiv (coe_quadPlus n K)
    (commutator_orthogonalGroup_quadPlus (by omega)))).symm hd

theorem a2l_rowPOmegaMinus_three (hC : HypA2.ChevOddInChev2) {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 5 ≤ n) (hm : LieModel X .POmegaMinus n 3 1) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, b, c, hirr, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hK : Nat.card K = 3 := by rw [hcard]; norm_num
  obtain ⟨S, v, hv0, hv⟩ := a2l_summand_minus (K := K) hn b c
  have hd := a2lDatum_projElementary_of_summand_three hC hK S hv0 hv
  exact a2lDatum_of_mulEquiv (e.trans (statedProjEquiv (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus (by omega) hirr))).symm hd

theorem a2l_rowPOmegaOdd (hC : HypA2.ChevOddInChev2) : a2lRowPOmegaOdd := by
  intro X _ _ n f hn hf hm
  have hf1 : 1 ≤ f := hm.admissible.2.1
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact a2l_rowPOmegaOdd_three hC (by omega) hm
  · exact a2l_rowPOmegaOdd_two hn hge hm

theorem a2l_rowPOmegaPlus (hC : HypA2.ChevOddInChev2) : a2lRowPOmegaPlus := by
  intro X _ _ n f hn hf hm
  have hf1 : 1 ≤ f := hm.admissible.2.1
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact a2l_rowPOmegaPlus_three hC (by omega) hm
  · exact a2l_rowPOmegaPlus_two hn hge hm

theorem a2l_rowPOmegaMinus (hC : HypA2.ChevOddInChev2) : a2lRowPOmegaMinus := by
  intro X _ _ n f hn hf hm
  have hf1 : 1 ≤ f := hm.admissible.2.1
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact a2l_rowPOmegaMinus_three hC (by omega) hm
  · exact a2l_rowPOmegaMinus_two hn hge hm

end CFSG.OddStandard.SmallF3.HypA2Leaves
