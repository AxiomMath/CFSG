module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.BProg.B3.S3SD7DichGen
public import CFSG.GH74.Generic.S3.L3Out
public import CFSG.GH74.Generic.S45.LSymFix

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalCores
  CFSG.ClassicalInvolution.Balance Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

namespace S3Sec29I2

variable {G : Type} [Group G] [Finite G]

theorem conjSub_inv_inv {Z : Type*} [Group Z] {s : Z} (hss : s * s = 1) (K : Subgroup Z) :
    conjSub s⁻¹ (conjSub s⁻¹ K) = K := by
  ext x
  rw [mem_conjSub_iff', mem_conjSub_iff', inv_inv]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have : s * (s * x * s⁻¹) * s⁻¹ = x := by
    calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
      _ = x := by rw [hss, hsi, hss]; group
  rw [this]

theorem dichotomy_of_normalizes {y u : G} {Λ M : Subgroup G} (hy : orderOf y = 2)
    (hyu : y ∈ centralizer ({u} : Set G))
    (hΛ : IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({u} : Set G)) Λ)
    (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M) (hyM : y ∈ normalizer (M : Set G)) :
    PumpCalc.bar u Λ ≤ PumpCalc.bar u M ∨ ⁅PumpCalc.bar u Λ, PumpCalc.bar u M⁆ = ⊥ := by
  set Y' := centralizer ({u} : Set G) with hY'
  have hso : orderOf (⟨y, hyu⟩ : ↥Y') = 2 := orderOf_mk_centralizer hyu hy
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ).1 hyu
  have hΛ2 := isTwoComponent_centralizer_mk hΛ hyu
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  have hMc : CFSG.IsComponent (PumpCalc.bar u M) := isComponent_bar hM
  set s : barQ ↥Y' := barMk ↥Y' ⟨y, hyu⟩ with hs
  have hs2 : orderOf s = 2 := orderOf_barMk hso
  have hsinv : s⁻¹ = s := inv_eq_self_of_orderOf_eq_two hs2
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs2, pow_two] at this
  have hMs : conjSub s⁻¹ (PumpCalc.bar u M) = PumpCalc.bar u M := by
    rw [hsinv]
    exact map_conj_bar_of_normalizes hyu hyM
  by_cases hMeq : PumpCalc.bar u M = L ∨ PumpCalc.bar u M = conjSub s⁻¹ L
  · left
    have hLeq : L = PumpCalc.bar u M := by
      rcases hMeq with h | h
      · exact h.symm
      · calc L = conjSub s⁻¹ (conjSub s⁻¹ L) := (conjSub_inv_inv hss L).symm
          _ = conjSub s⁻¹ (PumpCalc.bar u M) := by rw [← h]
          _ = PumpCalc.bar u M := hMs
    rcases hcases with ⟨-, hAL⟩ | ⟨hne, -⟩
    · rw [← hLeq]
      exact hAL
    · exfalso
      apply hne
      rw [hLeq]
      exact hMs
  · right
    push Not at hMeq
    obtain ⟨hne1, hne2⟩ := hMeq
    have hLs : CFSG.IsComponent (conjSub s⁻¹ L) := isComponent_conjSub hL _
    have hc1 : ⁅L, PumpCalc.bar u M⁆ = ⊥ :=
      (distinct_components_commute hL hMc).resolve_left (fun h => hne1 h.symm)
    have hc2 : ⁅conjSub s⁻¹ L, PumpCalc.bar u M⁆ = ⊥ :=
      (distinct_components_commute hLs hMc).resolve_left (fun h => hne2 h.symm)
    have hcc : L ⊔ conjSub s⁻¹ L ≤ Subgroup.centralizer ((PumpCalc.bar u M : Subgroup _) : Set _) :=
      sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc2)
    have hΛL : PumpCalc.bar u Λ ≤ L ⊔ conjSub s⁻¹ L := by
      rcases hcases with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
      · exact hAL.trans le_sup_left
      · refine hAD.trans ?_
        rintro _ ⟨x, rfl⟩
        exact swapDiag_mem_sup hAB x
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hΛL.trans hcc)

end S3Sec29I2

end CFSG.GH74.Generic.BProg.B3
