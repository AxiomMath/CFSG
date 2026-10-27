module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlueD
public import CFSG.GH74.QTGen4.Recog.Ku.A3V2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem pCore_M_inf_pCore_H [KuLeaf LeafEqKuAOfElemAbelian]
    (h : KuHyp G T M H P z) :
    pCoreOf 2 M ⊓ pCoreOf 2 H = pCoreOf 2 M ⊓ P := by
  have hsub : pCoreOf 2 M ⊓ P ≤ pCoreOf 2 M ⊓ pCoreOf 2 H :=
    inf_le_inf_left _ h.P_le_pCore_H
  have hcle := h.card_pCore_M_inf_pCore_H_le
  have hP8 := h.card_pCore_M_inf_P
  exact (Subgroup.eq_of_le_of_card_ge hsub (by omega)).symm

theorem kuW_inf_pCore_M [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA]
    [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : kuW P H ⊓ pCoreOf 2 M = kuV2 T M := by
  have hV2le : kuV2 T M ≤ kuW P H ⊓ pCoreOf 2 M := fun v hv => ⟨h.kuV2_le_kuW hv, hv.1⟩
  refine le_antisymm ?_ hV2le
  have hWnot : ¬ kuW P H ≤ pCoreOf 2 M := by
    intro hWV
    have hVC : pCoreOf 2 M ≤ T ⊓ Subgroup.centralizer (kuW P H : Set G) := by
      intro v hv
      refine ⟨h.pCore_le_T hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      exact congrArg Subtype.val (h.vElem.1.is_comm.comm ⟨w, hWV hw⟩ ⟨v, hv⟩)
    have hAQ : kuA P H ≤ pCoreOf 2 H := inf_le_left
    exact h.not_pCore_M_le_pCore_H
      (fun v hv => hAQ (h.T_inf_centralizer_kuW_le_kuA (hVC hv)))
  have hcW := h.card_kuW
  have hcV2 := h.card_kuV2
  have hd : Nat.card ↥(kuW P H ⊓ pCoreOf 2 M) ∣ 8 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : kuW P H ⊓ pCoreOf 2 M ≤ kuW P H)
    rwa [hcW] at this
  have hge : 4 ≤ Nat.card ↥(kuW P H ⊓ pCoreOf 2 M) := by
    have := Subgroup.card_le_of_le hV2le
    omega
  have hne : Nat.card ↥(kuW P H ⊓ pCoreOf 2 M) ≠ 8 := by
    intro h8
    apply hWnot
    have hWX : kuW P H ⊓ pCoreOf 2 M = kuW P H :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    calc kuW P H = kuW P H ⊓ pCoreOf 2 M := hWX.symm
      _ ≤ pCoreOf 2 M := inf_le_right
  have hle8 : Nat.card ↥(kuW P H ⊓ pCoreOf 2 M) ≤ 8 := Nat.le_of_dvd (by norm_num) hd
  have key8 : ∀ n < 9, n ∣ 8 → 4 ≤ n → n ≠ 8 → n = 4 := by decide
  have h4 : Nat.card ↥(kuW P H ⊓ pCoreOf 2 M) = 4 :=
    key8 _ (by omega) hd hge hne
  exact (Subgroup.eq_of_le_of_card_ge hV2le (by omega)).symm.le

theorem kuA_le_kuR [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : kuA P H ≤ kuR T M := by
  have hAT : kuA P H ≤ T := fun a ha => h.pCore_H_le_T ha.1
  have hAC : kuA P H ≤ Subgroup.centralizer (kuV2 T M : Set G) := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hvA : v ∈ kuA P H := h.kuW_le_kuA (h.kuV2_le_kuW hv)
    exact congrArg Subtype.val (h.isMulCommutative_kuA.is_comm.comm ⟨v, hvA⟩ ⟨a, ha⟩)
  rw [← h.centralizer_kuV2_T]
  exact le_inf hAT hAC

end KuHyp

end CFSG.GH74.QTGen4.Ku
