module

public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.BHS7.VFacts

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

omit [Finite Γ] in
theorem commutator_vSub_ne_bot (hEG : E ≤ G) (hn : ¬ E ≤ cStarIn G T) :
    ⁅E, vSub G T⁆ ≠ ⊥ := by
  intro h0
  apply hn
  refine le_trans (le_inf hEG ?_) (centralizer_vSub_le_cStarIn G T)
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : ⁅e, v⁆ ∈ (⁅E, vSub G T⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator he hv
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem seven_eight (h : MinCex G T) (hE : IsBTBlock G T E) (hn : ¬ E ≤ cStarIn G T) :
    pCoreOf 2 E = blockW E ∧ ⁅E, vSub G T⁆ = blockW E ∧ pCoreOf 2 E ≤ vSub G T ∧
      pCoreOf 2 E ≤ pCoreOf 2 G := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
  have hEV : E ≤ Subgroup.normalizer (vSub G T : Set Γ) := hE.le.trans (le_normalizer_vSub G T)
  have hne : ⁅E, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hE.le hn
  have hW : ⁅E, vSub G T⁆ = blockW E := commutator_eq_blockW h.charTwo h.sylow hE hVQ hEV hne
  have hWV : blockW E ≤ vSub G T := hW ▸ commutator_le_of_le_normalizer hEV
  have hWE : pCoreOf 2 E = blockW E := (blockW_eq_pCoreOf hE).symm
  have hPV : pCoreOf 2 E ≤ vSub G T := by rw [hWE]; exact hWV
  exact ⟨hWE, hW, hPV, hPV.trans hVQ⟩

end CFSG.CGT.PushingUpLit.BHS7
