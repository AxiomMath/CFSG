module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8B
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf14Ab8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem twinLab8_core (hF7 : F7Cent K₀ π g) (J : AEIdent (fam K (conjSub g (piGen π))) 8)
    {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b) := by
  classical
  have hn : 5 ≤ 8 := by norm_num
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  have hPΩ : fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ :=
    fun L hL => S.fam_mem hL
  obtain ⟨γ, hγ, c, hlab'⟩ := J.label K' S.twin_mem_fam
  obtain ⟨-, z', hz'K, hz'K'⟩ := S.hK'
  have hzz : z' = z := (S.hz.eq hz'K).symm
  rw [hzz] at hz'K'
  have e1 := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
  have e2 := J.map_eq_zBar hn S.twin_mem_fam (S.card8 K' S.hK'.1) hlab' hz'K'
  rcases TwinThinPf17Lab8.eq_or_compl_of_zBar_eq (e2.symm.trans e1) with rfl | hγc
  ·
    by_cases hcb : c = !b
    · subst hcb
      exact hlab'
    · exfalso
      have hcb' : c = b := by cases b <;> cases c <;> simp_all
      subst hcb'
      exact S.hne (S.eq_of_map_le hn J S.twin_mem_fam S.mem_fam_self
        (le_of_eq (hlab'.trans hlab.symm)))
  ·
    exfalso
    subst hγc
    obtain ⟨M, hMF, hlabM⟩ := J.label_surj α h (!b)
    have hMne : M ≠ K := by
      intro e
      rw [e] at hlabM
      have := hlab.symm.trans hlabM
      cases b
      · exact AE.memBar_true_ne_false hn α h this.symm
      · exact AE.memBar_true_ne_false hn α h this
    have hcommKM : ∀ x ∈ K, ∀ y ∈ M, x * y = y * x :=
      S.commutes_of_map_comm_gen hPΩ J hk S.mem_fam_self hMF (Ne.symm hMne) (by
        rw [hlab, hlabM]
        cases b
        · exact fun x hx y hy => (comm_memBar_twin α h y hy x hx).symm
        · exact comm_memBar_twin α h)
    have hadj : nbrAdj (CoreAssembly.conjClass K₀) K M :=
      S.nbrAdj_of_comm S.hK (S.fam_mem hMF) hMne hcommKM
    by_cases hMπ : M ∈ π
    · exact S.lab8_false_of_caseB J hlab hMF hMπ hlabM hγ disjoint_compl_left hlab'
    · exact S.lab8_false_of_caseA hF7 J hlab hMF (S.hos.nbr_diff_subset_beta S.hπ hadj hMπ) hlabM
        hγ disjoint_compl_left hlab'

theorem twinLab8_of_f7 (_hS : IsSimpleGroup ↥(genFittingFStar G))
    (_hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (_hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ u : G, IsUniqueInvolution L u →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥)
    (hF7 : F7Cent K₀ π g) : S.TwinLab 8 :=
  fun J _ _ _ hlab => S.twinLab8_core hF7 J hlab

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

