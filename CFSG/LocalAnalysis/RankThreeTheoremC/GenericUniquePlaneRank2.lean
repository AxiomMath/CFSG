module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericUniquePlaneRank2 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        ∀ R : Subgroup G, R ≤ P → IsElemAbelian p R → Nat.card R = p ^ 2 → x ∈ R →
          ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → CFSG.Open.pRank p H ≤ 2 → H ≤ M

theorem genericUniquePlane_of_rank2 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hL : GL83GenericLayer G) (h : GL83GenericUniquePlaneRank2 G) : GL83GenericUniquePlane G := by
  intro p hp P M hM hfail hIH x hgen R hRP hRe hRc hxR H hH hRH
  by_cases hrk : CFSG.Open.pRank p H ≤ 2
  · exact h p hp P M hM hfail hIH x hgen R hRP hRe hRc hxR H hH hRH hrk
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨E, hEH, hEe, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨P'', hEP''⟩ := (elementary_isPGroup p E hEe).exists_le_sylow
  obtain ⟨M'', hM'', hP''M'', -, -, -⟩ := exists_isCoreMaxLocal hS hp P''
  have hHM'' : H ≤ M'' := le_of_three_le_pRank_inf hD1 hp hM'' hH
    (le_trans (by omega) (le_pRank_of_elemAbelian_card
      (le_inf hEH (hEP''.trans hP''M'')) hEe hEc))
  have hNR : normalizer (R : Set G) ≤ M'' :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM'' (elementary_isPGroup p R hRe)
      (hRH.trans hHM'') (le_pRank_of_elemAbelian_card le_rfl hRe hRc)
  obtain ⟨h5, hf, m, hm2, ⟨e⟩⟩ := hL p hp P M hM hfail hIH x hgen
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsyl, hrk3⟩ := id hgen
  have hSab : IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    isMulCommutative_of_isSylowOf_mulEquiv_psl h5 hsyl (rankThreeLayer_le _)
      (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
      (fun c hc => mem_centralizer_singleton_iff.mp hc) hrk3.le hm2 e
  have hRS : R ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := fun r hr =>
    ⟨hRP hr, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hRe.1.is_comm.comm ⟨r, hr⟩ ⟨x, hxR⟩))⟩
  have hSR : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ normalizer (R : Set G) := fun s hs =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      congrArg Subtype.val (hSab.is_comm.comm ⟨r, hRS hr⟩ ⟨s, hs⟩))
  obtain ⟨E₃, hE₃S, hE₃e, hE₃c⟩ :=
    pRank_attained p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) (by omega)
  rw [hrk3] at hE₃c
  have hM''M : M'' ≤ M := le_of_three_le_pRank_inf hD1 hp hM hM''.1.1
    (le_pRank_of_elemAbelian_card
      (le_inf (hE₃S.trans (hSR.trans hNR)) (hE₃S.trans (inf_le_left.trans hPM))) hE₃e hE₃c)
  exact hHM''.trans hM''M

end CFSG.LocalAnalysis.RankThreeTheoremC
