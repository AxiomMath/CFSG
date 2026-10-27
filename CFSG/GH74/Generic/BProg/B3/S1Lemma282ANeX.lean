module

public import CFSG.GH74.Generic.BProg.B3.S1Lemma282Bal
public import CFSG.GH74.Generic.BProg.B3.LocBalSL4
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section ANeX


variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_a_ne_x (hc : Ctx21 G x K A a D J) (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) : a ≠ x := by
  classical
  intro hax
  obtain ⟨-, hAK, -, -⟩ := s1_basic hc h1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hAe : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hA8 : Nat.card ↥A = 8 := hc.src.2.2.1
  obtain ⟨hDA, hDel, hDrk⟩ := hc.obs.D_le
  have hLoc : S1Lemma282Bal.LocBalAll (↥K ⧸ pPrimeCore 2 ↥K) :=
    fun hAe' hA8' B hB => locBal32_SL4 h1 hAe' hA8' B hB
  subst hax
  rcases FalseCtxS45Comp.pCompIn_eq_or_commute hc.obs.comp hK with hJK | hcomm
  · subst hJK
    have hAN : A ≤ normalizer (J : Set G) := fun g hg => Subgroup.le_normalizer (hAK hg)
    rcases hc.obs_cases with h2 | ⟨h1', -⟩ | ⟨-, e', he'A, he'N, -⟩
    · exact hc.obs.not_locBal32_rank2 h2 (S1Lemma282Bal.locBal32_bar hK hAK hAe hA8 hDA hLoc)
    · exact hc.obs.not_locBal32_rank1 h1' hAN
        (S1Lemma282Bal.locBal32_bar hK hAK hAe hA8 le_rfl hLoc)
    · exact he'N (hAN he'A)
  · obtain ⟨d, hdD, hd1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) hDrk
      (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
    have hdA : d ∈ A := hDA hdD
    have hdK : d ∈ K := hAK hdA
    have hdY : d ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc.obs.y_cent d hdA)
    refine hc.obs.D_faith d hdD hd1 (ObsPump.mem_cSec_of_bar_comm hc.obs.comp hdY fun l hl => ?_)
    have hqb : TwoThin.barMk ↥(centralizer ({a} : Set G)) ⟨d, hdY⟩ ∈ PumpCalc.bar a K :=
      ⟨⟨d, hdY⟩, Subgroup.mem_subgroupOf.mpr hdK, rfl⟩
    have hl' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hl
    exact Subgroup.mem_centralizer_iff.mp hl' _ hqb

end ANeX

end CFSG.GH74.Generic.BProg.B3
