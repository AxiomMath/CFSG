module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3EndHyp
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41Aux
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
  CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem eg41_endgame_hyp {p : ℕ} [Fact p.Prime] (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : p ∈ rankThreeSigmaA G) (hp2 : p ≠ 2)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} {U H F : Subgroup G} (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hx1 : x ≠ 1)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hHtop : H ≠ ⊤) (hUH : U ≤ H) (hrk : Open.pRank p H ≤ 2) (hFH : IsSylowOf p F H)
    (hUF : U ≤ F) (hFM : F ≤ M) (hFab : IsMulCommutative F)
    (hwcF : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    Gen49BHyp p ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      ((U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hUH hxU⟩) := by
  have hprime : p.Prime := Fact.out
  have hxH : x ∈ H := hUH hxU
  set O : Subgroup H := primeComplementCore (G := H) p with hO
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hUp : IsPGroup p U := elementary_isPGroup p U hU
  have hxp : x ^ p = 1 := hU.2 x hxU
  have hxo : orderOf (⟨x, hxH⟩ : H) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = p :=
    orderOf_mk_of_coprime hprime O (primeComplementCore_coprime p) hxo
  have hFb : IsMulCommutative ((F.subgroupOf H).map (QuotientGroup.mk' O)) := by
    have h1 : IsMulCommutative (F.subgroupOf H) :=
      Subgroup.comap_injective_isMulCommutative (H := F) H.subtype_injective
    infer_instance
  have hF2 : 2 ≤ Open.pRank p F := le_pRank_of_elemAbelian_card hUF hU hUc
  have hN₁ : normalizer (F : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hFH.isPGroup hFM hF2
  have hN₂ : normalizer (U : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hUp (hUP.trans hPM)
      (le_pRank_of_elemAbelian_card le_rfl hU hUc)
  exact
    { ne_two := hp2
      core_eq_bot := primeComplementCore_quotient_eq_bot p
      catalog := (catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hFH
      abelian := hFb
      le_sylow := Subgroup.map_mono (Subgroup.subgroupOf_mono H hUF)
      elemAbelian := gen49q_isElemAbelian_map _ (isElemAbelian_subgroupOf hU H)
      card_eq := by
        rw [card_map_mk_of_isPGroup hprime O (primeComplementCore_coprime p)
          (show IsPGroup p (U.subgroupOf H) from hUp.comap_subtype),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
        exact hUc
      pRank_le := gen49q_pRank_top_quotient_le hprime hrk
      mem := ⟨⟨x, hxH⟩, hxU, rfl⟩
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo'
        exact hprime.one_lt.ne hxo'
      weakClosed := fun g hg => u3end_weaklyClosed_map_mk hFH (hUF hxU) hxo hFb hwcF g hg
      normalizer_S := normalizer_map_mk_le3 hprime
        (show IsPGroup p (F.subgroupOf H) from hFH.isPGroup.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hFH.le]; exact hN₁)
      normalizer_R := normalizer_map_mk_le3 hprime
        (show IsPGroup p (U.subgroupOf H) from hUp.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hUH]; exact hN₂)
      others := by
        rintro _ ⟨r, hr, rfl⟩ hr1 hrx
        have hrU : (r : G) ∈ U := hr
        have hr1' : (r : G) ≠ 1 := fun h => hr1 (by rw [show r = 1 from Subtype.ext h, map_one])
        have hrp : (r : G) ^ p = 1 := hU.2 _ hrU
        have hrx' : (r : G) ∉ zpowers x := by
          intro hmem
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
          have hrk' : r = (⟨x, hxH⟩ : H) ^ k := Subtype.ext (by rw [← hk]; rfl)
          have hmem' : QuotientGroup.mk' O r ∈ zpowers (QuotientGroup.mk' O ⟨x, hxH⟩) := by
            rw [hrk', map_zpow]
            exact zpow_mem (mem_zpowers _) k
          exact hrx (eg41_zpowers_eq_of_mem hprime hxo' hmem' hr1)
        have hCM : centralizer ({(r : G)} : Set G) ≤ M := hC _ hrU hrx'
        have hUC : U ≤ centralizer ({(r : G)} : Set G) := fun g hg =>
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            (hU.1.is_comm.comm ⟨g, hg⟩ ⟨r, hrU⟩))
        have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
          normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM
            (le_pRank_of_elemAbelian_card (le_inf hUP hUC) hU hUc) hCM
        have hro : orderOf r = p := by
          rw [← Subgroup.orderOf_coe]
          exact orderOf_eq_prime hrp hr1'
        refine ⟨(centralizer_mk_le_map hprime hro).trans (Subgroup.map_mono fun c hc => ?_), ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hCM (mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))⟩
        · rw [← MonoidHom.map_zpowers]
          refine normalizer_map_mk_le3 hprime (D := zpowers r)
            (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hro, pow_one])) ?_
          rw [MonoidHom.map_zpowers]
          exact hNM }

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
