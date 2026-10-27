module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Close
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Odd
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6ResidueU
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.McLaughlin
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem d2PairA6Residue3U_of_inputs {G : Type} [Group G] [Finite G]
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hAut : KFactStrongThreeAutomizer) (hLie : PairOneImageLieTR3 G) (hType : PairBlockType3 G)
    (hIrr : KFactBlockOneImageIrr3) : D2PairA6Residue3U G := by
  intro hS hD1 M hM ha hb P A H R hp hMP hesc hpr hstr hperf hRel hR9 hirr htrans L hL hk1
    hr3 hRL hker
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hctx : PairCtx3 P M A H R := ⟨hS, hD1, hM, ha, hb, hp, hMP, hesc, hpr, hstr, hperf⟩
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX hS
  have hev : 2 ∣ (H ⊓ M).relIndex H := by
    by_contra hodd
    exact htrans (hctx.transitive_of_oddIndex hAut hodd).2.2
  have hH : Open.pRank 3 H = 2 := hesc.pRank_H
  have hthree : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' := fun L' hL' =>
    hpr.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL'
  have hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    intro hZ
    set Bb := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) with hBb
    set Lb := barM M L with hLb
    set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
    have hBH : Open.pRank 3 Bb ≤ 2 := (hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
    have hRB : barM M R ≤ Bb := barM_mono fun r hr => by
      rw [hpr.normalizer_twoCore_H]
      exact hpr.le_H hr
    have hCB : Cb ≤ Bb := fun c hc =>
      hpr.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hNX fun L' hL' =>
        (hk1 L' hL').symm ▸ hc
    have hR2 : 2 ≤ Open.pRank 3 R :=
      le_pRank_of_isElemAbelian h3 hRel (by rw [hR9]; norm_num : Nat.card R = 3 ^ 2)
    have hRbar2 : 2 ≤ Open.pRank 3 (barM M R) := by
      rw [pRank_barM_eq h3 (by decide) M R hpr.le_M]
      exact hR2
    obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' 3 hZ
    rw [Subgroup.orderOf_mk] at hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hzB : z ∈ Bb := hCB hzZ.2
    have hLCz : Lb ⊔ Cb ≤ Subgroup.centralizer ({z} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      refine sup_le (fun l hl => ?_) (fun c hc => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hzZ.2 l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hc z hzZ.1).symm
    have hzR : z ∈ Subgroup.centralizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLCz (hRL hx))
    have hzR' : z ∉ barM M R := fun hzR'' => hz1 (by
      have : z ∈ barM M R ⊓ Cb := ⟨hzR'', hzZ.2⟩
      rw [hker, Subgroup.mem_bot] at this
      exact this)
    have hsucc := succ_pRank_le_of_commute (q := 3) hRB le_rfl hzB hz3 hzR' hzR
    omega
  have hy := exists_order_three_noncentral hL.le (hthree L hL) hZ
  have h2 : NineThreeTwo M (pCoreOf 2 H) L := hType P M A H R hctx L hL hr3 hZ
  exact false_of_oneImage_list3 hLie hIrr hctx hev hRel hR9 hirr hL hk1 h2 hr3 hZ hy

end CFSG.LocalAnalysis.RankThreeTheoremC
