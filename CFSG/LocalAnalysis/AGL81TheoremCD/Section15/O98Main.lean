module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

import CFSG.LocalAnalysis.GLTheoremB.BarXTools
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Red
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Normalize
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Shape
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure
public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

private theorem quotEquivBarX_mk {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C L : Subgroup G} (hLC : L ≤ C) (hsn : IsSubnormal L C) (x : ↥L) :
    CFSG.LocalAnalysis.GLTheoremB.quotEquivBarX hp hLC hsn (QuotientGroup.mk x) =
      CFSG.LocalAnalysis.GLTheoremB.barMap p hLC x := by
  simp [CFSG.LocalAnalysis.GLTheoremB.quotEquivBarX,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem quotientMulEquivOfEq_trans_quotEquivBarX_mk {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C) (hsn : IsSubnormal L C)
    (x : ↥L) :
    ((QuotientGroup.quotientMulEquivOfEq
        (show CFSG.pPrimeCore p ↥L = CFSG.Open.GLAPPrimeCore p ↥L from rfl)).trans
      (CFSG.LocalAnalysis.GLTheoremB.quotEquivBarX hp hLC hsn))
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥L) x) =
      CFSG.LocalAnalysis.GLTheoremB.barMap p hLC x := by
  rw [MulEquiv.trans_apply]
  have h1 : QuotientGroup.quotientMulEquivOfEq
      (show CFSG.pPrimeCore p ↥L = CFSG.Open.GLAPPrimeCore p ↥L from rfl)
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥L) x) =
      QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore p ↥L) x := by
    simp [QuotientGroup.quotientMulEquivOfEq_mk]
  rw [h1]
  exact quotEquivBarX_mk hp hLC hsn x

private theorem card_barMeet_dvd_card_inf {G : Type} [Group G] [Finite G]
    {H K M : Subgroup G} (hK : IsPComponentIn 3 K H) :
    Nat.card ↥(S15.barMeet K M) ∣
      Nat.card ↥(starImg 3 H K ⊓ starImg 3 H M) := by
  rcases hK.2 with ⟨K', hKcomp, hsn, hKmap, hKmin⟩
  have hsn' : IsSubnormal K H := (CFSG.Open.IsSubnormal.iff_subgroupOf hK.1).2 hsn
  let e := (QuotientGroup.quotientMulEquivOfEq
    (show CFSG.pPrimeCore 3 ↥K = CFSG.Open.GLAPPrimeCore 3 ↥K from rfl)).trans
    (CFSG.LocalAnalysis.GLTheoremB.quotEquivBarX Nat.prime_three hK.1 hsn')
  let eH : (↥K ⧸ CFSG.pPrimeCore 3 ↥K) →* StarGroup 3 H :=
    (CFSG.LocalAnalysis.GLTheoremB.barX 3 H K).subtype.comp e.toMonoidHom
  have heH_inj : Function.Injective eH := by
    intro a b hab
    apply e.injective
    exact Subtype.ext hab
  have hle : (S15.barMeet K M).map eH ≤ starImg 3 H K ⊓ starImg 3 H M := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hb
    have hcKM : (c : G) ∈ K ⊓ M := Subgroup.mem_subgroupOf.mp hc
    have heq : eH ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) c) =
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
          (Subgroup.inclusion hK.1 c) := by
      change (CFSG.LocalAnalysis.GLTheoremB.barX 3 H K).subtype
        (e ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) c)) = _
      rw [quotientMulEquivOfEq_trans_quotEquivBarX_mk Nat.prime_three hK.1 hsn' c]
      rfl
    rw [heq]
    constructor
    · exact Subgroup.mem_map.mpr ⟨⟨(c : G), hK.1 c.2⟩, c.2, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨⟨(c : G), hK.1 c.2⟩, hcKM.2, rfl⟩
  have hcard : Nat.card ↥(S15.barMeet K M) =
      Nat.card ↥((S15.barMeet K M).map eH) :=
    (Subgroup.card_map_of_injective heH_inj).symm
  rw [hcard]
  exact Subgroup.card_dvd_of_le hle

private theorem isL34Type_quot_of_starImg {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hK : IsPComponentIn 3 K H)
    (hL34 : IsL34Type ↥(starImg 3 H K)) :
    IsL34Type (↥K ⧸ CFSG.pPrimeCore 3 ↥K) := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hK
  exact IsL34Type.of_mulEquiv e.symm hL34

theorem threeFourShape_of_starImg {G : Type} [Group G] [Finite G] {M H K : Subgroup G}
    (hK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPComponentIn 3 K H)
    (hL34 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type
      ↥(CFSG.LocalAnalysis.RankThreeUC.AGL81C.starImg 3 H K))
    (h23 : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥(CFSG.LocalAnalysis.RankThreeUC.AGL81C.starImg 3 H K ⊓
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.starImg 3 H M) → r = 2 ∨ r = 3) :
    CFSG.LocalAnalysis.RankThreeUC.S15.ThreeFourShape K M := by
  refine Or.inl ⟨isL34Type_quot_of_starImg hK hL34, ?_⟩
  intro r hr hdvd
  exact h23 r hr (hdvd.trans (card_barMeet_dvd_card_inf hK))

private theorem seven_mem_normalizer {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {E Y S : Subgroup (StarGroup 3 H)} {z : StarGroup 3 H}
    (h : O98Red (StarGroup 3 H) E Y S z) {L : Subgroup G}
    (hL : IsPComponentIn 3 L H) (hL34 : IsL34Type ↥(starImg 3 H L))
    {y : G} (hy : y ∈ H) (hy7 : y ^ 7 = 1) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  let ybar : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨y, hy⟩
  have hybar7 : ybar ^ 7 = 1 := by
    have hyH : (⟨y, hy⟩ : ↥H) ^ 7 = 1 := Subtype.ext (by simpa using hy7)
    rw [← map_pow, hyH, map_one]
  have hcomp : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL
  have hyN : ybar ∈ Subgroup.normalizer (starImg 3 H L : Set (StarGroup 3 H)) :=
    O98Red.seven h hcomp hL34 ybar hybar7
  have hmap : (starImg 3 H L).map (MulAut.conj ybar).toMonoidHom = starImg 3 H L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
  have hstar : starImg 3 H (L.map (MulAut.conj y).toMonoidHom) = starImg 3 H L := by
    calc starImg 3 H (L.map (MulAut.conj y).toMonoidHom)
        = (starImg 3 H L).map (MulAut.conj ybar).toMonoidHom := by
          simpa [ybar] using starImg_map_conj 3 H L ⟨y, hy⟩
      _ = starImg 3 H L := hmap
  have hconj : IsPComponentIn 3 (L.map (MulAut.conj y).toMonoidHom) H :=
    isPComponentIn_conj hL hy
  have hEq : L.map (MulAut.conj y).toMonoidHom = L :=
    eq_of_starImg_eq Nat.prime_three hconj hL hstar
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

theorem o98Gen_of_inputs (hK35 : KFactThreeFiveInner)
    (hK37 : KFactThreeSevenTwoThree) : O98Gen := by
  intro G _ _ hC M hM hσ hstrong
  intro h3 Q hQM hQ hQc hΓ x _ hx hxQ hHM hO2 hO2M
  let H : Subgroup G := Subgroup.centralizer ({x} : Set G)
  obtain ⟨E, L, z, hred, hnine, hLc, hLM, hSL⟩ :=
    o98_red hC hM hσ h3 hQM hQ hQc hΓ hx hxQ (H := H) rfl hHM hO2 hO2M
  let Lstar : Subgroup (StarGroup 3 H) := starImg 3 H L
  have hLcomp : CFSG.IsComponent Lstar := isComponent_starImg hLc
  have hLstarM : ¬ Lstar ≤ starImg 3 H M :=
    fun h => hLM ((hnine.toCore.le_iff_starImg_le hLc.1).mpr h)
  have hE : starImg 3 H E ≤ Subgroup.normalizer (Lstar : Set (StarGroup 3 H)) :=
    O98Red.le_normalizer_E hred hLcomp hLstarM
  have hS : starImg 3 H (pCoreOf 2 (H ⊓ M)) ≤
      Subgroup.normalizer (Lstar : Set (StarGroup 3 H)) :=
    O98Red.le_normalizer_S hK35 hred hLcomp hLstarM
  obtain ⟨hL34, h23⟩ := O98Red.shape hK37 hred hLcomp hLstarM hSL hE hS
  refine ⟨L, hLc.1, hLc.2, hLM, threeFourShape_of_starImg hLc hL34 h23, ?_⟩
  intro y hy hyord
  have hy7 : y ^ 7 = 1 := by simpa [hyord] using pow_orderOf_eq_one y
  exact seven_mem_normalizer hred hLc (by simpa [Lstar] using hL34) hy.1 hy7

theorem o98_of_inputs (hK35 : KFactThreeFiveInner) (hK37 : KFactThreeSevenTwoThree) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O98 :=
  o98_of_gen (o98Gen_of_inputs hK35 hK37)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
