module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G]

theorem pRank_pPrimeCore_le_pRank_relPPrimeCore {p : ℕ} (hp : p.Prime) {H L : Subgroup G}
    (hLH : L ≤ H) (hLs : (L.subgroupOf H).IsSubnormal) {r : ℕ} (hr : r.Prime) :
    CFSG.Open.pRank r (CFSG.pPrimeCore p ↥L) ≤
      CFSG.Open.pRank r (CFSG.Open.relPPrimeCore p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  let O' : Subgroup G := O.map L.subtype
  have hO'H : O' ≤ H := (Subgroup.map_subtype_le O).trans hLH
  have hO'L : O'.subgroupOf L = O := by
    show Subgroup.comap L.subtype (Subgroup.map L.subtype O) = O
    rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hO'sn : (O'.subgroupOf L).IsSubnormal := by
    rw [hO'L]
    exact CFSG.pPrimeCore_normal.isSubnormal
  have hO'Hsn : (O'.subgroupOf H).IsSubnormal :=
    CFSG.Walter.isSubnormal_subgroupOf_trans (Subgroup.map_subtype_le O) hO'sn hLs
  have hcop : Nat.Coprime p (Nat.card (O'.subgroupOf H)) := by
    have h1 : Nat.card (O'.subgroupOf H) = Nat.card O' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'H).toEquiv
    have h2 : Nat.card O' = Nat.card O := Subgroup.card_map_of_injective L.subtype_injective
    rw [h1, h2]
    exact CFSG.pPrimeCore_coprime_card
  have hle : O'.subgroupOf H ≤ CFSG.pPrimeCore p ↥H :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hO'Hsn hcop
  have hO'le : O' ≤ CFSG.Open.relPPrimeCore p H := by
    rw [relPPrimeCore_eq_map hp H, ← Subgroup.map_subgroupOf_eq_of_le hO'H]
    exact Subgroup.map_mono hle
  calc CFSG.Open.pRank r (CFSG.pPrimeCore p ↥L) = CFSG.Open.pRank r O := rfl
    _ ≤ CFSG.Open.pRank r O' :=
        CFSG.SectionRank.pRank_le_map hr.one_lt L.subtype L.subtype_injective O
    _ ≤ CFSG.Open.pRank r (CFSG.Open.relPPrimeCore p H) :=
        CFSG.SectionRank.pRank_mono hr.one_lt hO'le

namespace NineSettingGen

variable {M Q H E : Subgroup G} {p k : ℕ}

theorem pRank_relPPrimeCore_le_three (h : NineSettingGen G M p Q H E k) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (CFSG.Open.relPPrimeCore p H) ≤ 3 := by
  by_cases hrp : r = p
  · subst r
    have hcop : Nat.Coprime p (Nat.card (CFSG.Open.relPPrimeCore p H)) :=
      coprime_card_relPPrimeCore h.prime H
    have hnd : ¬ p ∣ Nat.card (CFSG.Open.relPPrimeCore p H) :=
      (h.prime.coprime_iff_not_dvd).mp hcop
    rw [CFSG.LocalAnalysis.GLTheoremA.pRank_eq_zero_of_not_dvd_card h.prime hnd]
    omega
  · by_cases hsig : r ∈ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M
    · by_contra h3
      have h2 : 2 ≤ CFSG.Open.pRank r (CFSG.Open.relPPrimeCore p H) := by omega
      haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨T, hT⟩ :=
        CFSG.ABGLocalTools.exists_isSylowOf (p := r) (CFSG.Open.relPPrimeCore p H)
      have hTM : T ≤ M := hT.le.trans h.relPPrimeCore_le
      have hTr : CFSG.Open.pRank r T = CFSG.Open.pRank r (CFSG.Open.relPPrimeCore p H) :=
        CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow hr hT
      have hT2 : 2 ≤ CFSG.Open.pRank r T := by rw [hTr]; exact h2
      have hnorm : Subgroup.normalizer (T : Set G) ≤ M :=
        h.setting.normalizer_le_of_two_le_pRank hsig hTM hT2
      have hNHle : CFSG.Open.relPPrimeCore p H ≤ H :=
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
      have hNH : H ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore p H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNHle).mp
          (relPPrimeCore_normal h.prime H)
      have hfr :=
        CFSG.RankThree.PartTwo.Sec18.le_sup_normalizer_of_isSylowOf (p := r) hT hNH
      exact h.not_le (hfr.trans (sup_le h.relPPrimeCore_le hnorm))
    · have hrs : r ∉ CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet G M := by
        simpa [CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM,
          CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet] using hsig
      calc CFSG.Open.pRank r (CFSG.Open.relPPrimeCore p H)
          ≤ CFSG.Open.pRank r M := CFSG.SectionRank.pRank_mono hr.one_lt h.relPPrimeCore_le
        _ ≤ 3 :=
            h.setting.cstar.pRank_le_three_of_not_mem_sigmaSet h.setting.maxLocal hr hr2 hrs

theorem pRank_pPrimeCore_le_three (h : NineSettingGen G M p Q H E k) {L : Subgroup G}
    (hLH : L ≤ H) (hLs : (L.subgroupOf H).IsSubnormal) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (CFSG.pPrimeCore p ↥L) ≤ 3 :=
  (pRank_pPrimeCore_le_pRank_relPPrimeCore h.prime hLH hLs hr).trans
    (h.pRank_relPPrimeCore_le_three hr hr2)

theorem isKGroup_of_le (h : NineSettingGen G M p Q H E k) {L : Subgroup G} (hLH : L ≤ H) :
    CFSG.Open.IsKGroup ↥L :=
  (h.setting.cstar.toStandingGen.kProper.isKGroup H h.ne_top).of_le hLH

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
