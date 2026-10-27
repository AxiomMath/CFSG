module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwo
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3K2Z

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup

theorem kFactP65RankTwoE3_of_kdata (hI713 : GL83.I_7_13_1) (hChevP : KDI278ChevP)
    (hL3 : KDI278L3) (hChevQ : KDI278ChevQ) (hSpor : KDI278Spor) (hSporB : KDI278SporB)
    (hSporC : KDI278SporCNoM) (hI204 : KDL64I204U3) : KFactP65RankTwoE3 := by
  intro A _ _ hNoM p X Q B U hp hp5 hX hrk hQX hQp hQs hZc hBQ hBel hBc hUQ hUel hUc hBU hw
    ⟨Y, hYX, hYne, hΓU, hΓ2⟩ W hWX hBUW hcop
  haveI : Fact p.Prime := ⟨hp⟩
  have hBX : B ≤ X := hBQ.trans hQX
  have hUX : U ≤ X := hUQ.trans hQX
  have hXY : ¬ X ≤ Y := fun h => hYne (le_antisymm hYX h)
  have hOY : rankThreePrimeCore p X ≤ Y :=
    P64Free.rankThreePrimeCore_le_of_gammaOne_plane hp hUX hUel hUc hΓU
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  obtain ⟨Qb, hQb⟩ := P64Asm.XBar.exists_sylow hQ'p hQs
  have hBpl := P64Asm.XBar.plane hp hQX hQp hBQ hBel hBc
  have hUpl := P64Asm.XBar.plane hp hQX hQp hUQ hUel hUc
  have hB'p : IsPGroup p (B.subgroupOf X) := hQ'p.to_le (fun b hb => hBQ hb)
  have hU'p : IsPGroup p (U.subgroupOf X) := hQ'p.to_le (fun u hu => hUQ hu)
  have hZ := P64Asm.two_ZE3 (kdI278Rank1_of_i713 hI713) kdI278Alt_holds hChevP kdI278L2p2_holds hL3
    hChevQ hSpor hSporB hSporC (hNoM X (primeComplementCore (G := ↥X) p)) hI204 hp hp5
    (hX.quotient _) (primeComplementCore_quotient_eq_bot p) Qb
    (P64Asm.XBar.rank_top hp hrk.le)
    (P64Asm.XBar.cyclic_center hp hQX hQp hZc Qb hQb)
    ((B.subgroupOf X).map (P64Asm.XBar.mk p X)) ((U.subgroupOf X).map (P64Asm.XBar.mk p X))
    (by rw [hQb]; exact hBpl.1) hBpl.2.1 hBpl.2.2 (by rw [hQb]; exact hUpl.1) hUpl.2.1 hUpl.2.2
    (P64Asm.XBar.not_conj hp hBX hUX (hQp.to_le hBQ) (hQp.to_le hUQ) hBU)
    (P64Asm.XBar.weak_closed hp hQX hQp hBQ hBel hw Qb hQb)
    ((Y.subgroupOf X).map (P64Asm.XBar.mk p X)) (P64Asm.XBar.not_top_le hOY hXY)
    (fun S hS hk => P64Asm.normalizer_le_map_of_gamma hp (primeComplementCore (G := ↥X) p)
      (P64Asm.XBar.coprime p X) hU'p (k := 1)
      (fun S' hS'U hS'1 => P64Asm.normalizer_subgroupOf_le S' (hΓU _ (by
        rintro _ ⟨s, hs, rfl⟩
        exact hS'U hs) (by rw [pRank_map_subtype hp.one_lt]; exact hS'1))) hS hk)
    (fun S hS hk => P64Asm.XBar.gamma2 hp hQ'p hΓ2 (by rw [← hQb]; exact hS) hk)
  have hBW : B ≤ normalizer (W : Set A) := le_sup_left.trans hBUW
  have hUW : U ≤ normalizer (W : Set A) := le_sup_right.trans hBUW
  exact P64Asm.XBar.le_of_map_eq_bot hWX
    (hZ _ (sup_le (P64Asm.XBar.normalizer_map hBW) (P64Asm.XBar.normalizer_map hUW))
      (P64Asm.XBar.coprime_map hWX hcop))


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
