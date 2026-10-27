module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.RankOneK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltCaseK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.SLG2K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairOmegaPlus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairOmegaMinus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PRankSurvivor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetFF
public import CFSG.Quasithin.Background.FFC11C
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace B69K

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def AsSQTKOddCovers : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    Odd (Nat.card ↥(Subgroup.center L)) → 1 < Nat.card ↥(Subgroup.center L) →
      Survivor (L ⧸ Subgroup.center L) → CFSG.Open.SQTKTauCeti.StronglyQuasithin L

@[expose] def AsAltEven : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K T M : Subgroup Y), E2P.ASHyp K T M →
    ∀ m : ℕ, 10 ≤ m → Even m → ¬ Nonempty (↥K ≃* alternatingGroup (Fin m))

@[expose] def AsAltSlice : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), B69.CompHypK X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ j : ℕ, 3 ≤ j → IsAlt (2 ^ j + 1) (↥L ⧸ Subgroup.center ↥L) → B69.AltShape M A L W

theorem odd_card_center_comp {X L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥)
    (hL : CFSG.Open.IsComponentOf L X) : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have h1 := B69.odd_orderOf_of_mem_center_comp hO2 hL z.2
  have h2 : orderOf (z : ↥L) = 2 := by rw [Subgroup.orderOf_coe, hz]
  rw [h2] at h1
  exact absurd h1 (by decide)

theorem stronglyQuasithin_of_survivor (hCov : AsSQTKOddCovers) {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hodd : Odd (Nat.card ↥(Subgroup.center L)))
    (hS : Survivor (L ⧸ Subgroup.center L)) : CFSG.Open.SQTKTauCeti.StronglyQuasithin L := by
  rcases Nat.lt_or_ge 1 (Nat.card ↥(Subgroup.center L)) with h | h
  · exact hCov L hL hodd h hS
  · have h1 : Nat.card ↥(Subgroup.center L) = 1 := le_antisymm h Nat.card_pos
    have hbot : Subgroup.center L = ⊥ := (Subgroup.card_eq_one).1 h1
    have hbij : Function.Bijective (QuotientGroup.mk' (Subgroup.center L)) := by
      refine ⟨?_, QuotientGroup.mk'_surjective _⟩
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
    let e : L ≃* L ⧸ Subgroup.center L := MulEquiv.ofBijective _ hbij
    intro p hp hp2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_le_two_of_survivor hS hp hp2

theorem not_alt_even (hEven : AsAltEven) {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) {m : ℕ} (hm : 10 ≤ m) (hev : Even m) :
    ¬ IsAlt m (↥L ⧸ Subgroup.center ↥L) := by
  rintro ⟨e₀⟩
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e'⟩⟩ := asHyp_of_compHypK hH
  exact hEven Y K T' M' hAS m hm hev ⟨e'.symm.trans e₀⟩

theorem false_of_highRank {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L)
    (h : HighRankModel (↥L ⧸ Subgroup.center ↥L)) : False := by
  rcases h with ⟨n, f, hn, hmc⟩ | ⟨n, f, hn, hmc⟩ | ⟨r, f, hr, hmc⟩ | ⟨n, f, hn, hmc⟩ | ⟨n, f, hn, hmc⟩
  · obtain ⟨U, hU, hP⟩ := pairData_of_statedPSL hn hmc
    exact false_of_parabolicPair hH (MulEquiv.refl _) hU hP
  · obtain ⟨U, hU, hP⟩ := pairData_of_statedPSU hn hmc
    exact false_of_parabolicPair hH (MulEquiv.refl _) hU hP
  · obtain ⟨U, hU, hP⟩ := pairData_of_statedPSp hr hmc
    exact false_of_parabolicPair hH (MulEquiv.refl _) hU hP
  · obtain ⟨U, hU, hP⟩ := pairData_of_statedPOmegaPlus hn hmc
    exact false_of_parabolicPair hH (MulEquiv.refl _) hU hP
  · obtain ⟨U, hU, hP⟩ := pairData_of_statedPOmegaMinus hn hmc
    exact false_of_parabolicPair hH (MulEquiv.refl _) hU hP

section Chain


theorem chainK (hB42 : AsB42) (hA21 : AsA21SQTKSection) (hAlt : E2P.E22AltFam)
    (hLn : E2P.E22LnTwoFam) (hExc : E2P.E22Char2ExcFam) (hF : E2P.E22Families) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), B69.CompHypK X T M A L → SQTKGroup ↥L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → B69.CompShape T M A L W := by
  intro V _ _ hV X T M A L hH hSQL W hW
  obtain ⟨B, hBA, hBoff, hconcl⟩ := sectionB42K_of hB42 hA21 hV hH hSQL hW
  have hO2 : pCoreOf 2 X = ⊥ := hH.2.2.1
  have hL : CFSG.Open.IsComponentOf L X := hH.2.2.2.2.2.2.1
  rcases hconcl with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · have hnat := B69.binaryNaturalSL_of_case1 B69.asB69NoOddCoverSL2 hO2 hL hW c1.2.1
    exact Or.inl ⟨hnat, asB69RankOneSylowK V hV X T M A L hH W hW hnat,
      asB69RankOneBorelK V hV X T M A L hH W hW hnat⟩
  · exact (noRankTwoSL3K_of hV hH hW c2).elim
  · exact (noRankTwoSp4K V hV X T M A L hH W hW c3).elim
  · exact (noG2K hExc hF V hV X T M A L hH W hW B hBA hBoff c4).elim
  · exact Or.inr (asB69AltCaseK hAlt hA21 V hV X T M A L hH hSQL W hW B hBA hBoff c5)
  · exact (noRankTwoA6K V hV X T M A L hH W hW B hBA hBoff c6).elim
  · exact (noA7K hAlt hH hW c7).elim
  · exact (noRankTwoTripleA6K V hV X T M A L hH W hW B hBA hBoff c8).elim
  · obtain ⟨-, n, hn, ⟨K, hKf, hKfin, hK, π, hπ⟩, -⟩ := c9
    exact (false_of_sl_sectionK hLn hH hW hn (by simpa using hK) π hπ.1).elim
  · obtain ⟨⟨π, hπ⟩, -⟩ := c10
    exact (false_of_sl_sectionK hLn hH hW (Or.inl rfl) (K := ZMod 2) (by simp) π hπ.1).elim
  · obtain ⟨-, -, -, -, π, hπ, -⟩ := c11
    exact (false_of_sl_sectionK hLn hH hW (Or.inr rfl) (K := ZMod 2) (by simp) π hπ.1).elim

theorem false_of_excluded (hExc : E2P.E22Char2ExcFam) (hAlt : E2P.E22AltFam) (hF : E2P.E22Families)
    {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L)
    (h : ExcludedType (↥L ⧸ Subgroup.center ↥L)) : False := by
  rcases h with ⟨f, hf, h⟩ | h | h | h
  · exact not_char2Exc hExc hH (Or.inl ⟨f, hf, h⟩)
  · exact not_alt_seven hAlt hH h
  · exact not_alt_eight hAlt hH h
  · exact not_psu_three_three hF hH h

theorem asB69ComponentK_of (hbr : B113KDet.CatalogBridge)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hB42 : AsB42) (hA21 : AsA21SQTKSection) (hAlt : E2P.E22AltFam) (hLn : E2P.E22LnTwoFam)
    (hExc : E2P.E22Char2ExcFam) (hF : E2P.E22Families) (hCov : AsSQTKOddCovers)
    (hEven : AsAltEven) (hSlice : AsAltSlice) : B69.AsB69ComponentK := by
  intro V _ _ hV X T M A L hH W hW
  have hO2 : pCoreOf 2 X = ⊥ := hH.2.2.1
  have hAo : IsFFStarOffender X A := hH.2.2.2.2.2.1.1
  have hL : CFSG.Open.IsComponentOf L X := hH.2.2.2.2.2.2.1
  have hLA : ⁅L, A⁆ = L := hH.2.2.2.2.2.2.2
  have hFFc := B113KDet.ffConclusion_of_mulAut hbr hFF hV hH.1 hO2 hAo hL hLA
  rcases typeSplit_cert hFFc with hs | hr | hx | ⟨m, hm, hmA⟩
  · have hKL : CFSG.SectionRank.IsKGroupCat ↥L :=
      CFSG.SectionRank.IsKGroupCat.of_mulEquiv
        (CFSG.SectionRank.IsKGroupCat.subgroup hH.1 (L.subgroupOf X))
        (Subgroup.subgroupOfEquivOfLe hL.1).symm
    exact chainK hB42 hA21 hAlt hLn hExc hF V hV X T M A L hH
      ⟨stronglyQuasithin_of_survivor hCov hL.2.2 (odd_card_center_comp hO2 hL) hs, hKL⟩ W hW
  · exact (false_of_highRank hH hr).elim
  · exact (false_of_excluded hExc hAlt hF hH hx).elim
  · rcases Nat.even_or_odd m with hev | hodd
    · exact (not_alt_even hEven hH (by obtain ⟨c, hc⟩ := hev; omega) hev hmA).elim
    · by_cases hp : ∃ j : ℕ, m = 2 ^ j + 1
      · obtain ⟨j, rfl⟩ := hp
        have hj : 3 ≤ j := by
          by_contra hj
          have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact Or.inr (hSlice V hV X T M A L hH W hW j hj hmA)
      · exact (not_alt_odd hH hm hodd hp hmA).elim

end Chain

end B69K

end CFSG.Quasithin
