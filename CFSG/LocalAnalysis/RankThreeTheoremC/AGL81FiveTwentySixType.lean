module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixStar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Print516
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN

variable {X : Type} [Group X] [Finite X] {T L : Subgroup X}

theorem le_threeNormalizerJoin_of_le_gnC (hX : GNSetting X T) (hLC : L ≤ gnC T)
    (h3 : 3 ∣ Nat.card L) : L ≤ threeNormalizerJoin T L := by
  by_cases hT : T = ⊥
  · haveI : Subsingleton X := hX.subsingleton_of_eq_bot hT
    have hLbot : L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact Subsingleton.elim x 1
    rw [hLbot]
    exact bot_le
  · have hZT : CFSG.Quasithin.omegaOneCenterOf T ≤ T :=
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T
    have hZne : CFSG.Quasithin.omegaOneCenterOf T ≠ ⊥ :=
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot (S := T) hX.sylow.2.1 hT
    have hZc : ((CFSG.Quasithin.omegaOneCenterOf T).subgroupOf T).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T
    have hLN : L ≤ Subgroup.normalizer ((CFSG.Quasithin.omegaOneCenterOf T) : Set X) :=
      hLC.trans ((gnC_le_centralizer (le_refl _)).trans (Subgroup.centralizer_le_normalizer _))
    have h3' : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer
        ((CFSG.Quasithin.omegaOneCenterOf T) : Set X)) := by
      rw [inf_eq_left.mpr hLN]
      exact h3
    have hle := inf_normalizer_le_threeNormalizerJoin hZT hZne hZc h3'
    rwa [inf_eq_left.mpr hLN] at hle

omit [Finite X] in
theorem le_threeNormalizerJoin_of_le_centralizer {C₁ : Subgroup X}
    (h1 : C₁ ≤ CFSG.Quasithin.omegaOneCenterOf T) (hne : C₁ ≠ ⊥)
    (hc : (C₁.subgroupOf T).Characteristic) (h3 : 3 ∣ Nat.card L)
    (hLs : L.map (toStar T) ≤ gnImg T (Subgroup.centralizer (C₁ : Set X))) :
    L ≤ threeNormalizerJoin T L := by
  have hC₁T : C₁ ≤ T :=
    h1.trans (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hCN : gnC T ≤ Subgroup.normalizer (C₁ : Set X) :=
    (gnC_le_centralizer h1).trans (Subgroup.centralizer_le_normalizer _)
  have hLN : L ≤ Subgroup.normalizer (C₁ : Set X) := by
    have hmap : L.map (toStar T) ≤ (Subgroup.normalizer (C₁ : Set X)).map (toStar T) :=
      hLs.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer (C₁ : Set X)))
    have hle : L ≤ Subgroup.comap (toStar T)
        ((Subgroup.normalizer (C₁ : Set X)).map (toStar T)) :=
      Subgroup.map_le_iff_le_comap.mp hmap
    rwa [Subgroup.comap_map_eq_self (f := toStar T) (H := Subgroup.normalizer (C₁ : Set X))
      (by rw [QuotientGroup.ker_mk']; exact hCN)] at hle
  have h3' : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (C₁ : Set X)) := by
    rw [inf_eq_left.mpr hLN]
    exact h3
  have hle := inf_normalizer_le_threeNormalizerJoin hC₁T hne hc h3'
  rwa [inf_eq_left.mpr hLN] at hle

theorem le_threeNormalizerJoin_of_le_normalizer (hX : GNSetting X T) (hL : IsC2 L)
    (hLC : ¬ L ≤ gnC T) {C₂ : Subgroup X} (h2T : C₂ ≤ T) (hne : C₂ ≠ ⊥)
    (hc : (C₂.subgroupOf T).Characteristic) (h3 : 3 ∣ Nat.card L)
    (hLs : L.map (toStar T) ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) :
    L ≤ threeNormalizerJoin T L := by
  have hC₂norm : (C₂.subgroupOf T).Normal :=
    Subgroup.normal_of_characteristic (C₂.subgroupOf T) (h := hc)
  have hTN : T ≤ Subgroup.normalizer (C₂ : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h2T).mp hC₂norm
  have hperf : ⁅L.map (toStar T), L.map (toStar T)⁆ = L.map (toStar T) := by
    rw [← Subgroup.map_commutator, commutator_eq_self_of_isC2 hL]
  have hgen : pElementSubgroup 2 (L.map (toStar T)) = L.map (toStar T) :=
    pElementSubgroup_two_eq_of_perfect hperf
  have hgnA : gnA T C₂ (L.map (toStar T)) = L.map (toStar T) :=
    gnA_eq_of_le_normalizer hLs
  have hle2 : L.map (toStar T) ≤ (L ⊓ Subgroup.normalizer (C₂ : Set X)).map (toStar T) :=
    calc L.map (toStar T) = pElementSubgroup 2 (L.map (toStar T)) := hgen.symm
      _ = pElementSubgroup 2 (gnA T C₂ (L.map (toStar T))) := by rw [hgnA]
      _ ≤ (L ⊓ Subgroup.normalizer (C₂ : Set X)).map (toStar T) :=
        pElementSubgroup_two_gnA_le hX hL hLC hTN
  have hLH : T ⊓ L ≤ L ⊓ Subgroup.normalizer (C₂ : Set X) :=
    le_inf inf_le_right (inf_le_left.trans hTN)
  have hLnorm : L ≤ Subgroup.normalizer (C₂ : Set X) :=
    (le_of_map_toStar_le hX hL hLC inf_le_left hLH hle2).trans inf_le_right
  have h3' : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (C₂ : Set X)) := by
    rw [inf_eq_left.mpr hLnorm]
    exact h3
  have hle := inf_normalizer_le_threeNormalizerJoin h2T hne hc h3'
  rwa [inf_eq_left.mpr hLnorm] at hle

theorem le_threeNormalizerJoin_of_classical (hG : KFactChevGenThree) (hX : GNSetting X T)
    (hL : IsC2 L) (hLC : ¬ L ≤ gnC T) {C₁ C₂ : Subgroup X}
    (hP : CFSG.Quasithin.IsC118Pair T C₁ C₂) (hPar : GNParabolic T C₁ C₂)
    (hY : GNYComponent T C₁ C₂ (L.map (toStar T)))
    (hcl : CFSG.AGLEmbedding.IsClassicalTwoOrG2
      (↥(L.map (toStar T)) ⧸ Subgroup.center ↥(L.map (toStar T)))) :
    L ≤ threeNormalizerJoin T L := by
  have hpair := isGNPair_of_isC118Pair hP
  have hC₁T : C₁ ≤ T :=
    hpair.le_center.trans (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hC₂T : C₂ ≤ T := hpair.le₂
  have hC₁N : gnC T ≤ Subgroup.normalizer (C₁ : Set X) :=
    (gnC_le_centralizer hpair.le_center).trans (Subgroup.centralizer_le_normalizer _)
  have hC₁norm : (C₁.subgroupOf T).Normal :=
    Subgroup.normal_of_characteristic (C₁.subgroupOf T) (h := hpair.char₁)
  have hTN₁ : T ≤ Subgroup.normalizer (C₁ : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₁T).mp hC₁norm
  have hC₂norm : (C₂.subgroupOf T).Normal :=
    Subgroup.normal_of_characteristic (C₂.subgroupOf T) (h := hpair.char₂)
  have hTN₂ : T ≤ Subgroup.normalizer (C₂ : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₂T).mp hC₂norm
  have hcov : ParabolicCover T C₁ C₂ (L.map (toStar T)) :=
    fun P hPb => hPar (L.map (toStar T)) hY.1 (isChevTwo_of_classicalTwoOrG2 hcl) P hPb
  have hS₀ : IsSylowTwoOf (gnImg T T ⊓ L.map (toStar T)) (L.map (toStar T)) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
      hX.sylow hY.1.2.1
  obtain ⟨Ps, hPs, hgen, hK⟩ :=
    hG _ (L.map (toStar T)) _ hY.1.2.2 hcl hS₀
  have hgnA₁ : gnA T C₁ (L.map (toStar T)) =
      (L ⊓ Subgroup.normalizer (C₁ : Set X)).map (toStar T) :=
    gnImg_inf_map_eq hC₁N L
  have hJ₁ : L ⊓ Subgroup.normalizer (C₁ : Set X) ≤ threeNormalizerJoin T L := by
    obtain ⟨⟨P₁, hP₁, hP₁A⟩, -⟩ := exists_parabolic_le_gnA hY hcov hPs hgen
    obtain ⟨x, hx, ho, -⟩ := hK P₁ hP₁
    exact inf_normalizer_le_threeNormalizerJoin hC₁T hpair.ne_bot₁ hpair.char₁
      (three_dvd_card_of_mem_map (toStar T) (hgnA₁ ▸ hP₁A hx) ho)
  have hTJ : T ⊓ L ≤ threeNormalizerJoin T L :=
    (le_inf inf_le_right (inf_le_left.trans hTN₁)).trans hJ₁
  have hLstar : L.map (toStar T) ≤ (threeNormalizerJoin T L).map (toStar T) := by
    rw [hgen]
    refine iSup₂_le fun P hP => ?_
    obtain ⟨x, hx, ho, -⟩ := hK P hP
    have hPL : pElementSubgroup 2 P ≤ L.map (toStar T) :=
      (pElementSubgroup_le P).trans (hPs P hP).1
    rcases hcov P (hPs P hP) with h1 | h2
    · have hsub : pElementSubgroup 2 P ≤
          (L ⊓ Subgroup.normalizer (C₁ : Set X)).map (toStar T) := by
        rw [← hgnA₁]
        exact le_inf (h1.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))) hPL
      exact hsub.trans (Subgroup.map_mono hJ₁)
    · have hsub : pElementSubgroup 2 P ≤
          (L ⊓ Subgroup.normalizer (C₂ : Set X)).map (toStar T) := by
        refine (Subgroup.closure_mono ?_).trans (pElementSubgroup_two_gnA_le hX hL hLC hTN₂)
        intro y hy
        exact ⟨⟨h2 (Subgroup.subset_closure hy),
          hPL (Subgroup.subset_closure hy)⟩, hy.2⟩
      have h3₂ : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (C₂ : Set X)) :=
        three_dvd_card_of_mem_map (toStar T) (hsub hx) ho
      exact hsub.trans (Subgroup.map_mono
        (inf_normalizer_le_threeNormalizerJoin hC₂T hpair.ne_bot₂ hpair.char₂ h3₂))
  exact le_of_map_toStar_le hX hL hLC (threeNormalizerJoin_le T L) hTJ hLstar

theorem le_threeNormalizerJoin
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (h516 : AGL81I516)
    (hG : KFactChevGenThree) (hAF : GNAltFacts) (hAlt : AGL81FiveTwentySixAlt)
    (hX : GNSetting X T) (hL : IsC2 L) (h3 : 3 ∣ Nat.card L) :
    L ≤ threeNormalizerJoin T L := by
  by_cases hLC : L ≤ gnC T
  · exact le_threeNormalizerJoin_of_le_gnC hX hLC h3
  · have hcomp : CFSG.Open.IsComponentOf (L.map (toStar T)) ⊤ :=
      isComponentOf_map_toStar hX hL hLC
    have hT : T ≠ ⊥ := hX.ne_bot_of_isComponentOf hcomp
    obtain ⟨C₁, C₂, hP⟩ := exists_isC118Pair hX hT
    have hpair := isGNPair_of_isC118Pair hP
    by_cases hY : GNYComponent T C₁ C₂ (L.map (toStar T))
    · rcases classical_or_alt_of_gnYComponent hFF hX hP hY with hcl | ⟨n, hn, he⟩
      · exact le_threeNormalizerJoin_of_classical hG hX hL hLC hP
          (h516 X T hX C₁ C₂ hP) hY hcl
      · have hZ : Subgroup.center ↥(L.map (toStar T)) = ⊥ :=
          (hAF X T hX hT C₁ C₂ hP (L.map (toStar T)) hY n hn he).1
        have he' : Nonempty (↥(L.map (toStar T)) ≃* alternatingGroup (Fin n)) :=
          ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
            QuotientGroup.quotientBot).symm.trans he.some⟩
        exact hAlt X T L hX hL C₁ C₂ hP hY n hn he'
    · rcases le_or_le_of_not_gnYComponent hcomp hY with h1 | h2
      · exact le_threeNormalizerJoin_of_le_centralizer hpair.le_center hpair.ne_bot₁
          hpair.char₁ h3 h1
      · exact le_threeNormalizerJoin_of_le_normalizer hX hL hLC hpair.le₂ hpair.ne_bot₂
          hpair.char₂ h3 h2

end CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix
