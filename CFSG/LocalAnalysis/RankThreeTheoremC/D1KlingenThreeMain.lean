module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem exists_d1A9DataCore_of_klingen (hmod : StmtKlingenModel) (hk3 : KFactKlingenThreeLocal)
    [Fact (Nat.Prime 3)] {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hcfg : D1ComponentConfig3 3 P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype)
    (hKD : HasKlingenData 3 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))))
    (hsp : IsKlingenComponent 3 K) {X : Subgroup G} (hS : D1SurvivorData 3 P M H R X)
    (hXel : IsElemAbelian 3 X) (hXc : Nat.card X = 3 ^ 3) :
    ∃ σ z : G, D1A9DataCore P M H R X σ z := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hsp
  have hZ : Subgroup.center K = ⊥ :=
    hmod.center K 3 d hcfg.loc.ne_two hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK₀ : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have eK : K ≃* CatGroup d := eK₀.trans e₁
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  have hred := hcfg.red
  have hXH : X ≤ H := hS.le_R.trans hcfg.ext.le_H
  have hXp : IsPGroup 3 X := hcfg.ext.isPGroup.to_le hS.le_R
  have hXp' : IsPGroup 3 (X.subgroupOf H) := hXp.comap_subtype
  have hcard : Nat.card ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3))) = 3 ^ 3 := by
    rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime 3) hXp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hXRb : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hcfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hS.le_R)
  have hXe : IsElemAbelian 3 ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3))) := by
    refine elementary_abelian_map 3 ?_ _
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := (isMulCommutative_iff.mp hXel.1) ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hXel.2 _ (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨hIS, hT, hZc⟩ := hk3 d hd (H ⧸ primeComplementCore (G := H) 3) K hKn ⟨eK⟩ hC Rbar _ _
    hXRb hXe hcard hred.weakCore_le hred.ne_top hKD
  obtain ⟨σ', z', hσT, hσB, hσ3, hzB, hz1, hzc, hfix, hesc⟩ :=
    exists_sigma_z_of_klingenData hXRb hXe hcard hred.weakCore_le hT hZc hKD
  exact exists_d1A9DataCore_of_local hcfg hS hXel hXc hIS hT hσT hσB hσ3 hzB hz1 hzc hfix hesc

theorem stmtKlingenMSide3_of_five (hmod : StmtKlingenModel) (hk3 : KFactKlingenThreeLocal)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hi : KFactBlockThreeOneOrbit) (h : StmtKlingenMSideFive3 G) : StmtKlingenMSide3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD hsp X hS hXel hXc
  by_cases hp3 : p = 3
  swap
  · exact h p hp3 P M H R Rbar hcfg K hK huniq hnc hcent hKD hsp X hS hXel hXc
  subst hp3
  obtain ⟨σ, z, hA⟩ :=
    exists_d1A9DataCore_of_klingen hmod hk3 hcfg hK huniq hcent hKD hsp hS hXel hXc
  exact stmtA9MSide3_of h84 h85 h86 h93 hD2 hK2 hC3 hK5 hi hcfg.glob.rank hcfg.loc.sigma
    hcfg.loc.isCoreMaxLocal.1.1 hA

end CFSG.LocalAnalysis.RankThreeTheoremC
