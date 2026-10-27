module

public import CFSG.Quasithin.EmptyFaithful.SBd18Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D25
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D45
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBd14Glue
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBd15Step
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzN15Final

public section

namespace CFSG.Quasithin.SBd18

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem false_of_restHyp_f_F4 (F : SBd15.Frontier15338_F4) (h312 : A312ForSQTK) (h318 : A318Facts)
    (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    ∀ (n : ℕ) (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
      Nat.card G - Nat.card ↥I = n → SBd14.RestHyp T Mc M V₁ V₂ Yp I L t → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T Mc M V₁ V₂ Yp I L t hn r
    have hV : V₁ = centerOf L := r.V₁_eq_center F.h113
    have hII₁ : I ≤ Subgroup.normalizer (V₁ : Set G) := SBd14.le_normalizer_of_eq_center r.hNL hV
    by_cases hI : Subgroup.normalizer (V₁ : Set G) ≤ I
    · exact r.false_of_residues_f h312 h318 kC kF F.h113 (le_antisymm hII₁ hI)
    · obtain ⟨W₁, W₂, L₁, r₁⟩ := SBd15.exists_next_F4 F r
      have hlt : Nat.card ↥I < Nat.card ↥(Subgroup.normalizer (V₁ : Set G)) := by
        by_contra hge
        exact hI (Subgroup.eq_of_le_of_card_ge hII₁ (not_lt.mp hge)).ge
      have hle : Nat.card ↥(Subgroup.normalizer (V₁ : Set G)) ≤ Nat.card G :=
        Subgroup.card_le_card_group _
      exact ih (Nat.card G - Nat.card ↥(Subgroup.normalizer (V₁ : Set G))) (by omega)
        T Mc M W₁ W₂ Yp _ L₁ t rfl r₁

theorem input15338RestV_of_residues_f_F4 (F : SBd15.Frontier15338_F4) (h312 : A312ForSQTK)
    (h318 : A318Facts) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    SBd14.Input15338RestV_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4 _hV
  exact false_of_restHyp_f_F4 F h312 h318 kC kF _ T Mc M V₁ V₂ Yp I L t rfl
    ⟨c, hL0, hn2, hYL, hy, hY, hNL, hYY, hB, hBM, hQV, h1, h2, h3, h4⟩

theorem input15338Rest_of_residues_f_F4 (F : SBd15.Frontier15338_F4) (h312 : A312ForSQTK)
    (h318 : A318Facts) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    SBd9.Input15338Rest_F4 :=
  SBd14.input15338Rest_of_restV_F4 F.h113 (input15338RestV_of_residues_f_F4 F h312 h318 kC kF)

theorem input15338_of_residues_f_F4 (F : SBd15.Frontier15338_F4) (hrank : Lemma122Rank)
    (h312 : A312ForSQTK) (h318 : A318Facts) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    Input15338_F4 :=
  SBd9.input15338_of_rest_F4 F.h113 F.hA37 F.hA38 hrank F.kR
    (input15338Rest_of_residues_f_F4 F h312 h318 kC kF)

theorem stage15344_of_named_stageB_inputs_final18_F4
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (h15 : Input15315Two) (h16 : Input15316One)
    (kR : Input21Rank) (kP : Input21ProperRank)
    (k17L : ThreeRankBlocks) (k17B : SolvOvergroupsThreePrime) (k17T : ThetaEqComponent)
    (k19C : Lin2QuotIsLin2OrA5) (k19F : A5FixedPoints) (k19O : A5OddCommuting)
    (k20N : SL3Sp4NotA38Type) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (k20B : SolvOvergroupsInBorel) (k20C : RankTwoMaxParabolics)
    (k21N : A7NotA38Type) (k21T : HatA6ProperThreePart) (k21E : ExcA7NoS3Section)
    (k21O : OrdA7ConfigNoNine) (k21S : HatA6SwapLocal)
    (h23 : Input15323_F4) (h24 : Input15324M_F4)
    (h26 : Input15326Two) (h27 : Input15327) (h28 : Input15328)
    (h30 : Input15330) (h31 : Input15331_F4) (h32 : Input15332) (hc : Input15325Count)
    (h33 : Stage15325_F4 → ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G]
      (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
      CtxComp T Mc M V₁ V₂ Yp I t → ∃ L : Subgroup G, Concl15333 T M V₁ Yp I L)
    (h34 : Input15334) (h36 : Input15336One)
    (h37 : Input15337) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) (h39 : Input15339)
    (h40 : Input15340)
    (hcl : Input15335Close) (hr : Input15343Reduce) (he : Input15343Elim)
    (hA39 : A39ForSQTK) (hrank : Lemma122Rank) (h312 : A312ForSQTK) (h318 : A318Facts) :
    Stage15344_F4 :=
  have h5 : Input15311FiveII := S153D.input15311FiveII_of_stages h11 h113
  have h13 : Stage15313_F4 :=
    stage15313_of_named_stageB_inputs7M3_F4 h11 h113 hC27 hA37 hA38 hcover h15 h16 h36 kR kP k17L k17B
      k17T
      (lin2Setup_of_noStar hA37 hA38 (lin2SetupNoStar_of_inner hA37 hA38 k17L (lin2YInner_holds hA37 hA38)))
      (lin2RLSylow_holds hA37 hA38) (lin2ZLInYL_holds hA37 hA38) k19C
      (a5Setup_of_noStar hA37 hA38 (a5SetupNoStar_of_short hA37 hA38 a5IsShort_holds)) k19F k19O k20N
      (SzN15.noGraphAutOnFFModule3_of_b51 hB51 hA21 hcover)
      k20B k20C k21N k21T k21E k21O (hatA6VleU_holds h113) k21S h23 h24
  have h25 : Stage15325_F4 :=
    stage15325_of_blocks_F4 h113 h13
      (stage15325One_of_inputs_F4 h11 h113 hA37 hA38 h5 h26 h27 h28 h30 h31 h32 hc)
  have h8 : Input15311Eight := S153D.input15311Eight_of_stages h113
  have h38 : Input15338_F4 :=
    input15338_of_residues_f_F4 ⟨h11, h113, h25, h34, h36, h37, hA37, hA38, hA39, rankOneFamilies153_holds,
      rankTwoFamilies153_holds⟩ hrank h312 h318 kC kF
  stage15344_of_blocks_F4 h25
    (stageComponentCase_of_blocks_F4 h113
      (stageComponentTwo_of_inputs_F4 h11 h113 h25 h8 h33 h34 h36 h37 h38 h39 h40 hcl)
      (stageComponentOne_of_inputs_F4 h11 h113 h25 h8 h5 h33 h34
        (S153D.input15343Open_of_notA4 h113 (S153D.input15343NotA4_proved h113)) hr he))

end CFSG.Quasithin.SBd18
