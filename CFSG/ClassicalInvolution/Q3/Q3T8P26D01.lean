module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Asc77.AscT8YC6
public import CFSG.ClassicalInvolution.Asc77.AscT8ZB1
public import CFSG.ClassicalInvolution.Q3.Q3T8C261
public import CFSG.ClassicalInvolution.Q3.Q3T8P26A01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26B01
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
public import CFSG.ClassicalInvolution.Q3.Q3T8P26P02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26P01
import CFSG.ClassicalInvolution.Asc77.AscT8ZB1Eng
import CFSG.ClassicalInvolution.Asc77.AscT8ZB2Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YC7
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY

@[expose] def LayerCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ¬ DConnected (Q3T7.layerFam3 Ω (z * t)) → ∀ F : FrameData Ω W K J z t,
          F.vGroup ≤ zStarOf (Q3NL.exactLayer3 Ω (z * t)) ∧
            zStarOf (Q3NL.exactLayer3 Ω (z * t)) ≤
              F.vGroup ⊔ oddCoreOf (Q3NL.exactLayer3 Ω (z * t))


theorem layerFrattiniFact_of_center (hC : LayerCenterFact) : LayerFrattiniFact := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne hnconn F c hc
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨h1, h2⟩ := hC G Ω K J S R T W z t hs hdisc hμ hne hnconn F
  obtain ⟨hVab, -⟩ := alphaOf_vGroup_eq hs F
  set Y := Q3NL.exactLayer3 Ω (z * t) with hY
  have hcz : c ∈ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hcY : conjSub c Y = Y := Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hcz
  have hle : conjSub c F.vGroup ≤ F.vGroup ⊔ oddCoreOf Y := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hxz : x ∈ zStarOf Y := by
      have := conj_mem_zStarOf hcY (h1 hx)
      simpa [mul_assoc] using this
    exact h2 hxz
  have hcardV : Nat.card F.vGroup = 2 ^ 2 := hVab.1
  have hV : IsPGroup 2 F.vGroup := IsPGroup.of_card hcardV
  have hcard : Nat.card (conjSub c F.vGroup) = Nat.card F.vGroup := by
    unfold conjSub
    exact Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hV' : IsPGroup 2 (conjSub c F.vGroup) := IsPGroup.of_card (hcard.trans hcardV)
  have hVc : ∀ v ∈ F.vGroup, v ∈ Subgroup.centralizer ({z * t} : Set G) := by
    intro v hv
    have hzt : z * t ∈ F.vGroup := by
      have h01 : F.zz 0 * F.zz 1 ∈ F.vGroup := Subgroup.subset_closure (Set.mem_insert _ _)
      rwa [F.hz0, F.hz1] at h01
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hv2 : (v * (z * t)) * (v * (z * t)) = 1 := hVab.2 _ (F.vGroup.mul_mem hv hzt)
    have hvv : v * v = 1 := hVab.2 v hv
    have hzz : (z * t) * (z * t) = 1 := hVab.2 _ hzt
    calc v * (z * t) = (v * (z * t))⁻¹ := (inv_eq_of_mul_eq_one_right hv2).symm
      _ = (z * t)⁻¹ * v⁻¹ := mul_inv_rev _ _
      _ = (z * t) * v := by
        rw [inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hvv]
  have hVO : F.vGroup ≤ Subgroup.normalizer (oddCoreOf Y : Set G) := by
    intro v hv
    have hvz : v ∈ T8.cenZ (z * t) := by
      rw [T8.cenZ_eq_centralizer]
      exact hVc v hv
    have hvY : conjSub v Y = Y := Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hvz
    rw [mem_normalizer_iff_conjSub_eq, ← Thompson.oddCoreOf_conjSub_eq, hvY]
  obtain ⟨o, ho, hoV⟩ :=
    exists_oddCore_conj_of_le_sup (oddCoreOf_odd_natCard Y) hV hV' hVO hle hcard
  exact ⟨o, ho, by rw [conjSub_mul, hoV]⟩

end T8YY
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_rep_le_cenZ (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    (i : Fin 4) : (F.ρ i).R ≤ T8.cenZ (z * t) := by
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  intro r hr
  rw [T8.mem_cenZ_iff, zt_eq_frame F]
  exact T8YY.commute_frame_prod_of_mem_DSet c F.ρ F.hadj F.hclos F.hz (F.ρ i).hR hr 0 1

theorem frame_xMem (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    (i : Fin 4) : T8.XMem Ω (z * t) (F.ρ i).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.frame_xMemE hΩ.conjInvariant hnt c.comm_W F (zt_eq_frame F)
    (fun j => frame_rep_le_cenZ hs F j) i

theorem frame_zz_mem_layerJoin (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    (i : Fin 4) : F.zz i ∈ Q3NL.exactLayer3 Ω (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKt : (F.ρ i).K ∈ Q3NL.tqMembers3 Ω (z * t) :=
    (frame_xMem hs F i).mem_tqMembers3 hΩ hx
  have hL := Layer.isSylow2In_exactCore3_of_le_cenZ (F.ρ i).hRK (frame_rep_le_cenZ hs F i)
  have h8 := hΩ.eight_le_of_mem_RSet (F.ρ i).hR.1
  have hzR : F.zz i ∈ (F.ρ i).R :=
    T3.mem_of_isPGroup (F.hz i) (F.ρ i).hRK.1 (F.ρ i).hRK.2.1 (by omega)
  exact Q3NL.exactCore3_le_exactLayer3 hKt (hL.1 hzR)

theorem frame_isUniqueInvolution_layerRes (hs : Std8 Ω K J S R T W z t)
    (F : T8YY.FrameData Ω W K J z t) (i : Fin 4) :
    IsUniqueInvolution (Q3NL.exactCore3 (z * t) (F.ρ i).K) (F.zz i) :=
  Layer.isUniqueInvolution_exactCore3 (frame_xMem hs F i).2.1 (F.hz i)

theorem frame_isUniqueInvolution_layerImg (hs : Std8 Ω K J S R T W z t)
    (F : T8YY.FrameData Ω W K J z t) (i : Fin 4) :
    IsUniqueInvolution (Layer.layerImg3 Ω (z * t) (F.ρ i).K)
      (T8V.layerMk (z * t) (F.zz i) (frame_zz_mem_layerJoin hs F i)) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hKt : (F.ρ i).K ∈ Q3NL.tqMembers3 Ω (z * t) :=
    (frame_xMem hs F i).mem_tqMembers3 hΩ hx
  have hLY : Q3NL.exactCore3 (z * t) (F.ρ i).K ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hKt
  exact isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
    (isUniqueInvolution_subgroupOf (frame_isUniqueInvolution_layerRes hs F i) hLY)

theorem frame_layerImg_ne (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    Layer.layerImg3 Ω (z * t) (F.ρ i).K ≠ Layer.layerImg3 Ω (z * t) (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hKt : (F.ρ i).K ∈ Q3NL.tqMembers3 Ω (z * t) :=
    (frame_xMem hs F i).mem_tqMembers3 hΩ hx
  have hL : Layer.LayerHyp Ω (z * t) :=
    Layer.LayerHyp.of_stand3 hs.stand.toStand3 hx ⟨_, hKt⟩
  exact Layer.layerImg3_ne_of_involutions hL (frame_xMem hs F i) (frame_xMem hs F j)
    (F.hz i) (F.hz j) (F.zz_comm c i j) (F.hinj i j hij)

theorem frame_layerImg_nbr (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    Layer.layerImg3 Ω (z * t) (F.ρ j).K ∈
      omegaNbr (Q3T7.layerFam3 Ω (z * t)) (Layer.layerImg3 Ω (z * t) (F.ρ i).K) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hKi : (F.ρ i).K ∈ Q3NL.tqMembers3 Ω (z * t) :=
    (frame_xMem hs F i).mem_tqMembers3 hΩ hx
  have hKj : (F.ρ j).K ∈ Q3NL.tqMembers3 Ω (z * t) :=
    (frame_xMem hs F j).mem_tqMembers3 hΩ hx
  have hPN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set G) := fun y hy =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (F.ρ i).hK (hnt _ (F.ρ i).hK)
      (F.hz i) (T8.rep_le_centralizer c (F.ρ j) (F.ρ i)
        (Or.inr (F.hadj j i (Ne.symm hij))) (F.hz i) hy)
  exact Layer.layerImg3_omegaNbr hKi hKj (F.ρ j).hRK (frame_rep_le_cenZ hs F j) hPN
    (frame_layerImg_ne hs F hij)

end T8ZZ
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem vGroup_le_layerJoin (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t) :
    F.vGroup ≤ Q3NL.exactLayer3 Ω (z * t) := by
  unfold FrameData.vGroup
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact (Q3NL.exactLayer3 Ω (z * t)).mul_mem (frame_zz_mem_layerJoin hs F 0)
      (frame_zz_mem_layerJoin hs F 1)
  · exact (Q3NL.exactLayer3 Ω (z * t)).mul_mem (frame_zz_mem_layerJoin hs F 0)
      (frame_zz_mem_layerJoin hs F 2)

theorem layerCenter_of_central [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (F : T8YY.FrameData Ω W K J z t)
    (h01 : T8V.layerMk (z * t) (F.zz 0) (frame_zz_mem_layerJoin hs F 0) *
      T8V.layerMk (z * t) (F.zz 1) (frame_zz_mem_layerJoin hs F 1) ∈
        Subgroup.center (Q3T7.layerQuot3 Ω (z * t)))
    (h02 : T8V.layerMk (z * t) (F.zz 0) (frame_zz_mem_layerJoin hs F 0) *
      T8V.layerMk (z * t) (F.zz 2) (frame_zz_mem_layerJoin hs F 2) ∈
        Subgroup.center (Q3T7.layerQuot3 Ω (z * t)))
    (hcard : Nat.card (Subgroup.center (Q3T7.layerQuot3 Ω (z * t))) ≤ 4) :
    F.vGroup ≤ zStarOf (Q3NL.exactLayer3 Ω (z * t)) ∧
      zStarOf (Q3NL.exactLayer3 Ω (z * t)) ≤
        F.vGroup ⊔ oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) := by
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.layerCenter_of_centralE F (fun i => frame_zz_mem_layerJoin hs F i) F.vGroup rfl
    (T8YY.alphaOf_vGroup_eq hs F).1 (vGroup_le_layerJoin hs F) h01 h02 hcard

end T8ZZ
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
open CFSG.ClassicalInvolution.RouteD.Gaps (InvOf)
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ

theorem layerCenterFact_proved : T8YY.LayerCenterFact := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne hnconn F
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hKt : ∀ i, (F.ρ i).K ∈ Q3NL.tqMembers3 Ω (z * t) := fun i =>
    (frame_xMem hs F i).mem_tqMembers3 hΩ hx
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨_, hKt 0⟩
  have hne0 : (Q3NL.tqMembers3 Ω (z * t)).Nonempty := ⟨_, hKt 0⟩
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (Layer.zt_not_central3 hs)
  have hΨ := Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0
  have hinj : Function.Injective
      (fun i : Fin 3 => Layer.layerImg3 Ω (z * t) (F.ρ i.castSucc).K) := by
    intro i j h
    by_contra hij
    exact frame_layerImg_ne hs F (fun h' => hij (Fin.castSucc_injective _ h')) h
  obtain ⟨e, ⟨M⟩⟩ := T8X.exists_spin8_datum_of_triangle hs.stand.ih hs.stand.below hlt hΨ
    Q3T7.layerQuot3_oddCore_eq_bot (Q3T7.omegaGen_layerFam3 hs3 hL.hc2 hne0)
    (Q3T7.aEmpty_layerFam3 hs3 hL.hc2 hne0)
    (fun i : Fin 3 => Layer.layerImg3 Ω (z * t) (F.ρ i.castSucc).K)
    (fun i => Layer.layerImg3_mem (hKt _)) hinj
    (fun i j hij => frame_layerImg_nbr hs F (fun h' => hij (Fin.castSucc_injective _ h')))
    hnconn
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = 1 := M.exp_eq_f hD4
  have hF : PlusModelFacts 3 e := by
    rw [he]
    exact plusModelFacts
  have hrep : ∀ i : Fin 4, ∃ Ri ∈ M.cls, Layer.layerImg3 Ω (z * t) (F.ρ i).K = Ri.map M.ψ :=
    fun i => (M.mem_iff _).mp (Layer.layerImg3_mem (hKt i))
  choose Rs hRs hRsψ using hrep
  have hlift : ∀ i : Fin 4, ∃ ζ, InvOf (Rs i) ζ ∧
      M.ψ ζ = T8V.layerMk (z * t) (F.zz i) (frame_zz_mem_layerJoin hs F i) := by
    intro i
    refine datum_exists_involution_lift M hF (hRs i) ?_
    rw [← hRsψ i]
    exact frame_isUniqueInvolution_layerImg hs F i
  choose ζ hζ hζψ using hlift
  have hcomm : ∀ i j : Fin 4, i ≠ j → Commutes (Rs i) (Rs j) := by
    intro i j hij
    refine Q3MT.commutes_of_omegaNbr3 M hΨ hG2 hD4 (hRs i) (hRs j) ?_
    rw [← hRsψ i, ← hRsψ j]
    exact frame_layerImg_nbr hs F hij
  have hprod : ∀ i j : Fin 4, i ≠ j →
      T8V.layerMk (z * t) (F.zz i) (frame_zz_mem_layerJoin hs F i) *
        T8V.layerMk (z * t) (F.zz j) (frame_zz_mem_layerJoin hs F j) ∈
          Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := by
    intro i j hij
    have h := datum_mul_mem_center M hF (hRs i) (hRs j) (hcomm i j hij) (hζ i) (hζ j)
    rwa [hζψ i, hζψ j] at h
  exact layerCenter_of_central hs F (hprod 0 1 (by decide)) (hprod 0 2 (by decide))
    (datum_card_center_le M hF)

end T8ZZ
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
