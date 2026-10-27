module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26B01
import CFSG.ClassicalInvolution.Asc77.AscT8ZC6Eng
import CFSG.ClassicalInvolution.Q3.Q3T8RepHooks
public import CFSG.ClassicalInvolution.Asc77.AscT8ZA1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
open scoped commutatorElement
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem z_not_central [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) :
    ¬ ({z} : Set G) ⊆ Subgroup.center G :=
  Layer.not_central_of_ne_one3 hs.stand.modU hs.stand.mem hs.hz.ne_one

theorem xMem_z_K (hs : Std8 Ω K J S R T W z t) : T8.XMem Ω z K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  refine ⟨hK, ?_, R, Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1
      hs.hR.2.1, fun r hr => ?_⟩
  · exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  · have h := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]

theorem xMem_z_of_nbr (hs : Std8 Ω K J S R T W z t) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) : T8.XMem Ω z M := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨P, hP, hPz, hzN⟩ : ∃ P : Subgroup G, IsSylow2In P M ∧ (∀ r ∈ P, r * z = z * r) ∧
      z ∈ Subgroup.normalizer (M : Set G) := by
    obtain ⟨hLΩ, -, R₁, hR₁, hR₁L, hR₁N⟩ := hM
    have hsyl : IsSylow2In R₁ M := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ
        hLΩ hR₁ hR₁L
    have hRz : ∀ r ∈ R₁, r * z = z * r := fun r hr => by
      have h := hs.hz.conj_eq (n := r) (mem_normalizer_iff_conjSub_eq.mp (hR₁N hr))
      calc r * z = (r * z * r⁻¹) * r := by group
        _ = z * r := by rw [h]
    obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hLΩ
    have h8 := hΩ.eight_le_of_mem_RSet hR₁
    have huR : u ∈ R₁ := T3.mem_of_isPGroup hu hR₁L hsyl.2.1 (by omega)
    refine ⟨R₁, hsyl, hRz, ?_⟩
    have hzu : z ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hRz u huR).symm
    exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hLΩ (hnt M hLΩ) hu hzu
  exact ⟨hM.1, hzN, P, hP, hPz⟩

theorem omegaNbr_of_xMem_z (hs : Std8 Ω K J S R T W z t) {L : Subgroup G}
    (hL : T8.XMem Ω z L) (hne : L ≠ K) : L ∈ omegaNbr Ω K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hLΩ, -, P, hP, hPz⟩ := hL
  refine ⟨hLΩ, hne, P, mem_RSet_of_isSylow2In hLΩ hP, hP.1, fun r hr => ?_⟩
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz
    (Subgroup.mem_centralizer_singleton_iff.mpr (hPz r hr))

theorem z_mem_layerJoin_z (hs : Std8 Ω K J S R T W z t) : z ∈ Q3NL.exactLayer3 Ω z := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hK := xMem_z_K hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω z := hK.mem_tqMembers3 hΩ hz2
  have hRK : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ
      hs.stand.mem hs.hR.1 hs.hR.2.1
  have hRa : R ≤ T8.cenZ z := fun r hr => by
    rw [T8.mem_cenZ_iff]
    have h := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]
  have hL := Layer.isSylow2In_exactCore3_of_le_cenZ hRK hRa
  have h8 := hΩ.eight_le_of_mem_RSet hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRK.2.1 (by omega)
  exact Q3NL.exactCore3_le_exactLayer3 hKt (hL.1 hzR)

theorem layerImg_z_normal (hs : Std8 Ω K J S R T W z t) (g : Q3T7.layerQuot3 Ω z) :
    conjSub g (Layer.layerImg3 Ω z K) = Layer.layerImg3 Ω z K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hz2 : z * z = 1 := hs.hz.sq
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hzY := z_mem_layerJoin_z hs
  have hXK := xMem_z_K hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω z := hXK.mem_tqMembers3 hΩ hz2
  have hL : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hz2 ⟨K, hKt⟩
  have hLY : Q3NL.exactCore3 z K ≤ Q3NL.exactLayer3 Ω z := Q3NL.exactCore3_le_exactLayer3 hKt
  have huniq : IsUniqueInvolution (Layer.layerImg3 Ω z K) (T8V.layerMk z z hzY) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf (Layer.isUniqueInvolution_exactCore3 hKt.2.1 hs.hz) hLY)
  have hcen : ∀ g' : Q3T7.layerQuot3 Ω z, g' * T8V.layerMk z z hzY = T8V.layerMk z z hzY * g' := by
    intro g'
    obtain ⟨g'', rfl⟩ := QuotientGroup.mk_surjective g'
    have hg : (g'' : G) ∈ T8.cenZ z := Layer.exactLayer3_le_cenZ Ω z g''.2
    have hcz : (g'' : G) * z = z * g'' := T8.mem_cenZ_iff.mp hg
    have hc2 : g'' * (⟨z, hzY⟩ : ↥(Q3NL.exactLayer3 Ω z)) = ⟨z, hzY⟩ * g'' :=
      Subtype.ext (by simpa using hcz)
    change QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z)) g'' *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z)) ⟨z, hzY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z)) ⟨z, hzY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω z)) g''
    rw [← map_mul, ← map_mul, hc2]
  have hgz : g * T8V.layerMk z z hzY * g⁻¹ = T8V.layerMk z z hzY := by
    rw [hcen g]
    group
  have hnt' := Layer.noTwins_layerFam3 hL hnt
  have hkΨ := Layer.layerImg3_mem hKt
  have h1 := huniq.conj g
  rw [hgz] at h1
  exact hnt' _ hkΨ _ ⟨hL.quot.conjInvariant g _ hkΨ, _, huniq, h1⟩

theorem layerImg_nbr_ne_z (hs : Std8 Ω K J S R T W z t) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) :
    Layer.layerImg3 Ω z M ≠ Layer.layerImg3 Ω z K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hKt : K ∈ Q3NL.tqMembers3 Ω z := (xMem_z_K hs).mem_tqMembers3 hΩ hz2
  have hL : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hz2 ⟨K, hKt⟩
  obtain ⟨s, hs'⟩ := hΩ.exists_uniqueInvolution hM.1
  have hzs : z * s = s * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hM hs'
  exact Layer.layerImg3_ne_of_involutions hL (xMem_z_of_nbr hs hM) (xMem_z_K hs)
    hs' hs.hz hzs.symm (T8.ne_of_mem_omegaNbr hs.noTwins hM hs.hz hs').symm

end T8ZZ
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
open scoped commutatorElement
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_rep_le_cen_z (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    (i : Fin 4) : (F.ρ i).R ≤ T8.cenZ z := by
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.frame_rep_le_cen_zE c.toRepHooks F i

theorem frame_xMem_z (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    (i : Fin 4) : T8.XMem Ω z (F.ρ i).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.frame_xMem_zE hΩ.conjInvariant hnt c.comm_W F (fun j => frame_rep_le_cen_z hs F j) i

theorem frame_layerImg_ne_z (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    Layer.layerImg3 Ω z (F.ρ i).K ≠ Layer.layerImg3 Ω z (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hKt : (F.ρ 0).K ∈ Q3NL.tqMembers3 Ω z := (frame_xMem_z hs F 0).mem_tqMembers3 hΩ hz2
  have hL : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hz2 ⟨_, hKt⟩
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact Layer.layerImg3_ne_of_involutions hL (frame_xMem_z hs F i)
    (frame_xMem_z hs F j) (F.hz i) (F.hz j) (F.zz_comm c i j) (F.hinj i j hij)

theorem frame_layerImg_nbr_z (hs : Std8 Ω K J S R T W z t) (F : T8YY.FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    Layer.layerImg3 Ω z (F.ρ j).K ∈
      omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z (F.ρ i).K) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hPN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set G) := fun y hy =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (F.ρ i).hK (hnt _ (F.ρ i).hK)
      (F.hz i) (T8.rep_le_centralizer c (F.ρ j) (F.ρ i)
        (Or.inr (F.hadj j i (Ne.symm hij))) (F.hz i) hy)
  exact Layer.layerImg3_omegaNbr ((frame_xMem_z hs F i).mem_tqMembers3 hΩ hz2)
    ((frame_xMem_z hs F j).mem_tqMembers3 hΩ hz2) (F.ρ j).hRK (frame_rep_le_cen_z hs F j) hPN
    (frame_layerImg_ne_z hs F hij)

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem oddCore_z_commutes_nbr [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) {n : G}
    (hn : n ∈ oddCoreOf (Q3NL.exactLayer3 Ω z)) : n * s = s * n := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := T8YY.exists_fuzzyFrame hs hμ hnc
  have hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥ := by
    rw [(T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM
      hs.hJ).symm]
    exact hα
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.oddCore_z_commutes_nbrE hs.hz (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ z) hα' hn

theorem conjSub_eq_of_commute {Ω' : Set (Subgroup G)}
    (hnt : ∀ M ∈ Ω', ∀ M' ∈ twinSet Ω' M, M' = M) {M : Subgroup G} (hM : M ∈ Ω') {s : G}
    (hs : IsUniqueInvolution M s) {n : G} (hn : n * s = s * n) (hnΩ : conjSub n M ∈ Ω') :
    conjSub n M = M := by
  have h1 := hs.conj n
  have e : n * s * n⁻¹ = s := by
    rw [hn]
    group
  rw [e] at h1
  exact hnt M hM _ ⟨hnΩ, s, hs, h1⟩

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem eq_of_layerImg_eq_z [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup G} (hL : T8.XMem Ω z L)
    (h : Layer.layerImg3 Ω z L = Layer.layerImg3 Ω z (F.ρ j).K) : L = (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hz2 : z * z = 1 := hs.hz.sq
  have hKj : (F.ρ j).K ∈ Q3NL.tqMembers3 Ω z := (frame_xMem_z hs F j).mem_tqMembers3 hΩ hz2
  have hLt : L ∈ Q3NL.tqMembers3 Ω z := hL.mem_tqMembers3 hΩ hz2
  have hLH : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hz2 ⟨_, hKj⟩
  obtain ⟨n, hn, hnK⟩ := Layer.exists_oddCore_conj_of_layerImg3_eq hLH hKj hLt h.symm
  have hjK : (F.ρ j).K ∈ omegaNbr Ω K := by
    have := F.hadj 0 j (Ne.symm hj)
    rwa [F.h0] at this
  have hcomm := oddCore_z_commutes_nbr hs hμ hne hα hjK (F.hz j) hn
  have hΩn : conjSub n (F.ρ j).K ∈ Ω := hΩ.conjInvariant n _ (F.ρ j).hK
  have := conjSub_eq_of_commute hnt (F.ρ j).hK (F.hz j) hcomm hΩn
  rw [hnK] at this
  exact this
end T8ZZ
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
