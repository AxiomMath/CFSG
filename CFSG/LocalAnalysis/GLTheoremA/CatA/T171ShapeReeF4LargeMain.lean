module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4Large
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2Ambig
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4SLayer
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA (InnerOn)

open CFSG.ComponentClassification.PerfectAutomorphisms (hom_eq_id_of_central_displacement)

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L J : Subgroup G}

section Certificates


theorem innerOnCompNonShapeLarge_of_RF (hRF : LargeReeCentralizerActsInner) :
    ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
      Setup p L J A d b → 5 ≤ p → catalogIs (PSimple p L) (onLie ReeF4Idx) →
        ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b → InnerOn J b := by
  intro G _ _ p L J A d b hS hp5 hcat _hshape hin
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.odd
  have hp3 : 3 < p := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hJleL : J ≤ L := hS.comp.1.1.trans inf_le_left
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hS.prime hS.pcomp
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hLperf : commutator ↥L = ⊤ := hS.qs.1
  have hLself : GLAPComponent p L L :=
    glaPComponent_self_of_dvd_card hS.prime hS.qs hpL
  have hdInnDiag : InnDiagOn p (Subgroup.zpowers d) L :=
    S10.innDiagOn_of_inner hLself hS.qs
      (S171.innerDiagMarking_mono hS.idiag (Subgroup.zpowers_le.2 hS.d_mem))
  have hExcRk2 : catalogIs (PSimple p L) CFSG.LocalAnalysis.GLTheoremA.I167.ExcRk2Idx := by
    refine S10.catalogIs_imp (fun i hi => ?_) hcat
    cases i with
    | lie dd =>
      obtain ⟨k, hk⟩ := hi
      have hdd' : dd = (⟨TauCeti.LieTypeIndex.reeF4 k, by rw [← hk]; exact dd.2⟩ :
          TauCeti.ValidLieTypeIndex) := Subtype.ext hk
      rw [hdd']
      simp [CFSG.LocalAnalysis.GLTheoremA.I167.ExcRk2Idx, onLie]
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  have hdInner : InducesInnerMod p L d :=
    CFSG.LocalAnalysis.GLTheoremA.I167.inducesInnerMod_of_rk2 hp hp2 hS.qs hExcRk2 hdInnDiag
  have hO : GLAPPrimeCoreOf p L ≤ Subgroup.centralizer (L : Set G) :=
    centralizes_of_mem_gLAPPrimeCoreOf hp hS.qs hpL
  obtain ⟨i, hi, ⟨ePS⟩⟩ := hcat
  cases i with
  | lie dd =>
    obtain ⟨k, hk⟩ := hi
    have hv : (TauCeti.LieTypeIndex.reeF4 k).Valid := by rw [← hk]; exact dd.2
    have hdd : dd = (⟨TauCeti.LieTypeIndex.reeF4 k, hv⟩ : TauCeti.ValidLieTypeIndex) :=
      Subtype.ext hk
    have hm1 : 1 ≤ k :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
    obtain ⟨K, hfield, hfinite, hchar, hKcard, ⟨eK⟩⟩ :=
      CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm1 hR
    letI := hfield
    letI := hfinite
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
    haveI : Finite ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) := Subtype.finite
    obtain ⟨eP⟩ := pSimpleEquivCenterQuot_of_setup hS
    have ePS' : PSimple p L ≃*
        (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.reeF4 k, hv⟩).Group := hdd ▸ ePS
    let θ : ↥L ⧸ Subgroup.center ↥L ≃*
        ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) := eP.trans (ePS'.trans eK)
    have hZ : Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) = ⊥ :=
      CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial k K hKcard
    obtain ⟨r_d, hind_d⟩ := exists_conj_of_inducesInnerMod hdN hO hdInner θ
    obtain ⟨r_b, hind_b⟩ := exists_conj_of_inducesInnerMod hbN hO hin θ
    have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
    have hφdp : (MulAut.conj r_d) ^ p = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_pow_eq_one hdN hind_d hdp
    have hrdp : r_d ^ p = 1 := by
      have h1 : MulAut.conj (r_d ^ p) = 1 := by
        rw [map_pow]
        exact hφdp
      have h2 : r_d ^ p ∈
          Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) :=
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513Ns.conj_eq_one_iff_mem_center _).1 h1
      rwa [hZ, Subgroup.mem_bot] at h2
    have hrd1 : r_d ≠ 1 := by
      intro h1
      have hφ1 : (MulAut.conj r_d : MulAut ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) = 1 := by
        rw [h1, map_one]
      have hind1 : LargeEvenInduces θ (conjRel d)
          (1 : MulAut ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) := by
        rw [← hφ1]
        exact hind_d
      have hcent := exists_center_of_largeEvenInduces_one hdN hind1
      have hcentral : d ∈ Subgroup.centralizer (L : Set G) :=
        centralizes_of_conjRel_center hdN hcent ⟨hLperf⟩
      have hmem : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcentral⟩
      rw [hS.faithful] at hmem
      exact hS.d_ne (Subgroup.mem_bot.mp hmem)
    have hrd_ord : orderOf r_d = p := orderOf_eq_prime hrdp hrd1
    have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
      (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
    have hdes := componentDescent_component θ hdN hind_d hJc
    have hbd : b * d = d * b := by
      have h1 := hS.elem.1.is_comm.comm ⟨b, hS.b_mem⟩ ⟨d, hS.d_mem⟩
      exact congrArg Subtype.val h1
    have hcomm := largeEvenInduces_mul hbN hdN hbd hind_b hind_d
    have hcomm' := largeEvenInduces_mul hdN hbN hbd.symm hind_d hind_b
    rw [← hbd] at hcomm'
    have hφcomm : MulAut.conj r_b * MulAut.conj r_d =
        MulAut.conj r_d * MulAut.conj r_b :=
      largeEvenInduces_unique hcomm hcomm' (conjRel_total (Subgroup.mul_mem _ hbN hdN))
    have hconj : MulAut.conj (r_b * r_d) = MulAut.conj (r_d * r_b) := by
      simpa only [map_mul] using hφcomm
    have hrcomm : r_b * r_d = r_d * r_b :=
      CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hZ hconj
    have hrbC : r_b ∈ Subgroup.centralizer
        ({r_d} : Set ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hrcomm
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj r_d) =
        Subgroup.centralizer ({r_d} : Set ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) := by
      change CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
        (MulAut.conj r_d) = Subgroup.centralizer ({r_d} : Set _)
      exact CFSG.ClassicalInvolution.Generic.fixedSubgroup_conj_eq_centralizer r_d
    have hJmapComp : CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({r_d} : Set ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)))
        ((J.subgroupOf L).map (piCenterQuot θ)) := by
      rw [← hfix]
      exact CFSG.LocalAnalysis.GLTheoremA.LevelLieRF4SLayer.isComponentOf_rankThree_of_open
        ((CFSG.Assembly.isComponentOf_iff_open).1 hdes)
    obtain ⟨N, hNle, hN2, huniq, hNcomp, -⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.largeRee_component_chev
        (K := K) hm1 hKcard hp hp3 r_d hrd_ord
    obtain ⟨n, hnN, hact⟩ :=
      hRF k hv ⟨eK.symm⟩ hp hp3 r_d hrd_ord N hNle hN2 huniq hNcomp r_b hrbC
    have hNmap : N = (J.subgroupOf L).map (piCenterQuot θ) := (huniq _ hJmapComp).symm
    obtain ⟨jL, hjL, hjLeq⟩ := Subgroup.mem_map.mp (hNmap ▸ hnN)
    have hjLG : (jL : G) ∈ J := Subgroup.mem_subgroupOf.mp hjL
    let σb : MulAut ↥J :=
      J.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hS.b_norm⟩
    let σj : MulAut ↥J :=
      J.normalizerMonoidHom ⟨(jL : G), Subgroup.le_normalizer hjLG⟩
    have hσb_apply : ∀ y : ↥J, ((σb y : ↥J) : G) = b⁻¹ * (y : G) * b := by
      intro y
      show b⁻¹ * (y : G) * (b⁻¹)⁻¹ = b⁻¹ * (y : G) * b
      rw [inv_inv]
    have hσj_apply : ∀ y : ↥J, ((σj y : ↥J) : G) = (jL : G) * (y : G) * (jL : G)⁻¹ :=
      fun _ => rfl
    have hdisp : ∀ y : ↥J, y⁻¹ * ((σb * σj⁻¹) y) ∈ Subgroup.center ↥J := by
      intro y
      set w : ↥J := σj⁻¹ y with hw
      have hσjw : σj w = y := by
        rw [hw]
        exact MulEquiv.apply_symm_apply σj y
      let wL : ↥L := ⟨(w : G), hJleL w.2⟩
      have hwLJ : wL ∈ J.subgroupOf L := w.2
      have hbwL : b⁻¹ * (wL : G) * b ∈ L := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) (wL : G)).1 wL.2
      have hjwJmem : (jL : G) * (w : G) * (jL : G)⁻¹ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hjLG) (w : G)).1 w.2
        simpa using this
      have hjwL : (jL : G) * (wL : G) * (jL : G)⁻¹ ∈ L :=
        hJleL (by simpa using hjwJmem)
      have hbw : piCenterQuot θ ⟨b⁻¹ * (wL : G) * b, hbwL⟩ =
          r_b * piCenterQuot θ wL * r_b⁻¹ := by
        have h1 : MulAut.conj r_b (piCenterQuot θ wL) =
            piCenterQuot θ ⟨b⁻¹ * (wL : G) * b, hbwL⟩ := by
          have h2 := hind_b wL ⟨b⁻¹ * (wL : G) * b, hbwL⟩ (by rfl)
          exact h2
        rw [← h1, MulAut.conj_apply]
      have hjw : piCenterQuot θ ⟨(jL : G) * (wL : G) * (jL : G)⁻¹, hjwL⟩ =
          n * piCenterQuot θ wL * n⁻¹ := by
        have hcoe : (⟨(jL : G) * (wL : G) * (jL : G)⁻¹, hjwL⟩ : ↥L) =
            jL * wL * jL⁻¹ := by ext; rfl
        rw [hcoe, map_mul, map_mul, map_inv, hjLeq]
      have hpiw : piCenterQuot θ wL ∈ N := by
        rw [hNmap]
        exact Subgroup.mem_map_of_mem _ hwLJ
      have hpi_eq : piCenterQuot θ ⟨b⁻¹ * (wL : G) * b, hbwL⟩ =
          piCenterQuot θ ⟨(jL : G) * (wL : G) * (jL : G)⁻¹, hjwL⟩ := by
        rw [hbw, hjw, hact (piCenterQuot θ wL) hpiw]
      let zJ : ↥J := (σb w) * (σj w)⁻¹
      have hzJG : (zJ : G) = b⁻¹ * (wL : G) * b *
          ((jL : G) * (wL : G) * (jL : G)⁻¹)⁻¹ := by
        dsimp only [zJ]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hσb_apply w, hσj_apply w]
      have hzL : (⟨(zJ : G), hJleL zJ.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
        have heq : (⟨(zJ : G), hJleL zJ.2⟩ : ↥L) =
            (⟨b⁻¹ * (wL : G) * b, hbwL⟩ : ↥L) *
              (⟨(jL : G) * (wL : G) * (jL : G)⁻¹, hjwL⟩ : ↥L)⁻¹ :=
          Subtype.ext hzJG
        rw [heq]
        refine (piCenterQuot_eq_one_iff θ _).1 ?_
        rw [map_mul, map_inv, hpi_eq, mul_inv_cancel]
      have hcenterJ : zJ ∈ Subgroup.center ↥J := by
        rw [Subgroup.mem_center_iff]
        intro u
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 hzL (⟨(u : G), hJleL u.2⟩ : ↥L)
        exact congrArg (fun x : ↥L => (x : G)) hc
      have hzw : (σb w) * y⁻¹ ∈ Subgroup.center ↥J := by
        simpa [zJ, hσjw] using hcenterJ
      have hyz : y⁻¹ * σb w = σb w * y⁻¹ := by
        have hcomm := Subgroup.mem_center_iff.1 hzw y
        calc y⁻¹ * σb w = y⁻¹ * ((σb w * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (σb w * y⁻¹)) := by rw [hcomm]
          _ = σb w * y⁻¹ := by group
      rw [MulAut.mul_apply, hyz]
      exact hzw
    haveI : Group.IsPerfect ↥J := ⟨hS.comp.1.2.2.1⟩
    have hid := hom_eq_id_of_central_displacement (G := ↥J) (σb * σj⁻¹) hdisp
    have hσinv : (σb * σj⁻¹ : MulAut ↥J) = 1 := by
      ext z
      have hz : (σb * σj⁻¹) z = z := by
        have h := DFunLike.congr_fun hid z
        simpa using h
      simpa using hz
    have hσeq : σb = σj := by
      calc σb = σb * σj⁻¹ * σj := by group
        _ = 1 * σj := by rw [hσinv]
        _ = σj := one_mul _
    have hInner : ∃ a ∈ J, ∀ y ∈ J, b⁻¹ * y * b = a⁻¹ * y * a := by
      refine ⟨(jL : G)⁻¹, J.inv_mem hjLG, fun y hy => ?_⟩
      have h1 := congrArg (fun f : MulAut ↥J => ((f ⟨y, hy⟩ : ↥J) : G)) hσeq
      have h2 : ((σb ⟨y, hy⟩ : ↥J) : G) = b⁻¹ * y * b := hσb_apply ⟨y, hy⟩
      have h3 : ((σj ⟨y, hy⟩ : ↥J) : G) = (jL : G) * y * (jL : G)⁻¹ := hσj_apply ⟨y, hy⟩
      rw [h2, h3] at h1
      have h4 : ((jL : G)⁻¹)⁻¹ * y * ((jL : G)⁻¹) = (jL : G) * y * (jL : G)⁻¹ := by
        rw [inv_inv]
      rw [h4]
      exact h1
    exact innerOn_iff_inv.mpr hInner
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])

theorem reeF4CompInnerLarge_of_RF (hRF : LargeReeCentralizerActsInner) :
    ReeF4CompInnerLarge := by
  intro G _ _ p L J A d b hS hp5 hcat hshape hin
  exact innDiagOn_of_innerOn_setup hS
    (innerOnCompNonShapeLarge_of_RF hRF p L J A d b hS hp5 hcat hshape hin)

theorem reeF4CompInner_of_RF (hRF : LargeReeCentralizerActsInner) : ReeF4CompInner :=
  reeF4CompInner_of_large_of_three (reeF4CompInnerLarge_of_RF hRF) reeF4CompInnerThree_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
