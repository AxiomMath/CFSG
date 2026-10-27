module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmallDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRk2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerBase
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcLang
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcTw
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU1
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA (InnerOn)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem piCenterQuot_eq_one_iff {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (x : ↥L) :
    piCenterQuot θ x = 1 ↔ x ∈ Subgroup.center ↥L := by
  constructor
  · intro h
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = 1 :=
      θ.injective (by simpa [piCenterQuot] using h)
    exact (QuotientGroup.eq_one_iff x).1 h1
  · intro h
    change θ (QuotientGroup.mk x) = 1
    rw [(QuotientGroup.eq_one_iff x).2 h, map_one]

theorem centralizes_of_mem_gLAPPrimeCoreOf {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hdvd : p ∣ Nat.card ↥L) :
    GLAPPrimeCoreOf p L ≤ Subgroup.centralizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxL : x ∈ L := Subgroup.map_subtype_le (pPrimeCore p ↥L) hx
  haveI : Fact p.Prime := ⟨hp⟩
  have hOtop : GLAPPrimeCore p ↥L ≠ ⊤ := by
    intro htop
    have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) :=
      CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L)
    rw [htop, Subgroup.card_top] at hc
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hc hdvd)
  have hcenter : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq
      inferInstance hOtop
  have hx' : (⟨x, hxL⟩ : ↥L) ∈ GLAPPrimeCore p ↥L :=
    (Subgroup.mem_map_iff_mem L.subtype_injective).1 hx
  have hxc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := hcenter hx'
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩)

theorem exists_conj_of_inducesInnerMod {p : ℕ} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hO : GLAPPrimeCoreOf p L ≤ Subgroup.centralizer (L : Set G))
    (hin : InducesInnerMod p L g) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    ∃ r : R, LargeEvenInduces θ (conjRel g) (MulAut.conj r) := by
  obtain ⟨l, hlL, hl⟩ := hin
  let lL : ↥L := ⟨l, hlL⟩
  refine ⟨(θ (QuotientGroup.mk lL))⁻¹, ?_⟩
  intro y y' hyy'
  have hyL : (y : G) ∈ L := y.2
  have hy'L : (y' : G) ∈ L := y'.2
  have hmem : (l⁻¹ * (y : G) * l)⁻¹ * (g⁻¹ * (y : G) * g) ∈ GLAPPrimeCoreOf p L := hl y hyL
  have hoL : (l⁻¹ * (y : G) * l)⁻¹ * (g⁻¹ * (y : G) * g) ∈ L :=
    Subgroup.map_subtype_le (pPrimeCore p ↥L) hmem
  have hcent : (⟨(l⁻¹ * (y : G) * l)⁻¹ * (g⁻¹ * (y : G) * g), hoL⟩ : ↥L) ∈
      Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact hO hmem (w : G) w.2
  have hmk : (QuotientGroup.mk (⟨(l⁻¹ * (y : G) * l)⁻¹ * (g⁻¹ * (y : G) * g), hoL⟩ : ↥L) :
      ↥L ⧸ Subgroup.center ↥L) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hcent
  have hrel : (y' : G) = g⁻¹ * (y : G) * g := hyy'
  have hd : (QuotientGroup.mk y' : ↥L ⧸ Subgroup.center ↥L) =
      QuotientGroup.mk (⟨l⁻¹ * (y : G) * l,
        L.mul_mem (L.mul_mem (L.inv_mem hlL) hyL) hlL⟩ : ↥L) := by
    have h1 : (⟨(y' : G), hy'L⟩ : ↥L) = (⟨l⁻¹ * (y : G) * l,
        L.mul_mem (L.mul_mem (L.inv_mem hlL) hyL) hlL⟩ : ↥L) *
        (⟨(l⁻¹ * (y : G) * l)⁻¹ * (g⁻¹ * (y : G) * g), hoL⟩ : ↥L) := by
      apply Subtype.ext
      show (y' : G) = (l⁻¹ * (y : G) * l) * ((l⁻¹ * (y : G) * l)⁻¹ * (g⁻¹ * (y : G) * g))
      rw [hrel]
      group
    have := congrArg (QuotientGroup.mk (s := Subgroup.center ↥L)) h1
    simpa only [QuotientGroup.mk_mul, hmk, mul_one] using this
  have hθl : (θ (QuotientGroup.mk lL))⁻¹ = θ (QuotientGroup.mk lL⁻¹) := by
    simpa using (map_inv θ (QuotientGroup.mk lL)).symm
  have hcalc : MulAut.conj (θ (QuotientGroup.mk lL))⁻¹ (θ (QuotientGroup.mk y)) =
      θ (QuotientGroup.mk (⟨l⁻¹ * (y : G) * l,
        L.mul_mem (L.mul_mem (L.inv_mem hlL) hyL) hlL⟩ : ↥L)) := by
    rw [MulAut.conj_apply, hθl, ← map_mul, show (θ (QuotientGroup.mk lL⁻¹))⁻¹ =
      θ (QuotientGroup.mk lL) from by
        simpa using (map_inv θ (QuotientGroup.mk lL⁻¹)).symm, ← map_mul]
    congr 1
  rw [hcalc, hd]

theorem innerOn_iff_inv {J : Subgroup G} {b : G} :
    InnerOn J b ↔ ∃ a ∈ J, ∀ j ∈ J, b⁻¹ * j * b = a⁻¹ * j * a := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, fun j hj => ?_⟩
    have h1 := h (a⁻¹ * j * a) (J.mul_mem (J.mul_mem (J.inv_mem ha) hj) ha)
    have h1' : b * (a⁻¹ * j * a) * b⁻¹ = j := by
      rw [h1]
      group
    calc b⁻¹ * j * b = b⁻¹ * (b * (a⁻¹ * j * a) * b⁻¹) * b := by rw [h1']
      _ = a⁻¹ * j * a := by group
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun j hj => ?_⟩
    have h1 := h (c * j * c⁻¹) (J.mul_mem (J.mul_mem hc hj) (J.inv_mem hc))
    have h1' : b⁻¹ * (c * j * c⁻¹) * b = j := by
      rw [h1]
      group
    calc b * j * b⁻¹ = b * (b⁻¹ * (c * j * c⁻¹) * b) * b⁻¹ := by rw [h1']
      _ = c * j * c⁻¹ := by group

section Certificates


theorem reeF4CompInnerThree_holds : ReeF4CompInnerThree := by
  intro G _ _ p L J A d b hS hp3 hcat _ hin
  subst hp3
  have hJleL : J ≤ L := hS.comp.1.1.trans inf_le_left
  have hpJ : 3 ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hS.prime hS.pcomp
  have hpL : 3 ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hLperf : commutator ↥L = ⊤ := hS.qs.1
  have hLself : GLAPComponent 3 L L :=
    glaPComponent_self_of_dvd_card Nat.prime_three hS.qs hpL
  have hdInnDiag : InnDiagOn 3 (Subgroup.zpowers d) L :=
    S10.innDiagOn_of_inner hLself hS.qs
      (S171.innerDiagMarking_mono hS.idiag (Subgroup.zpowers_le.2 hS.d_mem))
  have hExcRk2 : catalogIs (PSimple 3 L) CFSG.LocalAnalysis.GLTheoremA.I167.ExcRk2Idx := by
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
  have hdInner : InducesInnerMod 3 L d :=
    CFSG.LocalAnalysis.GLTheoremA.I167.inducesInnerMod_of_rk2 Nat.prime_three
      (by norm_num) hS.qs hExcRk2 hdInnDiag
  have hO : GLAPPrimeCoreOf 3 L ≤ Subgroup.centralizer (L : Set G) :=
    centralizes_of_mem_gLAPPrimeCoreOf Nat.prime_three hS.qs hpL
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
    obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.S172A.pSimple_equiv_centerQuot hS.qs hpL
    have ePS' : PSimple 3 L ≃*
        (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.reeF4 k, hv⟩).Group := hdd ▸ ePS
    let θ : ↥L ⧸ Subgroup.center ↥L ≃*
        ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) := eP.trans (ePS'.trans eK)
    have hZ : Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) = ⊥ :=
      CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial k K hKcard
    obtain ⟨r_d, hind_d⟩ := exists_conj_of_inducesInnerMod hdN hO hdInner θ
    obtain ⟨r_b₀, hind_b₀⟩ := exists_conj_of_inducesInnerMod hbN hO hin θ
    have hind_b₀' : LargeEvenInduces θ
        (fun x x' : ↥L => (MulAut.conj b⁻¹) (x : G) = (x' : G)) (MulAut.conj r_b₀) := by
      intro x x' h
      refine hind_b₀ x x' ?_
      simpa [conjRel, MulAut.conj_apply] using h.symm
    obtain ⟨w, hwL, hw⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.l154_exists_conj_of_induces_inner hLperf
        (MulAut.conj b⁻¹) (fun x hx => by
          have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) x).mp hx
          simpa [MulAut.conj_apply] using h) θ r_b₀
        hind_b₀'
    let r_b : ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) :=
      piCenterQuot θ (⟨w, hwL⟩ : ↥L)
    have hind_b : LargeEvenInduces θ (conjRel b) (MulAut.conj r_b) := by
      intro x x' hxx'
      have h1 : b⁻¹ * (x : G) * b = w * (x : G) * w⁻¹ := by
        simpa [MulAut.conj_apply, inv_inv] using hw (x : G) x.2
      have hx' : w * (x : G) * w⁻¹ = (x' : G) := by rw [← h1, hxx']
      have hX : (⟨w, hwL⟩ : ↥L) * x * (⟨w, hwL⟩ : ↥L)⁻¹ = x' := by
        apply Subtype.ext
        simpa using hx'
      show MulAut.conj r_b (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk x')
      rw [MulAut.conj_apply]
      change (θ (QuotientGroup.mk (⟨w, hwL⟩ : ↥L))) * θ (QuotientGroup.mk x) *
        (θ (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)))⁻¹ = θ (QuotientGroup.mk x')
      rw [show (θ (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)))⁻¹ =
        θ (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)⁻¹) from by
          simpa using (map_inv θ (QuotientGroup.mk (⟨w, hwL⟩ : ↥L))).symm,
        ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hX]
    have hd3 : d ^ 3 = 1 := hS.elem.2 d hS.d_mem
    have hφd3 : (MulAut.conj r_d) ^ 3 = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_pow_eq_one hdN hind_d hd3
    have hrd3 : r_d ^ 3 = 1 := by
      have h1 : MulAut.conj (r_d ^ 3) = 1 := by
        rw [map_pow]
        exact hφd3
      have h2 : r_d ^ 3 ∈ Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) :=
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
    have hrd_ord : orderOf r_d = 3 := orderOf_eq_prime hrd3 hrd1
    have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
      (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
    have hdes := componentDescent_component θ hdN hind_d hJc
    have hJeq :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.component_eq_fixSubgroup_reeGamma_F4_kd264alg
        hm1 hKcard r_d hrd_ord
        (show CFSG.Open.IsComponentOf
        ((J.subgroupOf L).map (piCenterQuot θ))
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj r_d)) from
        (CFSG.Assembly.isComponentOf_iff_open).mp hdes)
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj r_d) =
        Subgroup.centralizer ({r_d} : Set ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) := by
      change CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
        (MulAut.conj r_d) = Subgroup.centralizer ({r_d} : Set _)
      exact CFSG.ClassicalInvolution.Generic.fixedSubgroup_conj_eq_centralizer r_d
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
    have hmemC : r_b ∈ Subgroup.centralizer ({r_d} :
        Set ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hrcomm
    have hJ' : (J.subgroupOf L).map (piCenterQuot θ) =
        Subgroup.centralizer ({r_d} : Set ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)) := by
      rw [hJeq, hfix]
    have hrbJ' : r_b ∈ (J.subgroupOf L).map (piCenterQuot θ) := by
      rw [hJ']
      exact hmemC
    obtain ⟨jL, hjL, hjLeq⟩ := Subgroup.mem_map.mp hrbJ'
    have hjLG : (jL : G) ∈ J := Subgroup.mem_subgroupOf.mp hjL
    have hcentW : (jL : ↥L)⁻¹ * (⟨w, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      have h1 : piCenterQuot θ (jL : ↥L) = piCenterQuot θ (⟨w, hwL⟩ : ↥L) := by
        rw [hjLeq]
      refine (piCenterQuot_eq_one_iff θ ((jL : ↥L)⁻¹ * ⟨w, hwL⟩)).1 ?_
      have h2 : piCenterQuot θ ((jL : ↥L)⁻¹ * ⟨w, hwL⟩) =
          (piCenterQuot θ (jL : ↥L))⁻¹ * piCenterQuot θ (⟨w, hwL⟩ : ↥L) := by
        rw [map_mul, map_inv]
      rw [h2, h1, inv_mul_cancel]
    have hwj : ∀ y ∈ J, b⁻¹ * y * b = (jL : G) * y * (jL : G)⁻¹ := by
      intro y hy
      have hyL : y ∈ L := hJleL hy
      have h1 : b⁻¹ * y * b = w * y * w⁻¹ := by
        simpa [MulAut.conj_apply, inv_inv] using hw y hyL
      set zG : G := (((jL : ↥L)⁻¹ * ⟨w, hwL⟩ : ↥L) : G) with hzG
      have hwval : w = (jL : G) * zG := by
        have h3 : (⟨w, hwL⟩ : ↥L) = jL * ((jL : ↥L)⁻¹ * ⟨w, hwL⟩) := by group
        have h4 := congrArg Subtype.val h3
        simpa [zG] using h4
      have hzc : zG * y = y * zG := by
        have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentW ⟨y, hyL⟩)
        exact h.symm
      calc b⁻¹ * y * b = w * y * w⁻¹ := h1
        _ = ((jL : G) * zG) * y * ((jL : G) * zG)⁻¹ := by rw [hwval]
        _ = (jL : G) * (zG * y * zG⁻¹) * (jL : G)⁻¹ := by group
        _ = (jL : G) * y * (jL : G)⁻¹ := by
            rw [show zG * y * zG⁻¹ = y from by
              rw [hzc, mul_assoc, mul_inv_cancel, mul_one]]
    have hInner' : ∃ a ∈ J, ∀ y ∈ J, b⁻¹ * y * b = a⁻¹ * y * a :=
      ⟨(jL : G)⁻¹, J.inv_mem hjLG, fun y hy => by simpa using hwj y hy⟩
    exact innDiagOn_of_innerOn_setup hS (innerOn_iff_inv.mpr hInner')
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
