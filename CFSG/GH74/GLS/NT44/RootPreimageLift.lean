module

public import CFSG.GH74.GLS.NT44.RigidActorClasses
public import CFSG.GH74.GLS.NT44.RootPreimage
import CFSG.GH74.GLS.NT44.ActualCover
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.GroupTheory.ComponentCovering
import CFSG.LocalAnalysis.OddStandard.Seitz77L34Inv
import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4
open CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PSL3Four

theorem exists_mem_rootX01_conj_of_sq_eq_one {y : S}
    (hy : y ^ 2 = 1) :
    ∃ c : S, y ∈ CFSG.ComponentClassification.GrSLit.GrS5.rootX01.map
      (MulAut.conj c).toMonoidHom := by
  rcases eq_or_ne y 1 with rfl | hy1
  · refine ⟨1, ?_⟩
    have hroot : (1 : S) ∈ CFSG.ComponentClassification.GrSLit.GrS5.rootX01 :=
      CFSG.ComponentClassification.GrSLit.GrS5.rootX01.one_mem
    have hm : MulAut.conj (1 : S) 1 ∈
        CFSG.ComponentClassification.GrSLit.GrS5.rootX01.map
          (MulAut.conj (1 : S)).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj (1 : S)).toMonoidHom hroot
    rw [show MulAut.conj (1 : S) 1 = 1 by simp] at hm
    exact hm
  · have hord : orderOf y = 2 := orderOf_eq_prime hy hy1
    have hconj : IsConj CFSG.OddStandard.Seitz77.L34.r₁S y :=
      CFSG.OddStandard.Seitz77.L34.isConj_r₁S_of_orderOf_eq_two hord
    let r : S := CFSG.ComponentClassification.GrSLit.GrS5.rhoS
      (CFSG.ComponentClassification.GrSLit.GrS5.x01S 1)
    have hr2 : r ^ 2 = 1 := by
      change (CFSG.ComponentClassification.GrSLit.GrS5.rhoS
        (CFSG.ComponentClassification.GrSLit.GrS5.x01S 1)) ^ 2 = 1
      rw [pow_two, CFSG.ComponentClassification.GrSLit.GrS5.rhoS_x01_mul,
        CharTwo.add_self_eq_zero,
        CFSG.ComponentClassification.GrSLit.GrS5.rhoS_x01_zero]
    have hr1 : r ≠ 1 := by
      change CFSG.ComponentClassification.GrSLit.GrS5.rhoS
        (CFSG.ComponentClassification.GrSLit.GrS5.x01S 1) ≠ 1
      exact CFSG.ComponentClassification.GrSLit.GrS5.rhoS_x01_ne_one one_ne_zero
    have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
    have hconj' : IsConj r y :=
      (IsConj.symm (CFSG.OddStandard.Seitz77.L34.isConj_r₁S_of_orderOf_eq_two hro)).trans
        hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj'
    refine ⟨c, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨r, ?_, ?_⟩
    · exact CFSG.ComponentClassification.GrSLit.GrS5.mem_rootX01.mpr ⟨1, rfl⟩
    · show MulAut.conj c r = y
      rw [MulAut.conj_apply]
      exact hc

theorem exists_root_preimage_kBar
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x) {q : kBar J}
    (hq : q ^ 2 ∈ Subgroup.center (kBar J)) :
    ∃ Y B : Subgroup (kBar J), q ∈ B ∧ Subgroup.center (kBar J) ≤ B ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Y ≤ B ∧
      Y ⊓ Subgroup.center (kBar J) = ⊥ ∧ Y ⊔ Subgroup.center (kBar J) = B ∧
      Nat.card Y = 4 ∧ ∀ a ∈ Y, a ^ 2 = 1 := by
  classical
  obtain ⟨eI⟩ := hJ.2
  have hfin : Finite fullQ := Finite.of_equiv (kBar J) eI.toEquiv
  have hqss : CFSG.IsQuasisimple fullQ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eI
      (TwoThin.isQuasisimple_hat (P92.rig_pcomp hJ))
  obtain ⟨b, lam, e, -, -, -, -, hqe, -, -, hqker, -⟩ :=
    @actualCoverOfL34 fullQ _ hfin hqss hL34 h16
  let qbar : fullQ →* S := b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center fullQ))
  let πJ : kBar J →* S := qbar.comp eI.toMonoidHom
  let ε : FullTwoCover ≃* kBar J := e.trans eI.symm
  let f : FullTwoCover →* kBar J := ε.toMonoidHom
  have hqbar_ker : qbar.ker = Subgroup.center fullQ := hqker
  have hqe' : qbar.comp e.toMonoidHom = fullTwoCoverToS := hqe
  have hf_center : Subgroup.map f (Subgroup.center FullTwoCover) = Subgroup.center (kBar J) :=
    Subgroup.map_center_eq ε
  have hf_inj : Function.Injective f := ε.injective
  have hπε : πJ.comp f = fullTwoCoverToS := by
    apply MonoidHom.ext
    intro x
    show qbar (eI (eI.symm (e x))) = fullTwoCoverToS x
    rw [MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun hqe' x
  have hcenter_ker : ∀ z ∈ Subgroup.center (kBar J), πJ z = 1 := by
    intro z hz
    have hmem : eI z ∈ qbar.ker := by
      rw [hqbar_ker, ← Subgroup.map_center_eq eI]
      exact Subgroup.mem_map_of_mem eI.toMonoidHom hz
    show qbar (eI z) = 1
    exact MonoidHom.mem_ker.mp hmem
  have hsq : πJ q ^ 2 = 1 := by
    simpa only [map_pow] using hcenter_ker (q ^ 2) hq
  obtain ⟨c, hc⟩ := exists_mem_rootX01_conj_of_sq_eq_one hsq
  let R : Subgroup S := CFSG.ComponentClassification.GrSLit.GrS5.rootX01.map
    (MulAut.conj c).toMonoidHom
  obtain ⟨Y₀, -, hY₀inf, hY₀sup, hY₀ea, hY₀card, he₀, -⟩ :=
    CFSG.GH74.GLS.NT44.exists_root_complement c
  let Y : Subgroup (kBar J) := Subgroup.map f Y₀
  let B : Subgroup (kBar J) := Subgroup.map f (Subgroup.comap fullTwoCoverToS R)
  have hY₀le : Y₀ ≤ R.comap fullTwoCoverToS := hY₀sup ▸ le_sup_left
  have hB_eq : B = R.comap πJ := by
    change Subgroup.map f (Subgroup.comap fullTwoCoverToS R) = R.comap πJ
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_comap]
      rw [show πJ (f y) = fullTwoCoverToS y from DFunLike.congr_fun hπε y]
      exact hy
    · intro hx
      rw [Subgroup.mem_comap] at hx
      refine Subgroup.mem_map.mpr ⟨ε.symm x, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have h1 : πJ x = fullTwoCoverToS (ε.symm x) := by
          calc πJ x = πJ (ε (ε.symm x)) := by rw [MulEquiv.apply_symm_apply]
            _ = fullTwoCoverToS (ε.symm x) := DFunLike.congr_fun hπε (ε.symm x)
        rw [← h1]
        exact hx
      · show f (ε.symm x) = x
        exact MulEquiv.apply_symm_apply ε x
  have hqB : q ∈ B := by
    rw [hB_eq, Subgroup.mem_comap]
    exact hc
  have hcenterB : Subgroup.center (kBar J) ≤ B := by
    intro z hz
    rw [hB_eq, Subgroup.mem_comap]
    rw [hcenter_ker z hz]
    exact R.one_mem
  have hYB : Y ≤ B := by
    change Subgroup.map f Y₀ ≤ Subgroup.map f (Subgroup.comap fullTwoCoverToS R)
    exact Subgroup.map_mono hY₀le
  have hYinf : Y ⊓ Subgroup.center (kBar J) = ⊥ := by
    change Subgroup.map f Y₀ ⊓ Subgroup.center (kBar J) = ⊥
    rw [← hf_center, ← Subgroup.map_inf Y₀ (Subgroup.center FullTwoCover) f hf_inj]
    rw [hY₀inf, Subgroup.map_bot]
  have hYsup : Y ⊔ Subgroup.center (kBar J) = B := by
    change Subgroup.map f Y₀ ⊔ Subgroup.center (kBar J) =
      Subgroup.map f (Subgroup.comap fullTwoCoverToS R)
    rw [← hf_center, ← Subgroup.map_sup Y₀ (Subgroup.center FullTwoCover) f, hY₀sup]
  have hYcard : Nat.card Y = 4 := by
    change Nat.card (Subgroup.map f Y₀) = 4
    rw [Subgroup.card_map_of_injective (f := f) hf_inj, hY₀card]
  have hYsq : ∀ a ∈ Y, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (show a ∈ Subgroup.map f Y₀ from ha)
    show f y ^ 2 = 1
    rw [← map_pow, hY₀ea.2 y hy, map_one]
  have hAcomm : IsMulCommutative ↥(R.comap fullTwoCoverToS) := by
    have : IsMulCommutative ↥Y₀ := hY₀ea.1
    refine IsMulCommutative.of_comm (fun a b => ?_)
    obtain ⟨a', rfl⟩ := he₀.surjective a
    obtain ⟨b', rfl⟩ := he₀.surjective b
    rw [← map_mul, ← map_mul]
    exact congrArg _ (mul_comm' a' b')
  have hBcommI : IsMulCommutative ↥B := by
    have : IsMulCommutative ↥(R.comap fullTwoCoverToS) := hAcomm
    refine IsMulCommutative.of_comm (fun a b => ?_)
    let eAB : ↥(R.comap fullTwoCoverToS) ≃* ↥B :=
      Subgroup.equivMapOfInjective (R.comap fullTwoCoverToS) f hf_inj
    obtain ⟨a', rfl⟩ := eAB.surjective a
    obtain ⟨b', rfl⟩ := eAB.surjective b
    rw [← map_mul, ← map_mul]
    exact congrArg _ (mul_comm' a' b')
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    have : IsMulCommutative ↥B := hBcommI
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)
  exact ⟨Y, B, hqB, hcenterB, hBcomm, hYB, hYinf, hYsup, hYcard, hYsq⟩

theorem exists_conj_eq_map_of_isPGroup_le_fixSubgroup {G : Type} [Group G] [Finite G]
    {x t : G} {J S : Subgroup G}
    (hJ : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) J) (ht2 : t ^ 2 = 1)
    (htN : t ∈ Subgroup.normalizer (J : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)))
    {B : Subgroup (kBar J)} (hB : IsPGroup 2 ↥B)
    (hBfix : B ≤ fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨t, htN⟩))) :
    ∃ f ∈ fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨t, htN⟩)),
      ∃ V : Subgroup ↥J, V.map J.subtype ≤ S ⊓ Subgroup.centralizer ({t} : Set G) ∧
        V ⊓ pPrimeCore 2 ↥J = ⊥ ∧
        V.map (QuotientGroup.mk' (pPrimeCore 2 ↥J)) = B.map (MulAut.conj f).toMonoidHom := by
  classical
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let Ct : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let D : Subgroup G := J ⊓ Ct
  let α : MulAut (kBar J) :=
    MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨t, htN⟩)
  let φ : ↥D →* kBar J :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp (Subgroup.inclusion (inf_le_left : D ≤ J))
  have hφrange : φ.range = fixSubgroup α :=
    range_inclusion_inf_centralizer_eq_fixSubgroup ht2 htN
  have hφker : ¬ 2 ∣ Nat.card ↥φ.ker :=
    not_two_dvd_card_ker_inclusion_inf_centralizer
  have hJsub : (J.subgroupOf Cx).IsSubnormal :=
    CFSG.GH74.Generic.BProg.B1.isSubnormal_of_isPCompIn hJ
  have hDsub_mathlib : (D.subgroupOf (Cx ⊓ Ct)).IsSubnormal := by
    have h := Subgroup.IsSubnormal.comap
      (Subgroup.inclusion (inf_le_left : Cx ⊓ Ct ≤ Cx)) hJsub
    rw [Subgroup.comap_inclusion_subgroupOf] at h
    have hsub_eq : D.subgroupOf (Cx ⊓ Ct) = J.subgroupOf (Cx ⊓ Ct) := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      rw [show D = J ⊓ Ct from rfl]
      constructor
      · intro hy
        exact hy.1
      · intro hy
        exact ⟨hy, y.2.2⟩
    rwa [hsub_eq]
  have hDsub_open : CFSG.Open.IsSubnormal D (Cx ⊓ Ct) := by
    have hDsub_assembly : CFSG.Assembly.IsSubnormal D (Cx ⊓ Ct) :=
      (CFSG.Assembly.IsSubnormal.iff_subgroupOf
        (inf_le_inf_right Ct hJ.1)).mpr hDsub_mathlib
    exact CFSG.Assembly.isSubnormal_iff_open.mp hDsub_assembly
  let T : Subgroup G := S ⊓ J ⊓ Ct
  have hTeq : (S ⊓ Ct) ⊓ (J ⊓ Ct) = T := by
    ext y
    simp only [T, Subgroup.mem_inf]
    tauto
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T D := by
    have h := hT.inf_of_isSubnormal hDsub_open
    rw [hTeq] at h
    simpa [D] using h
  let T_D : Subgroup ↥D := T.subgroupOf D
  have hTD : T ≤ D := inf_le_inf_right Ct inf_le_right
  have hmap_top : Subgroup.map D.subtype (⊤ : Subgroup ↥D) = D := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hT_D_sylow : CFSG.ABGLocalTools.IsSylowOf 2 T_D ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff D).mp ?_
    simpa [T_D, T, D, Subgroup.map_subgroupOf_eq_of_le hTD, hmap_top] using hT'
  have hTD_pgroup : IsPGroup 2 ↥T_D := by
    have hT_pgroup : IsPGroup 2 ↥T := hT'.isPGroup
    exact IsPGroup.of_equiv hT_pgroup (Subgroup.subgroupOfEquivOfLe hTD).symm
  have hφker_odd : Odd (Nat.card ↥φ.ker) :=
    Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp hφker)
  have hcop : Nat.Coprime (Nat.card ↥T_D) (Nat.card ↥φ.ker) := by
    obtain ⟨k, hk⟩ := hTD_pgroup.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k hφker_odd.coprime_two_left
  have hTD_inf_ker : T_D ⊓ φ.ker = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  let φ' : ↥D →* φ.range := φ.codRestrict φ.range (fun x => ⟨x, rfl⟩)
  have hφ'_surj : Function.Surjective φ' := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have hφ'_ker : φ'.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcomp : (φ.range).subtype.comp φ' = φ := by
    ext x
    rfl
  have hmap_range : Subgroup.map (φ.range).subtype (⊤ : Subgroup φ.range) = φ.range := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hT_φ_sylow : CFSG.ABGLocalTools.IsSylowOf 2 (T_D.map φ) φ.range := by
    have h := CFSG.isSylowOf_map_of_not_dvd_card_ker φ' hφ'_surj Nat.prime_two
      (by rwa [hφ'_ker]) hT_D_sylow
    rw [Subgroup.map_top_of_surjective φ' hφ'_surj] at h
    have h2 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff φ.range).mpr h
    rwa [Subgroup.map_map, hcomp, hmap_range] at h2
  have hB_le_range : B ≤ φ.range := by
    rw [hφrange]
    exact hBfix
  let B' : Subgroup φ.range := B.subgroupOf φ.range
  have hB'_pgroup : IsPGroup 2 B' :=
    IsPGroup.of_equiv hB (Subgroup.subgroupOfEquivOfLe hB_le_range).symm
  obtain ⟨B'', hB''⟩ := hB'_pgroup.exists_le_sylow
  have hB''_sylow : CFSG.ABGLocalTools.IsSylowOf 2
      ((B'' : Subgroup φ.range).map (φ.range).subtype) φ.range :=
    ⟨B'', rfl⟩
  obtain ⟨k, hk_range, hk⟩ :=
    CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hT_φ_sylow hB''_sylow
  let f : kBar J := k⁻¹
  have hf_fix : f ∈ fixSubgroup α := by
    rw [← hφrange]
    exact φ.range.inv_mem hk_range
  let S_B : Subgroup (kBar J) := B.map (MulAut.conj f).toMonoidHom
  have hS_B_le : S_B ≤ T_D.map φ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, hbB, hb_eq⟩
    have hbB' : (⟨b, hB_le_range hbB⟩ : φ.range) ∈ B' := by
      change (⟨b, hB_le_range hbB⟩ : φ.range) ∈ B.subgroupOf φ.range
      rw [Subgroup.mem_subgroupOf]
      exact hbB
    have hbB'' : (⟨b, hB_le_range hbB⟩ : φ.range) ∈ (B'' : Subgroup φ.range) :=
      hB'' hbB'
    have hb_image : b ∈ (B'' : Subgroup φ.range).map (φ.range).subtype :=
      Subgroup.mem_map_of_mem (φ.range).subtype hbB''
    have hk_b : k⁻¹ * b * k ∈ T_D.map φ := (hk b).mp hb_image
    rw [← hb_eq]
    change f * b * f⁻¹ ∈ T_D.map φ
    rw [show f * b * f⁻¹ = k⁻¹ * b * k by simp [f]]
    exact hk_b
  let V_D : Subgroup ↥D := S_B.comap φ ⊓ T_D
  have hV_D_le_T_D : V_D ≤ T_D := inf_le_right
  have hV_D_inf_ker : V_D ⊓ φ.ker = ⊥ := by
    change (S_B.comap φ ⊓ T_D) ⊓ φ.ker = ⊥
    rw [inf_assoc, hTD_inf_ker, inf_bot_eq]
  let V : Subgroup ↥J := V_D.map (Subgroup.inclusion (inf_le_left : D ≤ J))
  refine ⟨f, hf_fix, V, ?_, ?_, ?_⟩
  · have hV_subtype : V.map J.subtype = V_D.map D.subtype := by
      change (V_D.map (Subgroup.inclusion (inf_le_left : D ≤ J))).map J.subtype =
        V_D.map D.subtype
      rw [Subgroup.map_map]
      congr 1
    rw [hV_subtype]
    calc V_D.map D.subtype ≤ T_D.map D.subtype := Subgroup.map_mono hV_D_le_T_D
      _ = T := Subgroup.map_subgroupOf_eq_of_le hTD
      _ ≤ S ⊓ Ct := by
        intro y hy
        exact ⟨hy.1.1, hy.2⟩
  · have hφker_eq : φ.ker = (pPrimeCore 2 ↥J).comap
        (Subgroup.inclusion (inf_le_left : D ≤ J)) := by
      rw [show φ = (QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp
          (Subgroup.inclusion (inf_le_left : D ≤ J)) from rfl,
        ← MonoidHom.comap_ker (QuotientGroup.mk' (pPrimeCore 2 ↥J))
          (Subgroup.inclusion (inf_le_left : D ≤ J)),
        QuotientGroup.ker_mk']
    have hmap_inf := Subgroup.map_inf_eq V_D φ.ker
      (Subgroup.inclusion (inf_le_left : D ≤ J)) (Subgroup.inclusion_injective _)
    rw [hV_D_inf_ker, Subgroup.map_bot] at hmap_inf
    have hmap_comap : φ.ker.map (Subgroup.inclusion (inf_le_left : D ≤ J)) =
        (Subgroup.inclusion (inf_le_left : D ≤ J)).range ⊓ pPrimeCore 2 ↥J := by
      rw [hφker_eq, Subgroup.map_comap_eq]
    have hV_le_range : V ≤ (Subgroup.inclusion (inf_le_left : D ≤ J)).range :=
      Subgroup.map_le_range (Subgroup.inclusion (inf_le_left : D ≤ J)) V_D
    have hinf_eq : V ⊓ pPrimeCore 2 ↥J =
        V ⊓ ((Subgroup.inclusion (inf_le_left : D ≤ J)).range ⊓ pPrimeCore 2 ↥J) := by
      rw [← inf_assoc, inf_eq_left.mpr hV_le_range]
    rw [hinf_eq, ← hmap_comap]
    change (V_D.map (Subgroup.inclusion (inf_le_left : D ≤ J))) ⊓
      (φ.ker.map (Subgroup.inclusion (inf_le_left : D ≤ J))) = ⊥
    exact hmap_inf.symm
  · have hV_map_mk : V.map (QuotientGroup.mk' (pPrimeCore 2 ↥J)) = V_D.map φ := by
      change (V_D.map (Subgroup.inclusion (inf_le_left : D ≤ J))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥J)) = V_D.map φ
      rw [Subgroup.map_map]
    have hV_D_map_φ : V_D.map φ = S_B := by
      apply le_antisymm
      · rw [Subgroup.map_le_iff_le_comap]
        exact inf_le_left
      · intro x hx
        have hx' : x ∈ T_D.map φ := hS_B_le hx
        rcases Subgroup.mem_map.mp hx' with ⟨y, hy_T_D, hy_eq⟩
        have hy_comap : y ∈ S_B.comap φ := by
          rw [Subgroup.mem_comap]
          rwa [hy_eq]
        have hy_V_D : y ∈ V_D := Subgroup.mem_inf.mpr ⟨hy_comap, hy_T_D⟩
        rw [← hy_eq]
        exact Subgroup.mem_map_of_mem φ hy_V_D
    rw [hV_map_mk, hV_D_map_φ]

theorem exists_root_preimage_lift_of_inner_actor
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x t : G} {J S : Subgroup G} (hJ : J ∈ RigidSet fullQ x) (ht2 : t ^ 2 = 1)
    (htN : t ∈ Subgroup.normalizer (J : Set G))
    (htin : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨t, htN⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({x} : Set G)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G))) :
    ∃ V X : Subgroup G,
      V ≤ J ⊓ S ⊓ Subgroup.centralizer ({t} : Set G) ∧
      (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧
      S ⊓ zStar J ≤ V ∧
      X ≤ V ∧ X ⊓ zStar J = ⊥ ∧ Nat.card X = 4 ∧ (∀ a ∈ X, a ^ 2 = 1) ∧
      X ⊔ (S ⊓ zStar J) = V := by
  classical
  obtain ⟨q, hq⟩ := htin
  have hα2 : (MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨t, htN⟩)) ^ 2 = 1 := by
    have htN2 : (⟨t, htN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using ht2
    rw [← map_pow, ← map_pow, htN2, map_one, map_one]
  have hq2 : q ^ 2 ∈ Subgroup.center (kBar J) := by
    rw [← CFSG.GH74.GLS.Stage1.Thm4.Alt51.conj_eq_one_iff]
    rw [map_pow, hq]
    exact hα2
  obtain ⟨Y, B, hqB, hZB, hBcomm, hYB, hYinf, hYsup, hcardY, hYsq⟩ :=
    exists_root_preimage_kBar hL34 h16 hJ hq2
  have hBfix : B ≤ fixSubgroup (MulAut.mapQuotient (pPrimeCore 2 ↥J)
      (J.normalizerMonoidHom ⟨t, htN⟩)) := by
    intro b hb
    rw [mem_fixSubgroup, ← hq, MulAut.conj_apply]
    have hcomm : q * b = b * q := hBcomm q hqB b hb
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨eI⟩ := hJ.2
  have hcardZ : Nat.card (Subgroup.center (kBar J)) = 16 :=
    (Nat.card_congr (Subgroup.centerCongr eI).toEquiv).trans h16
  have hZ2 : IsPGroup 2 ↥(Subgroup.center (kBar J)) :=
    IsPGroup.of_card (n := 4) (by rw [hcardZ]; norm_num)
  have hY2 : IsPGroup 2 ↥Y :=
    P92.isPGroup_two_of_sq (fun a ha => by
      have := hYsq a ha
      simpa [pow_two] using this)
  have hB2 : IsPGroup 2 ↥B := by
    have h := hY2.to_sup_of_normal_right (p := 2) hZ2
    rwa [hYsup] at h
  obtain ⟨f, hf, V₀, hV₀S, hV₀bot, hV₀map⟩ :=
    exists_conj_eq_map_of_isPGroup_le_fixSubgroup (P92.rig_pcomp hJ) ht2 htN hT hB2 hBfix
  let mk : ↥J →* kBar J := QuotientGroup.mk' (pPrimeCore 2 ↥J)
  let e : kBar J ≃* kBar J := MulAut.conj f
  let B' : Subgroup (kBar J) := B.map e.toMonoidHom
  let Y' : Subgroup (kBar J) := Y.map e.toMonoidHom
  let V : Subgroup G := V₀.map J.subtype
  let X₀ : Subgroup ↥J := Y'.comap mk ⊓ V₀
  let X : Subgroup G := X₀.map J.subtype
  let W : Subgroup G := S ⊓ zStar J
  have hVJ : V ≤ J := Subgroup.map_subtype_le V₀
  have hVS : V ≤ S := hV₀S.trans inf_le_left
  have hVt : V ≤ Subgroup.centralizer ({t} : Set G) := hV₀S.trans inf_le_right
  have hV₀inj : ∀ a b : ↥J, a ∈ V₀ → b ∈ V₀ → mk a = mk b → a = b := by
    intro a b ha hb hab
    have hmem : a * b⁻¹ ∈ V₀ ⊓ pPrimeCore 2 ↥J := by
      refine Subgroup.mem_inf.mpr ⟨V₀.mul_mem ha (V₀.inv_mem hb), ?_⟩
      have h := QuotientGroup.eq_iff_div_mem.mp hab
      simpa [mk, div_eq_mul_inv] using h
    rw [hV₀bot] at hmem
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  have hB'comm : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hBcomm a₀ ha₀ b₀ hb₀]
  have hcenter_map : Subgroup.map e.toMonoidHom (Subgroup.center (kBar J)) =
      Subgroup.center (kBar J) :=
    Subgroup.map_center_eq e
  have hcenter_le_B' : Subgroup.center (kBar J) ≤ B' := by
    rw [← hcenter_map]
    exact Subgroup.map_mono hZB
  have hY'B' : Y' ≤ B' := Subgroup.map_mono hYB
  have hY'inf : Y' ⊓ Subgroup.center (kBar J) = ⊥ := by
    have h := Subgroup.map_inf Y (Subgroup.center (kBar J)) e.toMonoidHom e.injective
    rw [hYinf, Subgroup.map_bot, hcenter_map] at h
    exact h.symm
  have hY'sup : Y' ⊔ Subgroup.center (kBar J) = B' := by
    have h := Subgroup.map_sup Y (Subgroup.center (kBar J)) e.toMonoidHom
    rw [hYsup, hcenter_map] at h
    exact h.symm
  have hcardY' : Nat.card Y' = 4 := by
    change Nat.card (Y.map e.toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective e.injective, hcardY]
  have hY'sq : ∀ a ∈ Y', a ^ 2 = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow, hYsq y hy, map_one]
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have ha' : mk a₀ ∈ B' := by
      have h := Subgroup.mem_map_of_mem mk ha₀
      rwa [hV₀map] at h
    have hb' : mk b₀ ∈ B' := by
      have h := Subgroup.mem_map_of_mem mk hb₀
      rwa [hV₀map] at h
    have hab : a₀ * b₀ = b₀ * a₀ := by
      apply hV₀inj (a₀ * b₀) (b₀ * a₀) (V₀.mul_mem ha₀ hb₀) (V₀.mul_mem hb₀ ha₀)
      rw [map_mul, map_mul]
      exact hB'comm (mk a₀) ha' (mk b₀) hb'
    simpa using congrArg (fun x : ↥J => (x : G)) hab
  have hX₀V : X₀ ≤ V₀ := inf_le_right
  have hX₀map : X₀.map mk = Y' := by
    apply le_antisymm
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      exact ha.1
    · intro y hy
      have hy' : y ∈ V₀.map mk := by
        rw [hV₀map]
        exact hY'B' hy
      obtain ⟨a, ha, ham⟩ := Subgroup.mem_map.mp hy'
      exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_comap.mpr (by rw [ham]; exact hy), ha⟩, ham⟩
  have hXcard : Nat.card X = 4 := by
    have hcardX₀ : Nat.card X₀ = Nat.card Y' := by
      apply Nat.card_eq_of_bijective
        (fun x : ↥X₀ => (⟨mk (x : ↥J), Subgroup.mem_comap.mp x.2.1⟩ : ↥Y'))
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply hV₀inj _ _ (hX₀V x.2) (hX₀V y.2)
        exact congrArg (fun z : ↥Y' => (z : kBar J)) hxy
      · intro y
        have hy : (y : kBar J) ∈ X₀.map mk := by rw [hX₀map]; exact y.2
        obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨x, hx⟩, Subtype.ext hxm⟩
    change Nat.card (X₀.map J.subtype) = 4
    rw [Subgroup.card_map_of_injective J.subtype_injective, hcardX₀, hcardY']
  have hX₀bot : X₀ ⊓ pPrimeCore 2 ↥J = ⊥ := by
    change (Y'.comap mk ⊓ V₀) ⊓ pPrimeCore 2 ↥J = ⊥
    rw [inf_assoc, hV₀bot, inf_bot_eq]
  have hXinf : X ⊓ zStar J = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx.1
    have hx₀mk : mk x₀ ∈ Y' := hx₀.1
    have hcent : mk x₀ ∈ Subgroup.center (kBar J) :=
      (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
        (K := J) x₀).mp hx.2
    have hbot : mk x₀ ∈ Y' ⊓ Subgroup.center (kBar J) := ⟨hx₀mk, hcent⟩
    rw [hY'inf] at hbot
    have h1 : mk x₀ = 1 := Subgroup.mem_bot.mp hbot
    have hx₀ker : x₀ ∈ pPrimeCore 2 ↥J := by
      have := MonoidHom.mem_ker.mpr h1
      simpa only [mk, QuotientGroup.ker_mk'] using this
    have h2 : x₀ ∈ X₀ ⊓ pPrimeCore 2 ↥J := ⟨hx₀, hx₀ker⟩
    rw [hX₀bot] at h2
    have h3 : x₀ = 1 := Subgroup.mem_bot.mp h2
    rw [Subgroup.mem_bot]
    simpa using congrArg (fun z : ↥J => (z : G)) h3
  have hXsq : ∀ a ∈ X, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have ha'mk : mk a₀ ∈ Y' := ha₀.1
    have hsq : mk (a₀ ^ 2) = 1 := by
      rw [map_pow, hY'sq (mk a₀) ha'mk]
    have hker : a₀ ^ 2 ∈ pPrimeCore 2 ↥J := by
      have := MonoidHom.mem_ker.mpr hsq
      simpa only [mk, QuotientGroup.ker_mk'] using this
    have hmem : a₀ ^ 2 ∈ X₀ ⊓ pPrimeCore 2 ↥J := ⟨X₀.pow_mem ha₀ 2, hker⟩
    rw [hX₀bot] at hmem
    have h3 : a₀ ^ 2 = 1 := Subgroup.mem_bot.mp hmem
    show (a₀ : G) ^ 2 = 1
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  have hWle : S ⊓ zStar J ≤ V := by
    intro w hw
    have hwJ : w ∈ J := hw.2.1
    have hwcent : mk ⟨w, hwJ⟩ ∈ Subgroup.center (kBar J) :=
      (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
        (K := J) ⟨w, hwJ⟩).mp (by simpa using hw.2)
    have hbV : mk ⟨w, hwJ⟩ ∈ V₀.map mk := by
      rw [hV₀map]
      exact hcenter_le_B' hwcent
    obtain ⟨v, hvV₀, hvmk⟩ := Subgroup.mem_map.mp hbV
    have hvV : (v : G) ∈ V := Subgroup.mem_map_of_mem J.subtype hvV₀
    have hvZ : (v : G) ∈ zStar J :=
      (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
        (K := J) v).mpr (by rw [hvmk]; exact hwcent)
    have hvW : (v : G) ∈ S ⊓ zStar J := ⟨hVS hvV, hvZ⟩
    have hwW : w ∈ S ⊓ zStar J := hw
    have heq : w = (v : G) := by
      refine CFSG.GH74.GLS.Stage1.Thm2.Recip.eq_of_hatMk_eq
        (K := J) (S := S ⊓ zStar J) ?_ (hS.isPGroup.to_le inf_le_left) hwW hvW ?_
      · intro z hz
        exact hz.2.1
      · show mk ⟨w, hwJ⟩ = mk v
        exact hvmk.symm
    rw [heq]
    exact hvV
  have hWsup : X ⊔ W = V := by
    apply le_antisymm
    · exact sup_le (Subgroup.map_mono hX₀V) hWle
    · intro v hv
      obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
      have hbV : mk v₀ ∈ V₀.map mk := Subgroup.mem_map_of_mem mk hv₀
      rw [hV₀map] at hbV
      have hmem : mk v₀ ∈ Y' ⊔ Subgroup.center (kBar J) := by
        rw [hY'sup]
        exact hbV
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
      have hyX : y ∈ X₀.map mk := by rw [hX₀map]; exact hy
      obtain ⟨x₀, hx₀, hx₀mk⟩ := Subgroup.mem_map.mp hyX
      have hzB' : z ∈ V₀.map mk := by
        rw [hV₀map]
        exact hcenter_le_B' hz
      obtain ⟨w₀, hw₀V₀, hw₀mk⟩ := Subgroup.mem_map.mp hzB'
      have hw₀Z : (w₀ : G) ∈ zStar J :=
        (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
          (K := J) w₀).mpr (by rw [hw₀mk]; exact hz)
      have hw₀W : (w₀ : G) ∈ W :=
        ⟨hVS (Subgroup.mem_map_of_mem J.subtype hw₀V₀), hw₀Z⟩
      have hmul : x₀ * w₀ = v₀ := by
        apply hV₀inj (x₀ * w₀) v₀ (V₀.mul_mem (hX₀V hx₀) hw₀V₀) hv₀
        rw [map_mul, hx₀mk, hw₀mk]
        exact hyz
      show (v₀ : G) ∈ X ⊔ W
      rw [show (v₀ : G) = (x₀ : G) * (w₀ : G) by
        rw [← hmul]
        rfl]
      exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem J.subtype hx₀) hw₀W
  refine ⟨V, X, ?_, hVcomm, hWle, Subgroup.map_mono hX₀V, hXinf, hXcard, hXsq, hWsup⟩
  intro a ha
  exact ⟨⟨hVJ ha, hVS ha⟩, hVt ha⟩

end CFSG.GH74.GLS.NT44

end
