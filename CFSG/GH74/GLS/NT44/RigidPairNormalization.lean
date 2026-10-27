module

public import CFSG.GH74.GLS.NT44.RigidPairOddIntersection
public import CFSG.LocalAnalysis.StandardType.GGPumpupQuot
public import CFSG.GH74.GLS.NT44.RigidCenterSylowEquiv
import CFSG.GH74.GLS.NT44.RigidDiagonalAction
import CFSG.GH74.GLS.NT44.RigidCenterCommutators
import CFSG.GH74.GLS.NT44.RigidCenterInclusion
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Bg.Pu5.BalABasic
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import TauCeti.GroupTheory.PGroup
import CFSG.GroupTheory.InversionFourSubgroup
import CFSG.GH74.GLS.NT44.RigidPump
import CFSG.GH74.GLS.C3.Layer1.Th2Pump
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.C3.Layer1.BkIv81Core
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section
set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

private theorem rigidPair_literalMap_injective {G : Type} [Group G]
    {D L : Subgroup G}
    (hstab : ∀ d ∈ D, d ∈ Subgroup.normalizer (L : Set G) → d = 1) :
    Function.Injective
      (fun d : D => L.map (MulAut.conj (d : G)).toMonoidHom) := by
  intro d1 d2 hEq
  change L.map (MulAut.conj (d1 : G)).toMonoidHom =
    L.map (MulAut.conj (d2 : G)).toMonoidHom at hEq
  have hqD : (d2 : G)⁻¹ * (d1 : G) ∈ D :=
    D.mul_mem (D.inv_mem d2.2) d1.2
  have hqMap : L.map (MulAut.conj ((d2 : G)⁻¹ * (d1 : G))).toMonoidHom = L := by
    calc
      L.map (MulAut.conj ((d2 : G)⁻¹ * (d1 : G))).toMonoidHom =
          (L.map (MulAut.conj (d1 : G)).toMonoidHom).map
            (MulAut.conj (d2 : G)⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext z
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        group
      _ = (L.map (MulAut.conj (d2 : G)).toMonoidHom).map
            (MulAut.conj (d2 : G)⁻¹).toMonoidHom := by rw [hEq]
      _ = L := by
        rw [Subgroup.map_map]
        have hcancel : (MulAut.conj (d2 : G)⁻¹).toMonoidHom.comp
            (MulAut.conj (d2 : G)).toMonoidHom = MonoidHom.id G := by
          ext z
          simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
            MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [hcancel, Subgroup.map_id]
  have hq : (d2 : G)⁻¹ * (d1 : G) = 1 :=
    hstab _ hqD (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hqMap)
  apply Subtype.ext
  calc
    (d1 : G) = (d2 : G) * ((d2 : G)⁻¹ * (d1 : G)) := by group
    _ = (d2 : G) := by rw [hq]; exact mul_one _

private theorem rigidPair_literalMap_card_le_two {G : Type} [Group G]
    {D L P : Subgroup G} (hLP : L ≠ P)
    (hpair : ∀ d : D, L.map (MulAut.conj (d : G)).toMonoidHom = L ∨
      L.map (MulAut.conj (d : G)).toMonoidHom = P)
    (hinj : Function.Injective
      (fun d : D => L.map (MulAut.conj (d : G)).toMonoidHom)) :
    Nat.card D ≤ 2 := by
  let f : D → ↥({L, P} : Set (Subgroup G)) := fun d =>
    ⟨L.map (MulAut.conj (d : G)).toMonoidHom, by
      change L.map (MulAut.conj (d : G)).toMonoidHom = L ∨
        L.map (MulAut.conj (d : G)).toMonoidHom = P
      exact hpair d⟩
  have hf : Function.Injective f := by
    intro d1 d2 h
    exact hinj (congrArg Subtype.val h)
  have hcard : Nat.card ↥({L, P} : Set (Subgroup G)) = 2 := by
    change ({L, P} : Set (Subgroup G)).ncard = 2
    exact Set.ncard_pair hLP
  exact (Nat.card_le_card_of_injective f hf).trans_eq hcard

private theorem normalizes_of_rigid_pair_odd_intersection
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x v : G} {J L : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x)
    (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hL : L ∈ RigidSet fullQ v)
    (hL34 : IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16)
    (hodd : Odd (Nat.card ↥(CxK x J ⊓ CxK v L))) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  classical
  by_contra hxN
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvv : v * v = 1 := by
    simpa only [hv2, pow_two] using pow_orderOf_eq_one v
  have hvCx : v ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvx
  have hzv2 : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    IsPGroup.of_card (p := 2) (G := Subgroup.zpowers v) (n := 1) (by
      rw [Nat.card_zpowers, hv2]; norm_num)
  obtain ⟨S, hS, hzS⟩ :=
    P92.exists_sylow_ge (C := centralizer ({x} : Set G))
      (S := Subgroup.zpowers v) hzv2 (Subgroup.zpowers_le.mpr hvCx)
  let W : Subgroup G := S ⊓ zStar J
  have hvS : v ∈ S := hzS (Subgroup.mem_zpowers v)
  have hNW : v ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hvS, Alt51.mem_normalizer_zStar hvN⟩
  obtain ⟨eZ, e4, _heZ⟩ :=
    exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS hL34 h16
  have hWeq : Nonempty (↥W ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
    ⟨eZ.trans e4⟩
  let D : Subgroup G := W ⊓ centralizer ({v} : Set G)
  have h4D : 4 ≤ Nat.card D := by
    simpa only [D] using CFSG.four_le_card_inf_centralizer_of_c4_prod_c4 hWeq hvv hNW
  have hLv : IsPCompIn 2 (centralizer ({v} : Set G)) L := P92.rig_pcomp hL
  have hdiag : IDiag x L ≤ pLayerOf 2 (centralizer ({x} : Set G)) := by
    apply CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hv2
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hvx
    · exact CFSG.GH74.GLS.Bg.Pu5.BalA.IG_i_gen hx2 hvx hLv hxN
  have hrawAll : ∀ d : D, ∀ l ∈ IDiag x L,
      ⁅l, (d : G)⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
    intro d l hl
    exact commutator_mem_of_mem_zStar_kz
      (zStar_le_zStar_kz_of_mem_rigidSet hJ d.2.1.2) l (hdiag hl)
  have hpairAll : ∀ d : D,
      L.map (MulAut.conj (d : G)).toMonoidHom = L ∨
        L.map (MulAut.conj (d : G)).toMonoidHom =
          L.map (MulAut.conj x).toMonoidHom := by
    intro d
    obtain ⟨_, hpair, _⟩ :=
      normalizes_pair_and_centralizes_sections_of_odd_diagonal_commutators
        hx2 hvx hLv hxN d.2.2 (hS.le d.2.1.1) (hrawAll d)
    exact hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hstab_section : ∀ d : D,
      (d : G) ∈ Subgroup.normalizer (L : Set G) →
        (d : G) ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
    intro d hdNL
    obtain ⟨_, _, hstab⟩ :=
      normalizes_pair_and_centralizes_sections_of_odd_diagonal_commutators
        hx2 hvx hLv hxN d.2.2 (hS.le d.2.1.1) (hrawAll d)
    exact (hstab hdNL).1
  let H : Subgroup G := CxK x J ⊓ CxK v L
  have hHodd : Odd (Nat.card H) := by
    simpa only [H] using hodd
  have hstab_trivial : ∀ d : D,
      (d : G) ∈ Subgroup.normalizer (L : Set G) → (d : G) = 1 := by
    intro d hdNL
    have hdH : (d : G) ∈ H :=
      ⟨⟨hS.le d.2.1.1, d.2.1.2.2⟩, ⟨d.2.2, hstab_section d hdNL⟩⟩
    have hdS : (d : G) ∈ S := d.2.1.1
    have hdisj : Disjoint H S :=
      TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup (p := 2) (C := H) (Q := S)
        hHodd.not_two_dvd_nat hS.isPGroup
    exact Subgroup.disjoint_def.mp hdisj hdH hdS
  have hLP : L ≠ L.map (MulAut.conj x).toMonoidHom := by
    intro h
    exact hxN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hinj : Function.Injective
      (fun d : D => L.map (MulAut.conj (d : G)).toMonoidHom) :=
    rigidPair_literalMap_injective
      (D := D) (L := L) (fun d hd hdNL => hstab_trivial ⟨d, hd⟩ hdNL)
  have hcard2 : Nat.card D ≤ 2 :=
    rigidPair_literalMap_card_le_two hLP hpairAll hinj
  omega

theorem normalizes_rigid_families_of_rigid_actor :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)),
  (∀ I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x,
    v ∈ Subgroup.normalizer (I : Set G)) ∧
  (∀ L ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ v,
    x ∈ Subgroup.normalizer (L : Set G)) := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax
  classical
  have oddAt : ∀ (I : Subgroup G), I ∈ RigidSet fullQ x →
      ∀ (L : Subgroup G), L ∈ RigidSet fullQ v →
        Odd (Nat.card ↥(CxK x I ⊓ CxK v L)) := by
    intro I hI L hL
    exact odd_card_cxK_inf_cxK_of_rigid_actor
      hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax I hI L hL
  have hOpp : ∀ L ∈ RigidSet fullQ v, x ∈ normalizer (L : Set G) := by
    intro L hL
    exact @normalizes_of_rigid_pair_odd_intersection
      G instG instFinite fullQ instFullQ
      x v J L hx2 hv2 hvx hJ hvN hL hL34 h16 (oddAt J hJ L hL)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  let L0 : Subgroup G := J.map (MulAut.conj g).toMonoidHom
  have hL0 : L0 ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj (Q := fullQ) hJ g
    simpa only [hg, L0, CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap, RigidSet,
      Set.mem_setOf_eq] using h
  constructor
  ·
    intro I hI
    exact @normalizes_of_rigid_pair_odd_intersection
      G instG instFinite fullQ instFullQ
      v x L0 I hv2 hx2 hvx.symm hL0 (hOpp L0 hL0) hI hL34 h16
      (by simpa only [inf_comm] using oddAt I hI L0 hL0)
  · exact hOpp

private theorem rigidPair_inf_zStar_le_centralizer {G : Type} [Group G] [Finite G]
    {x u : G} {S I : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({x} : Set G)))
    (huS : u ∈ S)
    (huSection : u ∈ centralizerSection I (pPrimeCoreOf 2 I)) :
    S ⊓ zStar I ≤ Subgroup.centralizer ({u} : Set G) := by
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec hS.isPGroup hw.1 huS hw.2.1 huSection)

private theorem rigidPair_inf_zStar_le_zStar_kz_of_pump {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {fullQ : Type} [Group fullQ]
    {x u : G} {S I : Subgroup G} (hx2 : orderOf x = 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({x} : Set G)))
    (hI : I ∈ RigidSet fullQ x)
    (hu2 : orderOf u = 2) (huS : u ∈ S)
    (huSection : u ∈ centralizerSection I (pPrimeCoreOf 2 I)) :
    (∃ M : Subgroup G, PumpUpLT 2 x I u M) ∧
      S ⊓ zStar I ≤ zStar (Kz fullQ u) := by
  have hIc : IsPCompIn 2 (centralizer ({x} : Set G)) I := hI.1.1.2.2
  have hIil : IsILo 2 x I := hI.1.1
  have h3x : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by
    have h2 : oBound 2 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := hIil.2.1
    have h3' : oBound 2 = 3 := by simp [oBound]
    exact h3' ▸ h2
  have h3 : 3 ≤ pRank 2 G :=
    h3x.trans (CFSG.GH74.GLS.Bg.pRank_subgroup_le (by norm_num)
      (centralizer ({x} : Set G)))
  have hRu : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    CFSG.GH74.GLS.TwoThin.rankThreeCentralizers G (inferInstance : IsSimpleGroup G)
      hnonab h3 u hu2
  obtain ⟨M, hM⟩ := CFSG.GH74.GLS.TwoThin.exists_pumpup_of_involution hx2 hu2 hIc
    (hS.le huS) huSection hIil hRu
  refine ⟨⟨M, hM⟩, fun w hw => ?_⟩
  obtain ⟨n, hn⟩ := hS.isPGroup ⟨w, hw.1⟩
  exact mem_zStar_kz_of_pumpUpLT hI hM hw.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
    (rigidPair_inf_zStar_le_centralizer hS huS huSection hw)

theorem normalizes_rigid_family_of_centralizing_involution :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (S : Subgroup G)
    (_hS : CFSG.ABGLocalTools.IsSylowOf 2 S
      (Subgroup.centralizer ({x} : Set G)))
    (_hvS : v ∈ S)
    (I : Subgroup G)
    (_hI : I ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (u : G) (_hu2 : orderOf u = 2) (_huS : u ∈ S)
    (_huv : u ∈ Subgroup.centralizer ({v} : Set G))
    (_huSection : u ∈ CFSG.GH74.GLS.centralizerSection I
      (CFSG.GH74.GLS.pPrimeCoreOf 2 I))
    (L : Subgroup G)
    (_hL : L ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ v),
  u ∈ Subgroup.normalizer (L : Set G) := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax S hS hvS I hI u hu2 huS huv huSection L hL
  classical
  by_contra huN
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvNI : v ∈ normalizer (I : Set G) :=
    (normalizes_rigid_families_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
      hJ hvN hvact hxP hmax).1 I hI
  have hvv : v * v = 1 := by
    simpa only [hv2, pow_two] using pow_orderOf_eq_one v
  let W : Subgroup G := S ⊓ zStar I
  have hNW : v ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hvS, Alt51.mem_normalizer_zStar hvNI⟩
  have hWu : W ≤ centralizer ({u} : Set G) :=
    rigidPair_inf_zStar_le_centralizer hS huS huSection
  obtain ⟨eZ, e4, _heZ⟩ :=
    exists_rigid_center_sylow_equiv_of_center_card_sixteen hI hS hL34 h16
  have hWeq : Nonempty (↥W ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
    ⟨eZ.trans e4⟩
  let D : Subgroup G := W ⊓ centralizer ({v} : Set G)
  have h4D : 4 ≤ Nat.card D := by
    simpa only [D] using CFSG.four_le_card_inf_centralizer_of_c4_prod_c4 hWeq hvv hNW
  have hWZu : W ≤ zStar (Kz fullQ u) :=
    (rigidPair_inf_zStar_le_zStar_kz_of_pump hnonab hx2 hS hI hu2 huS huSection).2
  have hLv : IsPCompIn 2 (centralizer ({v} : Set G)) L := P92.rig_pcomp hL
  have hvu : v * u = u * v := (Subgroup.mem_centralizer_singleton_iff.mp huv).symm
  have hdiag : IDiag u L ≤ pLayerOf 2 (centralizer ({u} : Set G)) := by
    apply CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hv2
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hvu
    · exact CFSG.GH74.GLS.Bg.Pu5.BalA.IG_i_gen hu2 hvu hLv huN
  have hrawAll : ∀ d : D, ∀ l ∈ IDiag u L,
      ⁅l, (d : G)⁆ ∈ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
    intro d l hl
    exact commutator_mem_of_mem_zStar_kz (hWZu d.2.1) l (hdiag hl)
  have hpairAll : ∀ d : D,
      L.map (MulAut.conj (d : G)).toMonoidHom = L ∨
        L.map (MulAut.conj (d : G)).toMonoidHom =
          L.map (MulAut.conj u).toMonoidHom := by
    intro d
    obtain ⟨_, hpair, _⟩ :=
      normalizes_pair_and_centralizes_sections_of_odd_diagonal_commutators
        hu2 hvu hLv huN d.2.2 (hWu d.2.1) (hrawAll d)
    exact hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hstab_section : ∀ d : D,
      (d : G) ∈ Subgroup.normalizer (L : Set G) →
        (d : G) ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
    intro d hdNL
    obtain ⟨_, _, hstab⟩ :=
      normalizes_pair_and_centralizes_sections_of_odd_diagonal_commutators
        hu2 hvu hLv huN d.2.2 (hWu d.2.1) (hrawAll d)
    exact (hstab hdNL).1
  let H : Subgroup G := CxK x I ⊓ CxK v L
  have hHodd : Odd (Nat.card H) :=
    odd_card_cxK_inf_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
      hvact hxP hmax I hI L hL
  have hstab_trivial : ∀ d : D,
      (d : G) ∈ Subgroup.normalizer (L : Set G) → (d : G) = 1 := by
    intro d hdNL
    have hdH : (d : G) ∈ H :=
      ⟨⟨hS.le d.2.1.1, d.2.1.2.2⟩, ⟨d.2.2, hstab_section d hdNL⟩⟩
    have hdisj : Disjoint H S :=
      TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup (p := 2) (C := H) (Q := S)
        hHodd.not_two_dvd_nat hS.isPGroup
    exact Subgroup.disjoint_def.mp hdisj hdH d.2.1.1
  have hLP : L ≠ L.map (MulAut.conj u).toMonoidHom := by
    intro h
    exact huN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hinj : Function.Injective
      (fun d : D => L.map (MulAut.conj (d : G)).toMonoidHom) :=
    rigidPair_literalMap_injective
      (D := D) (L := L) (fun d hd hdNL => hstab_trivial ⟨d, hd⟩ hdNL)
  have hcard2 : Nat.card D ≤ 2 :=
    rigidPair_literalMap_card_le_two hLP hpairAll hinj
  omega

theorem commonLayer_le_orbitJoinLT {G : Type} [Group G] [Finite G] {z t : G}
    (ht2 : orderOf t = 2) (htz : t ∈ centralizer ({z} : Set G)) {M : Subgroup G}
    (hM : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) M) :
    ∃ A : Subgroup ↥(centralizer ({z} : Set G)), CFSG.IsPComponent 2 A ∧
      M.subgroupOf (centralizer ({z} : Set G)) ≤
        CFSG.StandardType.GGPumpup.orbitJoinLT A ⟨t, htz⟩ 2 := by
  let Y : Subgroup G := centralizer ({z} : Set G)
  let s : Y := ⟨t, htz⟩
  have hs2 : orderOf s = 2 := CFSG.GH74.GLS.TwoThin.orderOf_mk_centralizer htz ht2
  have hpow : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hTC : M.subgroupOf Y ≤ centralizer ({s} : Set Y) :=
    CFSG.GH74.GLS.TwoThin.le_centralizer_mk hM.1 htz
  have hT2c : ComponentClassification.TwoComponents.IsTwoComponent
      ((M.subgroupOf Y).subgroupOf (centralizer ({s} : Set Y))) :=
    CFSG.GH74.GLS.TwoThin.isTwoComponent_centralizer_mk hM htz
  have hT2 : CFSG.IsPComponent 2 ((M.subgroupOf Y).subgroupOf (centralizer ({s} : Set Y))) :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).mpr hT2c
  have hTE : M.subgroupOf Y ≤ CFSG.pLayer Y 2 := by
    rw [CFSG.ComponentClassification.LocalBFailure.pLayer_two_eq_twoLayer]
    exact (CFSG.GH74.GLS.TwoThin.pumpupY_structure hs2 hTC hT2c).1
  obtain ⟨A, hA, hKA⟩ :=
    CFSG.StandardType.GGPumpup.exists_pComponent_closureIn_eq (H := Y) (p := 2) hpow hTC hT2 hTE
  refine ⟨A, hA, ?_⟩
  show M.subgroupOf Y ≤ CFSG.StandardType.GGPumpup.orbitJoinLT A s 2
  rw [← hKA]
  exact CFSG.StandardType.GGPumpup.le_closureIn _ _

theorem orbitJoinLT_le_centralizerSection {G : Type} [Group G] [Finite G] {z t : G}
    (ht2 : orderOf t = 2) (htz : t ∈ centralizer ({z} : Set G)) {I : Subgroup G}
    (hI : IsPCompIn 2 (centralizer ({z} : Set G)) I) (htI : t ∈ normalizer (I : Set G))
    {A : Subgroup ↥(centralizer ({z} : Set G))} (hA : CFSG.IsPComponent 2 A)
    (hne : I.subgroupOf (centralizer ({z} : Set G)) ≠ A) :
    CFSG.StandardType.GGPumpup.orbitJoinLT A ⟨t, htz⟩ 2 ≤
      (centralizerSection I (pPrimeCoreOf 2 I)).subgroupOf (centralizer ({z} : Set G)) := by
  let Y : Subgroup G := centralizer ({z} : Set G)
  let s : Y := ⟨t, htz⟩
  have hs2 : orderOf s = 2 := CFSG.GH74.GLS.TwoThin.orderOf_mk_centralizer htz ht2
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h
    exact h
  have hnorm : s ∈ normalizer ((I.subgroupOf Y : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx : ((s * x * s⁻¹ : Y) : G) = t * (x : G) * t⁻¹ := by
      have h1 : ((s : Y) : G) = t := rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    simp only [Subgroup.mem_subgroupOf, hx]
    exact Subgroup.mem_normalizer_iff.mp htI (x : G)
  have hconjI : conjugate (I.subgroupOf Y) s = I.subgroupOf Y :=
    CFSG.StandardType.GGPumpup.conjugate_eq_of_mem_normalizer hnorm
  have key : ∀ B : Subgroup Y, CFSG.IsPComponent 2 B → B ≠ I.subgroupOf Y →
      B ≤ (centralizerSection I (pPrimeCoreOf 2 I)).subgroupOf Y := by
    intro B hB hBne
    have hBin : IsPCompIn 2 Y (B.map Y.subtype) := by
      refine ⟨Subgroup.map_subtype_le B, ?_⟩
      have h3 : (B.map Y.subtype).subgroupOf Y = B := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective B
      rw [h3]
      exact hB
    have hBne' : B.map Y.subtype ≠ I := by
      intro h
      apply hBne
      have h2 : (B.map Y.subtype).subgroupOf Y = I.subgroupOf Y :=
        congrArg (fun K : Subgroup G => K.subgroupOf Y) h
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective B] at h2
      exact h2
    have hle : B.map Y.subtype ≤ cSec I := le_cSec_of_ne hBin hI hBne'
    intro b hb
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem Y.subtype hb))
  show CFSG.StandardType.GGPumpup.orbitJoinLT A s 2 ≤
    (centralizerSection I (pPrimeCoreOf 2 I)).subgroupOf Y
  refine CFSG.StandardType.GGPumpup.orbitJoinLT_le (A := A) (x := s) (n := 2) fun i hi => ?_
  interval_cases i
  · rw [pow_zero, CFSG.ComponentClassification.UnbalancedLayer.conjugate_one]
    exact key A hA (Ne.symm hne)
  · rw [pow_one]
    refine key (conjugate A s)
      (CFSG.ComponentClassification.UnbalancedLayer.isPComponent_conjugate hA s) ?_
    intro h
    have hAs : conjugate (conjugate A s) s = A := by
      rw [CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate, hss,
        CFSG.ComponentClassification.UnbalancedLayer.conjugate_one]
    have heq : conjugate (conjugate A s) s = conjugate (I.subgroupOf Y) s := by rw [h]
    rw [hAs, hconjI] at heq
    exact hne heq.symm

private theorem commonLayer_le_centralizerSection {G : Type} [Group G] [Finite G] {z t : G}
    (ht2 : orderOf t = 2) (htz : t ∈ centralizer ({z} : Set G)) {K₁ K₂ M : Subgroup G}
    (hK₁ : IsPCompIn 2 (centralizer ({z} : Set G)) K₁)
    (hK₂ : IsPCompIn 2 (centralizer ({z} : Set G)) K₂) (hne : K₁ ≠ K₂)
    (htK₁ : t ∈ normalizer (K₁ : Set G)) (htK₂ : t ∈ normalizer (K₂ : Set G))
    (hM : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) M) :
    M ≤ centralizerSection K₁ (pPrimeCoreOf 2 K₁) ∨
      M ≤ centralizerSection K₂ (pPrimeCoreOf 2 K₂) := by
  obtain ⟨A, hA, hMA⟩ := commonLayer_le_orbitJoinLT ht2 htz hM
  have key : ∀ {K : Subgroup G}, IsPCompIn 2 (centralizer ({z} : Set G)) K →
      t ∈ normalizer (K : Set G) → K.subgroupOf (centralizer ({z} : Set G)) ≠ A →
        M ≤ centralizerSection K (pPrimeCoreOf 2 K) := by
    intro K hK htK hKA m hm
    have hmz : m ∈ centralizer ({z} : Set G) := (hM.1 hm).2
    exact orbitJoinLT_le_centralizerSection ht2 htz hK htK hA hKA
      (hMA (show (⟨m, hmz⟩ : ↥(centralizer ({z} : Set G))) ∈
        M.subgroupOf (centralizer ({z} : Set G)) from hm))
  by_cases h₁ : K₁.subgroupOf (centralizer ({z} : Set G)) = A
  · refine Or.inr (key hK₂ htK₂ fun h₂ => hne ?_)
    have h := Subgroup.subgroupOf_inj.mp (h₁.trans h₂.symm)
    rwa [inf_eq_left.mpr hK₁.1, inf_eq_left.mpr hK₂.1] at h
  · exact Or.inl (key hK₁ htK₁ h₁)

theorem no_isPCompIn_common_centralizer_of_rigid_actor_of_one_lt_card :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (_hr : 1 < Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (M : Subgroup G),
  ¬ CFSG.GH74.GLS.IsPCompIn 2
    (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) M := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax hr M hM
  classical
  obtain ⟨hNx, hNv⟩ := normalizes_rigid_families_of_rigid_actor hnonab hKproper hL34 h16 hx2
    hv2 hxv hvx hJ hvN hvact hxP hmax
  have hvCx : v ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hvx
  have hxCv : x ∈ centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvx.symm
  have hfin : Finite ↥(RigidSet fullQ x) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨⟨K₁, hK₁⟩, ⟨K₂, hK₂⟩, hne⟩ :=
    (Finite.one_lt_card_iff_nontrivial.mp hr).exists_pair_ne
  have hK : K₁ ≠ K₂ := fun h => hne (Subtype.ext h)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  have hconj : ∀ {K : Subgroup G}, K ∈ RigidSet fullQ x →
      K.map (MulAut.conj g).toMonoidHom ∈ RigidSet fullQ v := by
    intro K hK
    have h := isRigidOfType_conj hK g
    rw [hg] at h
    exact h
  have hL : K₁.map (MulAut.conj g).toMonoidHom ≠ K₂.map (MulAut.conj g).toMonoidHom :=
    fun h => hK (Subgroup.map_injective (MulAut.conj g).injective h)
  have hMx : IsPCompIn 2 (centralizer ({v} : Set G) ⊓ centralizer ({x} : Set G)) M := by
    rw [inf_comm]
    exact hM
  have hA := commonLayer_le_centralizerSection hv2 hvCx (P92.rig_pcomp hK₁)
    (P92.rig_pcomp hK₂) hK (hNx K₁ hK₁) (hNx K₂ hK₂) hMx
  have hB := commonLayer_le_centralizerSection hx2 hxCv (P92.rig_pcomp (hconj hK₁))
    (P92.rig_pcomp (hconj hK₂)) hL (hNv _ (hconj hK₁)) (hNv _ (hconj hK₂)) hM
  have hfinal : ∀ K ∈ RigidSet fullQ x, ∀ L ∈ RigidSet fullQ v,
      M ≤ centralizerSection K (pPrimeCoreOf 2 K) →
        M ≤ centralizerSection L (pPrimeCoreOf 2 L) → False := by
    intro K hK L hL hMK hML
    have hodd := odd_card_cxK_inf_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
      hJ hvN hvact hxP hmax K hK L hL
    have hle : M ≤ CxK x K ⊓ CxK v L := fun m hm =>
      ⟨⟨(hM.1 hm).1, hMK hm⟩, ⟨(hM.1 hm).2, hML hm⟩⟩
    have heven : Even (Nat.card M) := CFSG.GH74.GLS.C3.Layer1.Bk.even_card_of_isPCompIn hM
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
      ((even_iff_two_dvd.mp heven).trans (Subgroup.card_dvd_of_le hle)))
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hfinal K₁ hK₁ _ (hconj hK₁) hA hB
  · exact hfinal K₁ hK₁ _ (hconj hK₂) hA hB
  · exact hfinal K₂ hK₂ _ (hconj hK₁) hA hB
  · exact hfinal K₂ hK₂ _ (hconj hK₂) hA hB

end CFSG.GH74.GLS.NT44

end
