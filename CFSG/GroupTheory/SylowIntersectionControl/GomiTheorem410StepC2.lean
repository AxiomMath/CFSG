module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
import CFSG.GroupTheory.SylowAutTrivialComponent
import CFSG.GroupTheory.ComponentCovering
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentLift
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.Quasithin
  CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
private theorem subgroupOf_map_subtype_s4c2 {Y : Subgroup Ω} (N : Subgroup ↥Y) :
    (N.map Y.subtype).subgroupOf Y = N := by
  rw [← Subgroup.comap_subtype]
  exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective N

private instance pCoreOf_subgroupOf_normal_s4c2 (G : Subgroup Ω) :
    ((pCoreOf 2 G).subgroupOf G).Normal := by
  have h : (pCoreOf 2 G).subgroupOf G = pCore 2 ↥G :=
    subgroupOf_map_subtype_s4c2 (Y := G) (pCore 2 ↥G)
  rw [h]
  exact inferInstance

private theorem pCoreOf_eq_inf_pCoreOf_s4c2 {G X : Subgroup Ω} (hXG : X ≤ G)
    (hsub : (X.subgroupOf G).IsSubnormal) :
    pCoreOf 2 X = X ⊓ pCoreOf 2 G := by
  refine le_antisymm ?_ ?_
  · have hsub' : CFSG.Open.IsSubnormal X G :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hXG).mpr hsub
    exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 hsub')
  · have hle : X ⊓ pCoreOf 2 G ≤ X := inf_le_left
    have hnorm : ((X ⊓ pCoreOf 2 G).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_
      refine (le_inf Subgroup.le_normalizer
        (hXG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))).trans ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
    have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
    have hp : IsPGroup 2 ↥(X ⊓ pCoreOf 2 G) := hQ2.to_le inf_le_right
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hle hnorm hp

omit [Finite Ω] in
private theorem conj_le_s4c2 {G B : Subgroup Ω} (hBG : B ≤ G) {g : Ω} (hg : g ∈ G) :
    B.map (MulAut.conj g).toMonoidHom ≤ G := by
  have hGmap : G.map (MulAut.conj g).toMonoidHom = G :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  calc B.map (MulAut.conj g).toMonoidHom ≤ G.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hBG
    _ = G := hGmap

omit [Finite Ω] in
private theorem conj_isSubnormal_s4c2 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal) {g : Ω} (hg : g ∈ G) :
    ((B.map (MulAut.conj g).toMonoidHom).subgroupOf G).IsSubnormal := by
  have hBgG : B.map (MulAut.conj g).toMonoidHom ≤ G := conj_le_s4c2 hBG hg
  have hGmap : G.map (MulAut.conj g).toMonoidHom = G :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  refine (CFSG.Open.IsSubnormal.iff_subgroupOf hBgG).mp ?_
  have h1 := ((CFSG.Open.IsSubnormal.iff_subgroupOf hBG).mpr hsub).map
    (MulAut.conj g).toMonoidHom
  rwa [hGmap] at h1

omit [Finite Ω] in
private theorem map_conj_le_conjClosure_s4c2 {G B : Subgroup Ω} {g : Ω} (hg : g ∈ G) :
    B.map (MulAut.conj g).toMonoidHom ≤ conjClosure B G := by
  rintro x ⟨b, hb, rfl⟩
  exact mem_conjClosure hg hb

private abbrev bar_s4c2 (G X : Subgroup Ω) : Subgroup (↥G ⧸ (pCoreOf 2 G).subgroupOf G) :=
  (X.subgroupOf G).map (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))

private def barHom_s4c2 (G X : Subgroup Ω) (hXG : X ≤ G) :
    ↥X →* (↥G ⧸ (pCoreOf 2 G).subgroupOf G) :=
  (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G)).comp (Subgroup.inclusion hXG)

private theorem barHom_ker_s4c2 {G X : Subgroup Ω} (hXG : X ≤ G)
    (hsub : (X.subgroupOf G).IsSubnormal) :
    (barHom_s4c2 G X hXG).ker = pCore 2 ↥X := by
  ext x
  rw [MonoidHom.mem_ker]
  simp only [barHom_s4c2, MonoidHom.comp_apply]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmem : x ∈ pCore 2 ↥X ↔ (x : Ω) ∈ pCoreOf 2 X :=
    (Subgroup.mem_map_iff_mem (K := pCore 2 ↥X) X.subtype_injective).symm
  rw [hmem, pCoreOf_eq_inf_pCoreOf_s4c2 hXG hsub, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

omit [Finite Ω] in
private theorem barHom_range_s4c2 {G X : Subgroup Ω} (hXG : X ≤ G) :
    (barHom_s4c2 G X hXG).range = bar_s4c2 G X := by
  change ((QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G)).comp
      (Subgroup.inclusion hXG)).range
    = (X.subgroupOf G).map (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))
  rw [← MonoidHom.map_range (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))
    (Subgroup.inclusion hXG), Subgroup.inclusion_range]

private noncomputable def barIso_s4c2 {G X : Subgroup Ω} (hXG : X ≤ G)
    (hsub : (X.subgroupOf G).IsSubnormal) :
    (↥X ⧸ pCore 2 ↥X) ≃* ↥(bar_s4c2 G X) :=
  (QuotientGroup.quotientMulEquivOfEq (barHom_ker_s4c2 hXG hsub)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (barHom_s4c2 G X hXG)).trans
      (MulEquiv.subgroupCongr (barHom_range_s4c2 hXG)))

omit [Finite Ω] in
private theorem conj_pCore_eq_s4c2 {B : Subgroup Ω} (g : Ω) :
    (pCore 2 ↥B).map (Subgroup.equivMapOfInjective B (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom
      = pCore 2 ↥(B.map (MulAut.conj g).toMonoidHom) := by
  apply Subgroup.map_injective (f := (B.map (MulAut.conj g).toMonoidHom).subtype)
    (Subgroup.subtype_injective (B.map (MulAut.conj g).toMonoidHom))
  rw [Subgroup.map_map]
  have hcomp : (B.map (MulAut.conj g).toMonoidHom).subtype.comp
      (Subgroup.equivMapOfInjective B (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp B.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map]
  change (pCoreOf 2 B).map (MulAut.conj g).toMonoidHom
      = pCoreOf 2 (B.map (MulAut.conj g).toMonoidHom)
  exact (CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) B).symm

private noncomputable def conjQuotientIso_s4c2 {B : Subgroup Ω} (g : Ω) :
    (↥B ⧸ pCore 2 ↥B) ≃*
      (↥(B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 ↥(B.map (MulAut.conj g).toMonoidHom)) :=
  QuotientGroup.congr (pCore 2 ↥B) (pCore 2 ↥(B.map (MulAut.conj g).toMonoidHom))
    (Subgroup.equivMapOfInjective B (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    (conj_pCore_eq_s4c2 g)

private noncomputable def conjBarIso_s4c2 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal) {g : Ω} (hg : g ∈ G) :
    ↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)) ≃* (↥B ⧸ pCore 2 ↥B) :=
  (barIso_s4c2 (conj_le_s4c2 hBG hg) (conj_isSubnormal_s4c2 hBG hsub hg)).symm.trans
    (conjQuotientIso_s4c2 g).symm

private theorem isQuasisimple_conjBar_s4c2 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal) {g : Ω} (hg : g ∈ G)
    (hq : CFSG.IsQuasisimple (↥B ⧸ pCore 2 ↥B)) :
    CFSG.IsQuasisimple ↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)) :=
  CFSG.IsQuasisimple.of_mulEquiv (conjBarIso_s4c2 hBG hsub hg) hq

private theorem sylowAutTrivial_conjBar_s4c2 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal) {g : Ω} (hg : g ∈ G)
    (hR : SylowAutTrivial ((↥B ⧸ pCore 2 ↥B) ⧸ center (↥B ⧸ pCore 2 ↥B))) :
    SylowAutTrivial (↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)) ⧸
      center ↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom))) := by
  let e := conjBarIso_s4c2 hBG hsub hg
  let ece := QuotientGroup.congr
    (Subgroup.center ↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)))
    (Subgroup.center (↥B ⧸ pCore 2 ↥B)) e (Subgroup.map_center_eq e)
  exact SylowAutTrivial.of_mulEquiv ece hR

omit [Finite Ω] in
private theorem isSubnormal_bar_s4c2 {G B : Subgroup Ω}
    (hsub : (B.subgroupOf G).IsSubnormal) : (bar_s4c2 G B).IsSubnormal :=
  Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective ((pCoreOf 2 G).subgroupOf G)) hsub

private theorem isSylowOf_map_s4c2 {X Y : Type*} [Group X] [Finite X] [Group Y]
    {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (f : X →* Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Finite Ω] in
private theorem bar_sup_pCore_s4c2 {G N : Subgroup Ω} (hNG : N ≤ G) :
    bar_s4c2 G (N ⊔ pCoreOf 2 G) = bar_s4c2 G N := by
  have hQG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  change ((N ⊔ pCoreOf 2 G).subgroupOf G).map
      (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))
    = (N.subgroupOf G).map (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))
  have hQbot : ((pCoreOf 2 G).subgroupOf G).map
      (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G)) = ⊥ :=
    QuotientGroup.map_mk'_self (N := (pCoreOf 2 G).subgroupOf G)
  rw [Subgroup.subgroupOf_sup hNG hQG, Subgroup.map_sup, hQbot, sup_bot_eq]

private theorem isSylowOf_bar_sup_s4c2 {G T N : Subgroup Ω} (hNG : N ≤ G)
    (hT : IsSylowTwoOf T (N ⊔ pCoreOf 2 G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (bar_s4c2 G T) (bar_s4c2 G N) := by
  have hQG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hNQle : N ⊔ pCoreOf 2 G ≤ G := sup_le hNG hQG
  have hTle : T ≤ N ⊔ pCoreOf 2 G := hT.1
  have hTleG : T ≤ G := hTle.trans hNQle
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (N ⊔ pCoreOf 2 G) :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hT
  have hT0 : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf G)
      ((N ⊔ pCoreOf 2 G).subgroupOf G) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) G).mp ?_
    have h := hTsyl
    rw [← Subgroup.map_subgroupOf_eq_of_le hTleG,
      ← Subgroup.map_subgroupOf_eq_of_le hNQle] at h
    exact h
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (bar_s4c2 G T)
      (bar_s4c2 G (N ⊔ pCoreOf 2 G)) :=
    isSylowOf_map_s4c2 hT0 (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))
  rwa [bar_sup_pCore_s4c2 hNG] at h1

private theorem oResidualTwo_eq_top_of_surjective_s4c2 {L M : Type*} [Group L] [Group M]
    (f : L →* M) (hf : Function.Surjective f) (h : oResidualTwo L = ⊤) :
    oResidualTwo M = ⊤ := by
  unfold oResidualTwo at h ⊢
  rw [sInf_eq_top] at h ⊢
  intro N' hN'
  obtain ⟨hN'n, hN'p⟩ := hN'
  have hNc : (N'.comap f).Normal := hN'n.comap f
  have hquot : IsPGroup 2 (L ⧸ N'.comap f) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hN'p (f g)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, map_pow]
    exact (QuotientGroup.eq_one_iff ((f g) ^ 2 ^ k)).mp hk
  have htop : N'.comap f = ⊤ := h _ ⟨hNc, hquot⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := hf x
  exact (show y ∈ N'.comap f from by rw [htop]; trivial)

omit [Finite Ω] in
private theorem Dbar_le_centralizer_Tbar_s4c2 {G T D : Subgroup Ω}
    (hTG : T ≤ G) (hDG : D ≤ G) (hTD : ⁅T, D⁆ ≤ pCoreOf 2 G) :
    bar_s4c2 G D ≤ Subgroup.centralizer
      (bar_s4c2 G T : Set (↥G ⧸ (pCoreOf 2 G).subgroupOf G)) := by
  have hle : ⁅T.subgroupOf G, D.subgroupOf G⁆ ≤ (pCoreOf 2 G).subgroupOf G := by
    rw [← Subgroup.map_le_map_iff_of_injective G.subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTG,
      Subgroup.map_subgroupOf_eq_of_le hDG,
      Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 G)]
    exact hTD
  have hbot : (⁅T.subgroupOf G, D.subgroupOf G⁆).map
      (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  rw [Subgroup.map_commutator] at hbot
  rw [Subgroup.commutator_comm] at hbot
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot

omit [Finite Ω] in
private theorem bar_oResidualTwo_s4c2 {G D : Subgroup Ω} (hDG : D ≤ G)
    (hD : oResidualTwo ↥D = ⊤) : oResidualTwo ↥(bar_s4c2 G D) = ⊤ := by
  have h1 := oResidualTwo_eq_top_of_surjective_s4c2 (barHom_s4c2 G D hDG).rangeRestrict
    (MonoidHom.rangeRestrict_surjective (barHom_s4c2 G D hDG)) hD
  rwa [barHom_range_s4c2 hDG] at h1

omit [Finite Ω] in
private theorem subnormal_conjBar_conjClosure_s4c2 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hBsub : (B.subgroupOf G).IsSubnormal) {g : Ω} (hg : g ∈ G) :
    CFSG.Open.IsSubnormal (bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom))
      (bar_s4c2 G (conjClosure B G)) := by
  have hBgN : B.map (MulAut.conj g).toMonoidHom ≤ conjClosure B G :=
    map_conj_le_conjClosure_s4c2 hg
  have hBgN0 : (B.map (MulAut.conj g).toMonoidHom).subgroupOf G ≤
      (conjClosure B G).subgroupOf G := Subgroup.subgroupOf_mono G hBgN
  have h2 : CFSG.Open.IsSubnormal ((B.map (MulAut.conj g).toMonoidHom).subgroupOf G)
      ((conjClosure B G).subgroupOf G) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hBgN0).mpr
      (conj_isSubnormal_s4c2 hBG hBsub hg).subgroupOf
  exact h2.map (QuotientGroup.mk' ((pCoreOf 2 G).subgroupOf G))

private theorem Dbar_le_centralizer_conjBar_s4c2 {G B D T : Subgroup Ω} (g : Ω) (hg : g ∈ G)
    (hBG : B ≤ G) (hBsub : (B.subgroupOf G).IsSubnormal)
    (hq : CFSG.IsQuasisimple (↥B ⧸ pCore 2 ↥B))
    (hR : SylowAutTrivial ((↥B ⧸ pCore 2 ↥B) ⧸ center (↥B ⧸ pCore 2 ↥B)))
    (hDG : D ≤ G) (hD : oResidualTwo ↥D = ⊤)
    (hT : IsSylowTwoOf T (conjClosure B G ⊔ pCoreOf 2 G))
    (hTD : ⁅T, D⁆ ≤ pCoreOf 2 G) :
    bar_s4c2 G D ≤ Subgroup.centralizer
      (bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom) :
        Set (↥G ⧸ (pCoreOf 2 G).subgroupOf G)) := by
  have hNG : conjClosure B G ≤ G :=
    conjClosure_le fun _ hh _ hz => G.mul_mem (G.mul_mem hh (hBG hz)) (G.inv_mem hh)
  have hBgG : B.map (MulAut.conj g).toMonoidHom ≤ G := conj_le_s4c2 hBG hg
  have hBgsub : ((B.map (MulAut.conj g).toMonoidHom).subgroupOf G).IsSubnormal :=
    conj_isSubnormal_s4c2 hBG hBsub hg
  have hKsubN := subnormal_conjBar_conjClosure_s4c2 hBG hBsub hg
  have hSylS : CFSG.ABGLocalTools.IsSylowOf 2
      (bar_s4c2 G T ⊓ bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom))
      (bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)) :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal
      (isSylowOf_bar_sup_s4c2 hNG hT) hKsubN
  have hTleG : T ≤ G := hT.1.trans (sup_le hNG (CFSG.LieType.BorelTits.pCoreOf_le 2 G))
  have hDcenT : bar_s4c2 G D ≤ Subgroup.centralizer
      (bar_s4c2 G T : Set (↥G ⧸ (pCoreOf 2 G).subgroupOf G)) :=
    Dbar_le_centralizer_Tbar_s4c2 hTleG hDG hTD
  have hDcenS : bar_s4c2 G D ≤ Subgroup.centralizer
      (bar_s4c2 G T ⊓ bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom) :
        Set (↥G ⧸ (pCoreOf 2 G).subgroupOf G)) :=
    hDcenT.trans (Subgroup.centralizer_le inf_le_left)
  obtain ⟨P, hP⟩ := hSylS.exists_sylow_eq_subgroupOf
  have hPmap : ((P : Subgroup ↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom))).map
      (bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)).subtype)
      = bar_s4c2 G T ⊓ bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom) := by
    rw [hP]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hDres : oResidualTwo ↥(bar_s4c2 G D) = ⊤ := bar_oResidualTwo_s4c2 hDG hD
  have hDP : bar_s4c2 G D ≤ Subgroup.centralizer
      (((P : Subgroup ↥(bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom))).map
        (bar_s4c2 G (B.map (MulAut.conj g).toMonoidHom)).subtype :
          Subgroup (↥G ⧸ (pCoreOf 2 G).subgroupOf G)) : Set _) := by
    rw [hPmap]
    exact hDcenS
  exact SylowAutTrivial.le_centralizer (isQuasisimple_conjBar_s4c2 hBG hBsub hg hq)
    (isSubnormal_bar_s4c2 hBgsub)
    (sylowAutTrivial_conjBar_s4c2 hBG hBsub hg hR) P hDres hDP

theorem commutator_conjClosure_le_pCoreOf {G B D T : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B))
    (hR : SylowAutTrivial ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ center (↥B ⧸ CFSG.pCore 2 ↥B)))
    (hT : IsSylowTwoOf T (conjClosure B G ⊔ pCoreOf 2 G)) (hDG : D ≤ G)
    (hD : oResidualTwo ↥D = ⊤) (hTD : ⁅T, D⁆ ≤ pCoreOf 2 G) :
    ⁅conjClosure B G, D⁆ ≤ pCoreOf 2 G := by
  classical
  let Q : Subgroup Ω := pCoreOf 2 G
  let π : ↥G →* (↥G ⧸ Q.subgroupOf G) := QuotientGroup.mk' (Q.subgroupOf G)
  let C0 : Subgroup ↥G :=
    (Subgroup.centralizer ((D.subgroupOf G).map π : Subgroup (↥G ⧸ Q.subgroupOf G))).comap π
  have hstep : ∀ h ∈ G, ∀ b ∈ B, h * b * h⁻¹ ∈ C0.map G.subtype := by
    intro h hh b hb
    have hBh : h * b * h⁻¹ ∈ B.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨b, hb, by simp [MulAut.conj_apply]⟩
    have hG : h * b * h⁻¹ ∈ G := G.mul_mem (G.mul_mem hh (hB.le hb)) (G.inv_mem hh)
    have hbK : π (⟨h * b * h⁻¹, hG⟩ : ↥G) ∈
        bar_s4c2 G (B.map (MulAut.conj h).toMonoidHom) :=
      Subgroup.mem_map_of_mem π hBh
    have hle := Dbar_le_centralizer_conjBar_s4c2 h hh hB.le hB.subnormal hq
      (show SylowAutTrivial ((↥B ⧸ pCore 2 ↥B) ⧸ center (↥B ⧸ pCore 2 ↥B)) from hR)
      hDG hD hT hTD
    have hcen : π (⟨h * b * h⁻¹, hG⟩ : ↥G) ∈
        Subgroup.centralizer ((D.subgroupOf G).map π : Subgroup (↥G ⧸ Q.subgroupOf G)) := by
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      exact ((Subgroup.mem_centralizer_iff.mp (hle hz)) _ hbK).symm
    exact Subgroup.mem_map.mpr ⟨⟨h * b * h⁻¹, hG⟩, Subgroup.mem_comap.mpr hcen, rfl⟩
  have hNC : conjClosure B G ≤ C0.map G.subtype := conjClosure_le hstep
  rw [Subgroup.commutator_le]
  intro n hn d hd
  have hnC : n ∈ C0.map G.subtype := hNC hn
  obtain ⟨y, hyC0, hy⟩ := Subgroup.mem_map.mp hnC
  have hmemD : π (⟨d, hDG hd⟩ : ↥G) ∈ (D.subgroupOf G).map π :=
    Subgroup.mem_map_of_mem π (show (⟨d, hDG hd⟩ : ↥G) ∈ D.subgroupOf G from hd)
  have hcomm : π (⟨d, hDG hd⟩ : ↥G) * π y = π y * π (⟨d, hDG hd⟩ : ↥G) :=
    (Subgroup.mem_centralizer_iff.mp hyC0) _ hmemD
  have h1 : π ⁅y, (⟨d, hDG hd⟩ : ↥G)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have h2 : ⁅y, (⟨d, hDG hd⟩ : ↥G)⁆ ∈ (pCoreOf 2 G).subgroupOf G :=
    (QuotientGroup.eq_one_iff (N := (pCoreOf 2 G).subgroupOf G) _).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  rw [← hy]
  exact h2

end CFSG.GroupTheory
