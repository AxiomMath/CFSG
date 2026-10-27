module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCovG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L311Aux
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_x_ka_pocket [Finite G] {H : Subgroup G} (hH : InFStar H) {y : G} {B : Subgroup G}
    (hyH : y ∈ H) (hy : y * y = 1) (hp : Sl23PocketIn H y B) :
    Sl23PocketIn (⊤ : Subgroup (↥H ⧸ oddCore ↥H)) (QuotientGroup.mk (⟨y, hyH⟩ : ↥H))
      ((B.subgroupOf H).map (QuotientGroup.mk' (oddCore ↥H))) := by
  have h1 := l34g_x_sl23PocketIn_subgroupOf (le_refl H) hyH hp
  rw [Subgroup.subgroupOf_self] at h1
  have hy' : (⟨y, hyH⟩ : ↥H) * ⟨y, hyH⟩ = 1 := Subtype.ext hy
  have h2 := l34g_x_sl23PocketIn_map (l34g_x_cover hH) hy' h1
  rwa [Subgroup.map_top_of_surjective _ (l34g_x_cover hH).surjective] at h2

theorem l34g_x_ka_fixed [Finite G] {H : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ normalizer (H : Set G)) {α : MulAut (↥H ⧸ oddCore ↥H)}
    (hα : ∀ x : ↥H, (QuotientGroup.mk (conjAut H ht htN x) : ↥H ⧸ oddCore ↥H) =
      α (QuotientGroup.mk x))
    {B : Subgroup G} (hBH : B ≤ H) (hBt : B ≤ centralizer ({t} : Set G)) :
    ∀ b ∈ (B.subgroupOf H).map (QuotientGroup.mk' (oddCore ↥H)), α b = b := by
  rintro _ ⟨b', hb', rfl⟩
  have hbt : t * (b' : G) = (b' : G) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hBt (Subgroup.mem_subgroupOf.mp hb'))).symm
  have hfix : conjAut H ht htN b' = b' := by
    apply Subtype.ext
    rw [coe_conjAut, hbt]
    exact mul_inv_cancel_right _ _
  calc α (QuotientGroup.mk' (oddCore ↥H) b')
      = QuotientGroup.mk (conjAut H ht htN b') := (hα b').symm
    _ = QuotientGroup.mk' (oddCore ↥H) b' := by rw [hfix]; rfl

theorem l34g_x_ka_ascent [Finite G] {H : Subgroup G} (hH : InFStar H) {t : G} (ht : t * t = 1)
    (htN : t ∈ normalizer (H : Set G)) {α : MulAut (↥H ⧸ oddCore ↥H)}
    (hα : ∀ x : ↥H, (QuotientGroup.mk (conjAut H ht htN x) : ↥H ⧸ oddCore ↥H) =
      α (QuotientGroup.mk x))
    {y : G} (hyH : y ∈ H) (hy : y * y = 1) {Jb : Subgroup (↥H ⧸ oddCore ↥H)}
    (hJb : IsComponentIn Jb (L34GFix α)) (hFS : InFStar Jb)
    (hyJ : (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ oddCore ↥H) ∈ Jb)
    (hI : IsI4PlusIn Jb (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ oddCore ↥H)) :
    ∃ J : Subgroup G, IsComponentIn J (H ⊓ centralizer ({t} : Set G)) ∧ InFStar J ∧ y ∈ J ∧
      IsI4PlusIn J y := by
  have hcov := l34g_x_cover hH
  have hq : CFSG.IsQuasisimple ↥Jb := inFStar_isQuasisimple hFS
  have hy' : (⟨y, hyH⟩ : ↥H) * ⟨y, hyH⟩ = 1 := Subtype.ext hy
  have hmem : (⟨y, hyH⟩ : ↥H) ∈ coverDerived (QuotientGroup.mk' (oddCore ↥H)) Jb :=
    hcov.mem_coverDerived hq hy' hyJ
  refine ⟨(coverDerived (QuotientGroup.mk' (oddCore ↥H)) Jb).map H.subtype,
    l34g_x_isComponentIn_lift hH ht htN hα hJb,
    l34g_x_inFStar_map_inj H.subtype H.subtype_injective
      (l34g_x_inFStar_coverDerived hcov hFS),
    Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, hmem, rfl⟩, ?_⟩
  exact l34g_x_isI4PlusIn_map_inj H.subtype H.subtype_injective hmem
    (l34g_x_isI4PlusIn_coverDerived hcov hq hy' hyJ hI)

theorem asc82FactPocketComp_of_core (h : Asc82CoreKGA) : Asc82FactPocketComp := by
  intro G _ _ H hH y B hy2 hp t ht2 htN hBt hty
  have hyH : y ∈ H := (hp.2.1 hp.1).1
  have hBH : B ≤ H := fun b hb => (hp.2.1 hb).1
  have hy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  have ht : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  obtain ⟨α, hα2, hα⟩ := l34g_x_induced ht htN
  have hord : orderOf (⟨y, hyH⟩ : ↥H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hy2
  have hbar : orderOf (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ oddCore ↥H) = 2 :=
    l34g_x_orderOf_map (l34g_x_cover hH) hord
  have hpk := l34g_x_ka_pocket hH hyH hy hp
  obtain ⟨Jb, hJb, hFS, hBJ⟩ := h _ (l34g_x_starQuotient hH) _ _ hbar hpk α hα2
    (l34g_x_ka_fixed ht htN hα hBH hBt) (l34g_x_induced_ne_conj hH hyH hy ht htN hty hα)
  have hyB : (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ oddCore ↥H) ∈
      (B.subgroupOf H).map (QuotientGroup.mk' (oddCore ↥H)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp.1)
  have hI : IsI4PlusIn Jb (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ oddCore ↥H) :=
    ⟨hbar, _, Sl23PocketIn.of_le hpk hBJ le_top⟩
  exact l34g_x_ka_ascent hH ht htN hα hyH hy hJb hFS (hBJ hyB) hI

end CFSG.OddStandard.SmallF3.Omega
