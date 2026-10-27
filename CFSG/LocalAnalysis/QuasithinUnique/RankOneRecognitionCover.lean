module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearFourCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Models
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.QuasithinUnique.RankOneRecog

open CFSG.Open
open scoped MatrixGroups

section Ambient

variable {G : Type*} [Group G]

theorem isElemAbelian_subgroupOf {U H : Subgroup G} (hU : IsElemAbelian 2 U) :
    IsElemAbelian 2 (U.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hU H

theorem stronglyClosed_subgroupOf {H S U : Subgroup G} {S' : Sylow 2 H}
    (hS' : (S' : Subgroup H).map H.subtype = S)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) :
    fusionStronglyClosed ((U.subgroupOf H : Subgroup H) : Set H) (S' : Subgroup H) := by
  intro a ha g hg
  have hgS : (g : G)⁻¹ * (a : G) * (g : G) ∈ S := by
    rw [← hS']
    exact Subgroup.mem_map_of_mem H.subtype hg
  exact hcl (a : G) ha (g : G) g.2 hgS

theorem subgroupOf_le_of_map_eq {H S U : Subgroup G} {S' : Subgroup H}
    (hS' : S'.map H.subtype = S) (hUS : U ≤ S) : U.subgroupOf H ≤ S' := by
  intro x hx
  have hxS : (x : G) ∈ S := hUS hx
  rw [← hS'] at hxS
  obtain ⟨y, hy, hyx⟩ := hxS
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

end Ambient

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_iff_exists {S H : Subgroup G} :
    IsSylowTwoOf S H ↔ ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hS
    have hS2 : IsPGroup 2 (S.subgroupOf H) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    refine ⟨hS2.toSylow hS.2.2, ?_⟩
    change (S.subgroupOf H).map H.subtype = S
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS.1]
  · rintro ⟨P, rfl⟩
    refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map H.subtype, ?_⟩
    change ¬ 2 ∣ (((P : Subgroup H).map H.subtype).comap H.subtype).index
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact P.not_dvd_index

theorem exists_sylow_inf_of_subnormal {H S L : Subgroup G} (hS : IsSylowTwoOf S H) (hLH : L ≤ H)
    (hsub : (L.subgroupOf H).IsSubnormal) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := isSylowTwoOf_iff_exists.mp hS
  obtain ⟨P', hP'⟩ := exists_sylow_map_eq_inf_of_subnormal S' hsub
  let e : (L.subgroupOf H) ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  refine ⟨P'.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : L.subtype.comp e.toMonoidHom = H.subtype.comp (L.subgroupOf H).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hP', Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective, hS',
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLH]

theorem isSylowTwoOf_inf_of_subnormal {H S L : Subgroup G} (hS : IsSylowTwoOf S H) (hLH : L ≤ H)
    (hsub : (L.subgroupOf H).IsSubnormal) : IsSylowTwoOf (S ⊓ L) L := by
  obtain ⟨P, hP⟩ := exists_sylow_inf_of_subnormal hS hLH hsub
  exact isSylowTwoOf_iff_exists.mpr ⟨P, hP⟩

theorem exists_noncentral_sylow_centralizer {H S L : Subgroup G} {w : G}
    (hS : IsSylowTwoOf S H) (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hinner : ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) :
    ∃ (P : Sylow 2 L) (x : L), x ∈ Subgroup.centralizer ((P : Subgroup L) : Set L) ∧
      x ∉ Subgroup.center L := by
  obtain ⟨P, hP⟩ := exists_sylow_inf_of_subnormal hS hLH hsub
  obtain ⟨x, hxL, hx⟩ := hinner
  refine ⟨P, ⟨x, hxL⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyS : (y : G) ∈ S := by
      have : (y : G) ∈ (P : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem _ hy
      rw [hP] at this
      exact this.1
    have h1 : (y : G) * w = w * y := Subgroup.mem_centralizer_iff.mp hwS _ hyS
    have h2 : w⁻¹ * y * w = x⁻¹ * y * x := hx y y.2
    have h3 : w⁻¹ * y * w = y := by
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    have h4 : x⁻¹ * y * x = y := h2.symm.trans h3
    apply Subtype.ext
    show (y : G) * x = x * y
    calc (y : G) * x = x * (x⁻¹ * y * x) := by group
      _ = x * y := by rw [h4]
  · intro hxc
    apply hnc
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (⟨y, hy⟩ : L) * ⟨x, hxL⟩ = ⟨x, hxL⟩ * ⟨y, hy⟩ :=
      Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩
    have h2 : y * x = x * y := congrArg Subtype.val h1
    have h3 : w⁻¹ * y * w = y := by
      rw [hx y hy]
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [h2]
        _ = y := by group
    calc y * w = w * (w⁻¹ * y * w) := by group
      _ = w * y := by rw [h3]

end Sylow

section Bender

theorem isSimpleGroup_of_fusionIsBenderGroup {X : Type*} [Group X] [Finite X]
    (h : fusionIsBenderGroup X) : IsSimpleGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact (CFSG.BenderSuzuki.IsSimpleBenderGroup.isPSL2 ⟨f, hf, ⟨e⟩⟩).isSimple
  · exact e.isSimpleGroup_congr.mpr (CFSG.ShultStronglyClosedTI.unitaryCover_native_simple f hf)
  · exact (e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)).isSimpleGroup_congr.mpr
      (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a ha).1

theorem exists_noncommuting_of_perfect {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (h : fusionIsBenderGroup X) : ∃ a b : X, a * b ≠ b * a := by
  have : IsSimpleGroup X := isSimpleGroup_of_fusionIsBenderGroup h
  by_contra hcon
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  exact Group.IsPerfect.not_isMulCommutative X (IsMulCommutative.mk (Std.Commutative.mk hcomm))

noncomputable def mulEquivOfCenterEqBot {L X : Type*} [Group L] [Group X]
    (h : Subgroup.center L = ⊥) (e : L ⧸ Subgroup.center L ≃* X) : L ≃* X :=
  QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq h.symm).trans e)

theorem fusionIsBenderGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨m⟩⟩ | ⟨f, hf, ⟨m⟩⟩ | ⟨a, ha, ⟨m⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans m⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans m⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans m⟩⟩)

theorem fusionIsBenderGroup_of_center_eq_bot {L : Type*} [Group L]
    (h : Subgroup.center L = ⊥) (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L)) :
    fusionIsBenderGroup L :=
  fusionIsBenderGroup_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).symm hmodel

universe u

theorem ker_comp_centerQuotient {L X : Type*} [Group L] [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L := by
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

theorem linear_center_eq_bot_of_noncentral_sylow_centralizer {L : Type u} [Group L] [Finite L]
    [Group.IsPerfect L] (hp : IsPGroup 2 (Subgroup.center L)) {f : ℕ} (hf : 2 ≤ f)
    (e : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField 2 f)) (P : Sylow 2 L) {x : L}
    (hx : x ∈ Subgroup.centralizer ((P : Subgroup L) : Set L)) (hxn : x ∉ Subgroup.center L) :
    Subgroup.center L = ⊥ := by
  let F := GaloisField 2 f
  have hcard : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  let eJ := e.trans (CFSG.ShultStronglyClosedTI.glaSL2EquivNative f hf hcard).symm
  let η := eJ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hsurj : Function.Surjective η := eJ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center L := ker_comp_centerQuotient eJ
  have hcentral : η.ker ≤ Subgroup.center L := hker.le
  have hp' : IsPGroup 2 η.ker := hker.symm ▸ hp
  by_cases hfour : f = 2
  · have hcardfour : Nat.card F = 4 := by simpa [hfour] using hcard
    by_contra hne
    have hne' : η.ker ≠ ⊥ := hker ▸ hne
    have hcen := ((CFSG.ShultStronglyClosedTI.four_field_linear_central_two_cover_full hcardfour η
      hsurj hcentral hp').2 hne' P).2.2.2.1
    exact hxn (hker ▸ hcen ▸ hx)
  · have hbot := (CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_trivial f
      (by omega) hcard η hsurj hcentral hp').1
    exact hker.symm.trans hbot

theorem unitary_center_eq_bot {L : Type u} [Group L] [Finite L] [Group.IsPerfect L]
    (hp : IsPGroup 2 (Subgroup.center L)) {f : ℕ} (hf : 2 ≤ f)
    (e : L ⧸ Subgroup.center L ≃* PSU3 2 f) : Subgroup.center L = ⊥ :=
  (CFSG.ShultStronglyClosedTI.unitaryCover_native_center_quotient_full f hf hp e).1

theorem suzuki_center_eq_bot_of_noncentral_sylow_centralizer {L : Type u} [Group L] [Finite L]
    [Group.IsPerfect L] (hp : IsPGroup 2 (Subgroup.center L)) {a : ℕ} (ha : 1 ≤ a)
    (e : L ⧸ Subgroup.center L ≃* Sz a) (P : Sylow 2 L) {x : L}
    (hx : x ∈ Subgroup.centralizer ((P : Subgroup L) : Set L)) (hxn : x ∉ Subgroup.center L) :
    Subgroup.center L = ⊥ := by
  let η := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hsurj : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center L := ker_comp_centerQuotient e
  by_contra hne
  have hcen := (CFSG.ShultStronglyClosedTI.suzukiCover_native_nontrivial_Sylow_centralizer a ha η
    hsurj hker.le (hker.symm ▸ hp) (hker ▸ hne)).1 P
  exact hxn (hker ▸ hcen ▸ hx)

theorem center_eq_bot_of_noncentral_sylow_centralizer {L : Type u} [Group L] [Finite L]
    [Group.IsPerfect L] (hp : IsPGroup 2 (Subgroup.center L))
    (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L)) (P : Sylow 2 L) {x : L}
    (hx : x ∈ Subgroup.centralizer ((P : Subgroup L) : Set L)) (hxn : x ∉ Subgroup.center L) :
    Subgroup.center L = ⊥ := by
  rcases hmodel with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact linear_center_eq_bot_of_noncentral_sylow_centralizer hp hf e P hx hxn
  · exact unitary_center_eq_bot hp hf e
  · exact suzuki_center_eq_bot_of_noncentral_sylow_centralizer hp ha e P hx hxn

theorem simple_nonabelian_of_center_eq_bot {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hcenter : Subgroup.center L = ⊥) (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L)) :
    IsSimpleGroup L ∧ ∃ a b : L, a * b ≠ b * a := by
  have hL : fusionIsBenderGroup L := fusionIsBenderGroup_of_center_eq_bot hcenter hmodel
  exact ⟨isSimpleGroup_of_fusionIsBenderGroup hL, exists_noncommuting_of_perfect hL⟩

theorem even_linear_two_central_cover_inner_action_reconstruction {G : Type*} [Group G] [Finite G]
    {H S L : Subgroup G} {w : G} (hS : IsSylowTwoOf S H) (hLH : L ≤ H)
    (hsub : (L.subgroupOf H).IsSubnormal) (hperf : Group.IsPerfect L)
    (hZ : IsPGroup 2 (Subgroup.center L)) {f : ℕ} (hf : 2 ≤ f)
    (e : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField 2 f))
    (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hinner : ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      Nonempty (L ≃* PSL(2, GaloisField 2 f)) := by
  have := hperf
  obtain ⟨P, x, hx, hxn⟩ := exists_noncentral_sylow_centralizer hS hLH hsub hwS hinner hnc
  have hcenter := linear_center_eq_bot_of_noncentral_sylow_centralizer hZ hf e P hx hxn
  have h := simple_nonabelian_of_center_eq_bot hcenter (Or.inl ⟨f, hf, ⟨e⟩⟩)
  exact ⟨hcenter, h.1, h.2, ⟨mulEquivOfCenterEqBot hcenter e⟩⟩

theorem even_unitary_three_central_cover_reconstruction {L : Type u} [Group L] [Finite L]
    [Group.IsPerfect L] (hZ : IsPGroup 2 (Subgroup.center L)) {f : ℕ} (hf : 2 ≤ f)
    (e : L ⧸ Subgroup.center L ≃* PSU3 2 f) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      Nonempty (L ≃* PSU3 2 f) := by
  have hcenter := unitary_center_eq_bot hZ hf e
  have h := simple_nonabelian_of_center_eq_bot hcenter (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  exact ⟨hcenter, h.1, h.2, ⟨mulEquivOfCenterEqBot hcenter e⟩⟩

theorem Suzuki_central_cover_inner_action_reconstruction {G : Type*} [Group G] [Finite G]
    {H S L : Subgroup G} {w : G} (hS : IsSylowTwoOf S H) (hLH : L ≤ H)
    (hsub : (L.subgroupOf H).IsSubnormal) (hperf : Group.IsPerfect L)
    (hZ : IsPGroup 2 (Subgroup.center L)) {a : ℕ} (ha : 1 ≤ a)
    (e : L ⧸ Subgroup.center L ≃* Sz a) (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hinner : ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      Nonempty (L ≃* Sz a) := by
  have := hperf
  obtain ⟨P, x, hx, hxn⟩ := exists_noncentral_sylow_centralizer hS hLH hsub hwS hinner hnc
  have hcenter := suzuki_center_eq_bot_of_noncentral_sylow_centralizer hZ ha e P hx hxn
  have h := simple_nonabelian_of_center_eq_bot hcenter (Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩))
  exact ⟨hcenter, h.1, h.2, ⟨mulEquivOfCenterEqBot hcenter e⟩⟩

end Bender

end CFSG.QuasithinUnique.RankOneRecog
