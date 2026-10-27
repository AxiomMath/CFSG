module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Walter.AStar.Basic
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem odd_card_oddCore_aux (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem two_dvd_card_of_isQuasisimple {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) : 2 ∣ Nat.card X := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
  have heven : Even (Nat.card (X ⧸ Subgroup.center X)) :=
    CFSG.Walter.even_card_of_isSimpleGroup hX.2.2
  exact (even_iff_two_dvd.mp heven).trans (Subgroup.card_quotient_dvd_card (Subgroup.center X))

private theorem two_dvd_card_of_isComponent {X : Type*} [Group X] [Finite X]
    {K : Subgroup X} (hK : CFSG.IsComponent K) : 2 ∣ Nat.card K :=
  two_dvd_card_of_isQuasisimple hK.1

private theorem exists_mul_ne_mul_of_simple_perfect {Q : Type*} [Group Q] [Nontrivial Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  have hcomm : IsMulCommutative Q := isMulCommutative_iff.mpr fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  exact Group.IsPerfect.not_isMulCommutative Q hcomm

private theorem simple_oddCore_of_lieModel [Finite G] {X : Subgroup G}
    {tag : CFSG.Open.StatedLieTag} {n f : ℕ} (hn : n ≠ 0)
    (hm : LieModel (X ⧸ CFSG.oddCore X) tag n 3 f) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ CFSG.oddCore X)
    ⟨tag, n, 3, f, hm.statedClassicalModel_of_ne_zero hn⟩).2.2

private theorem simple_oddCore_of_shape [Finite G] {X : Subgroup G}
    (h : IsOmega5 X ∨ IsL29 X ∨ IsU33 X ∨ IsL3Eps3 X) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) := by
  rcases h with h | h | h | h
  · exact simple_oddCore_of_lieModel (by norm_num) h
  · exact simple_oddCore_of_lieModel (by norm_num) h
  · exact simple_oddCore_of_lieModel (by norm_num) h
  · rcases h with h | h
    · exact simple_oddCore_of_lieModel (by norm_num) h
    · exact simple_oddCore_of_lieModel (by norm_num) h

private theorem isQuasisimple_of_layer_eq_top_of_simple_oddCore {X : Type*} [Group X] [Finite X]
    (hlayer : CFSG.layer X = ⊤)
    (hsimple : IsSimpleGroup (X ⧸ CFSG.oddCore X)) :
    CFSG.IsQuasisimple X := by
  classical
  let q : X →* (X ⧸ CFSG.oddCore X) := QuotientGroup.mk' (CFSG.oddCore X)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hperfX : Group.IsPerfect X := by
    have h : Group.IsPerfect ↥(CFSG.layer X) := CFSG.LocalCores.layer_isPerfect
    rw [hlayer] at h
    letI : Group.IsPerfect ↥(⊤ : Subgroup X) := h
    have hf : Function.Surjective (Subgroup.topEquiv (G := X)).toMonoidHom := by
      simpa using (Subgroup.topEquiv (G := X)).surjective
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := X)).toMonoidHom) hf
  haveI : Group.IsPerfect X := hperfX
  haveI : Group.IsPerfect (X ⧸ CFSG.oddCore X) :=
    Group.IsPerfect.ofSurjective (f := q) hq
  have hXnt : Nontrivial X := hq.nontrivial
  have hlayerNe : CFSG.layer X ≠ ⊥ := by
    rw [hlayer]
    exact top_ne_bot
  obtain ⟨K, hK⟩ : ∃ K : Subgroup X, CFSG.IsComponent K := by
    by_contra h
    exact hlayerNe (CFSG.LocalCores.layer_eq_bot_of_forall fun L hL => h ⟨L, hL⟩)
  have hmap_top : ∀ L : Subgroup X, CFSG.IsComponent L → L.map q = ⊤ := by
    intro L hL
    have hLnorm : L.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hL
    have hLmapNorm : (L.map q).Normal := hLnorm.map q hq
    have hLmapNe : L.map q ≠ ⊥ := by
      intro hbot
      have hle : L ≤ q.ker := (Subgroup.map_eq_bot_iff L).mp hbot
      rw [show q.ker = CFSG.oddCore X from QuotientGroup.ker_mk' _] at hle
      have h2 : 2 ∣ Nat.card L := two_dvd_card_of_isComponent hL
      have h3 : Nat.card L ∣ Nat.card (CFSG.oddCore X) := Subgroup.card_dvd_of_le hle
      exact (Nat.not_even_iff_odd.mpr (odd_card_oddCore_aux X))
        (even_iff_two_dvd.mpr (h2.trans h3))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.map q) with h | h
    · exact absurd h hLmapNe
    · exact h
  have huniq : ∀ L : Subgroup X, CFSG.IsComponent L → L = K := by
    intro L hL
    by_contra hne
    have hcomm : ⁅L, K⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hL hK).resolve_left hne
    have hLtop := hmap_top L hL
    have hKtop := hmap_top K hK
    have hcommQ : IsMulCommutative (X ⧸ CFSG.oddCore X) := by
      apply isMulCommutative_iff.mpr
      intro a b
      obtain ⟨x, hxL, hxa⟩ := Subgroup.mem_map.mp (hLtop.symm ▸ Subgroup.mem_top a)
      obtain ⟨y, hyK, hyb⟩ := Subgroup.mem_map.mp (hKtop.symm ▸ Subgroup.mem_top b)
      have hcent : L ≤ Subgroup.centralizer (K : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hxy : x * y = y * x :=
        (Subgroup.mem_centralizer_iff.mp (hcent hxL) y hyK).symm
      calc a * b = q x * q y := by rw [hxa, hyb]
        _ = q (x * y) := (map_mul q x y).symm
        _ = q (y * x) := by rw [hxy]
        _ = q y * q x := map_mul q y x
        _ = b * a := by rw [hxa, hyb]
    have hnonab : ∃ a b : X ⧸ CFSG.oddCore X, a * b ≠ b * a :=
      exists_mul_ne_mul_of_simple_perfect
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (isMulCommutative_iff.mp hcommQ a b)
  have hsup : CFSG.layer X = K := by
    rw [CFSG.layer.eq_sSup]
    exact le_antisymm (sSup_le fun L hL => le_of_eq (huniq L hL)) (le_sSup hK)
  have hKtop : K = ⊤ := hsup.symm.trans hlayer
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv) hK.1

private theorem layer_layerCent_eq_top [Finite G] (L : Subgroup G) (s : G) :
    CFSG.layer ↥(layerCent L s) = ⊤ := by
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  haveI : Finite ↥H := Subtype.finite
  let e : ↥(CFSG.layer H) ≃* ↥(layerCent L s) :=
    (CFSG.layer H).equivMapOfInjective H.subtype H.subtype_injective
  haveI : Finite ↥(CFSG.layer H) :=
    Finite.of_injective (Subgroup.subtype (CFSG.layer H)) (Subgroup.subtype_injective _)
  exact CFSG.LocalCores.layer_eq_top_of_surjective
    (CFSG.WholeGroup.layer_layer_eq_top (G := ↥H)) e.toMonoidHom e.surjective

theorem isComponentIn_layerCent [Finite G] {L : Subgroup G} {s : G}
    (h : IsOmega5 (layerCent L s) ∨ IsL29 (layerCent L s) ∨ IsU33 (layerCent L s) ∨
      IsL3Eps3 (layerCent L s)) :
    IsComponentIn (layerCent L s) (L ⊓ centralizer ({s} : Set G)) := by
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  have hsimple : IsSimpleGroup (↥(layerCent L s) ⧸ CFSG.oddCore ↥(layerCent L s)) :=
    simple_oddCore_of_shape h
  have hquasi : CFSG.IsQuasisimple ↥(layerCent L s) :=
    isQuasisimple_of_layer_eq_top_of_simple_oddCore (layer_layerCent_eq_top L s) hsimple
  have hle : layerCent L s ≤ H := by
    rw [layerCent, CFSG.inSubgroup]
    exact Subgroup.map_subtype_le _
  have hEq : (layerCent L s).subgroupOf H = CFSG.layer H := by
    ext x
    rw [Subgroup.mem_subgroupOf, layerCent, CFSG.inSubgroup]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    · intro hx
      exact Subgroup.mem_map_of_mem H.subtype hx
  have hNormal : ((layerCent L s).subgroupOf H).Normal := by
    rw [hEq]
    haveI : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
    exact inferInstance
  exact isComponentIn_of_normal hle hquasi hNormal

end CFSG.OddStandard.SmallF3.Omega
