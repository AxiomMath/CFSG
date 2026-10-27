module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Position

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le)

section Skeleton

variable {G : Type} [Group G] {L : Subgroup G}

variable [Finite G]

theorem exists_le_centralizer_perfectCore_of_twoSided_compat (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {x z : G} (hzL : z ∈ L)
    (hzLx : z ∈ CFSG.conjugate L x) (hxt : x⁻¹ * t * x = t * z) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hzU' : ∃ U' : Sylow 2 (CFSG.conjugate L x),
      ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u)
    (hact : ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF2 : ∀ (U : Sylow 2 C) (w : C), (∀ u ∈ (U : Subgroup C), u * w = w * u) → w ≠ 1 →
      ∃ (k : κ) (c : C), c * w * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {D : Type*} [Group D]
    (hF56 : ∀ (k k' : κ) (β : (Q k ⊔ M k : Subgroup C) ≃* (Q k' ⊔ M k' : Subgroup C)),
      (∀ y : (Q k ⊔ M k : Subgroup C), ((β y : C) ∈ Q k' ↔ (y : C) ∈ Q k)) →
      ∀ ι : M k ≃* M k',
      (∀ m : M k, ((ι m : C))⁻¹ * (β (inclusion le_sup_right m) : C) ∈ Q k') →
      Nonempty (perfectCore (centralizer
        ((((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype : Subgroup C) : Set C)) ≃*
          D))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype) :
    ∃ (k : κ) (g : G), rep k ≠ 1 ∧ g⁻¹ * t * g = t * (e.symm (rep k) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧
        Nonempty (P ≃* D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact (e.symm c).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [hφdef]⟩
  have hφL : ∀ c : C, φ c ∈ L := fun c => hφr ▸ ⟨c, rfl⟩
  obtain ⟨U, hU⟩ := hzU
  set zC : C := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := fun h => hz1 (by rw [← hφz, h, map_one])
  have hzCU : ∀ u ∈ ((U.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 C) :
      Subgroup C), u * zC = zC * u := by
    intro u hu
    change u ∈ (U : Subgroup L).map e.toMonoidHom at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hzC, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hU v hv))
  obtain ⟨k, c, hc⟩ := hF2 _ zC hzCU hzC1
  have hrep1 : rep k ≠ 1 := by
    intro h1
    apply hzC1
    have : zC = c⁻¹ * (c * zC * c⁻¹) * c := by group
    rw [this, hc, h1]
    group
  set l : G := φ c with hldef
  set g₁ : G := x * l⁻¹ with hg₁def
  set y : G := φ (rep k) with hydef
  have hy : y = l * z * l⁻¹ := by rw [hydef, ← hc, map_mul, map_mul, map_inv, hφz]
  have htl : l * t = t * l := mem_centralizer_iff.1 htC l (hφL c)
  have htl' : l * t * l⁻¹ = t := by rw [htl, mul_inv_cancel_right]
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    calc g₁⁻¹ * t * g₁ = l * (x⁻¹ * t * x) * l⁻¹ := by rw [hg₁def]; group
      _ = l * t * z * l⁻¹ := by rw [hxt, mul_assoc l t z]
      _ = t * (l * z * l⁻¹) := by rw [htl]; group
      _ = t * y := by rw [hy]
  obtain ⟨U', hU'⟩ := hzU'
  set ψ : CFSG.conjugate L x ≃* C := (F4Pilot.conjugateEquivSelf L x).trans e with hψ
  have hφψ : ∀ u : CFSG.conjugate L x, φ (ψ u) = x * u * x⁻¹ := by
    intro u
    simp [hφdef, hψ, F4Pilot.conjugateEquivSelf]
  set w : C := ψ ⟨z, hzLx⟩ with hw
  have hwU : ∀ u ∈ ((U'.mapSurjective (f := ψ.toMonoidHom) ψ.surjective : Sylow 2 C) :
      Subgroup C), u * w = w * u := by
    intro u hu
    change u ∈ (U' : Subgroup (CFSG.conjugate L x)).map ψ.toMonoidHom at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hw, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hU' v hv))
  have hw1 : w ≠ 1 := by
    intro h
    apply hz1
    have h' : (⟨z, hzLx⟩ : CFSG.conjugate L x) = 1 := ψ.injective (h.trans (map_one ψ).symm)
    exact congrArg Subtype.val h'
  obtain ⟨k', c', hc'⟩ := hF2 _ w hwU hw1
  set φ'₀ : C →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  set φ' : C →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'rep : φ' (rep k') = y := by
    have h1 : (MulAut.conj c'⁻¹).toMonoidHom (rep k') = w := by
      rw [← hc']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hφ'def, MonoidHom.comp_apply, h1, hφ'₀def, MonoidHom.comp_apply, hw, hφψ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hy, hg₁def]
    group
  have hact' : ∀ m ∈ CFSG.conjugate L g₁, t * m * t⁻¹ = φ' (rep k') * m * (φ' (rep k'))⁻¹ := by
    intro m hm
    rw [hφ'rep, hy]
    have hm' : l⁻¹ * m * l ∈ CFSG.conjugate L x := by
      rw [SeitzQ2.mem_conjugate_iff_conj_mem] at hm ⊢
      have e' : x * (l⁻¹ * m * l) * x⁻¹ = g₁ * m * g₁⁻¹ := by rw [hg₁def]; group
      rw [e']
      exact hm
    have h := hact _ hm'
    calc t * m * t⁻¹ = (l * t * l⁻¹) * m * (l * t * l⁻¹)⁻¹ := by rw [htl']
      _ = l * (t * (l⁻¹ * m * l) * t⁻¹) * l⁻¹ := by group
      _ = l * (z * (l⁻¹ * m * l) * z⁻¹) * l⁻¹ := by rw [h]
      _ = l * z * l⁻¹ * m * (l * z * l⁻¹)⁻¹ := by group
  have hΛ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r
    (Or.inr hg₁) hact'
  rw [hF3 k, hF3 k'] at hΛ
  have hXJ' : X ≤ J.map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨hQeq, ι, hspec, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ'
    (hQ k) (hQ k') (hM k) (hM k') (hMN k) (hMN k') (hQM k) (hQM k') hΛ (hJ k) hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  set β : (Q k ⊔ M k : Subgroup C) ≃* (Q k' ⊔ M k' : Subgroup C) :=
    ((Q k ⊔ M k).equivMapOfInjective φ hφ).trans
      ((MulEquiv.subgroupCongr hΛ).trans ((Q k' ⊔ M k').equivMapOfInjective φ' hφ').symm)
    with hβdef
  have hβφ : ∀ y : (Q k ⊔ M k : Subgroup C), φ' (β y) = φ y := by
    intro y
    have h1 : ((Q k' ⊔ M k').equivMapOfInjective φ' hφ') (β y) =
        MulEquiv.subgroupCongr hΛ ((Q k ⊔ M k).equivMapOfInjective φ hφ y) := by
      rw [hβdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [coe_equivMapOfInjective_apply] at h2
    rw [h2]
    rfl
  have hβQ : ∀ y : (Q k ⊔ M k : Subgroup C), ((β y : C) ∈ Q k' ↔ (y : C) ∈ Q k) := by
    intro y
    rw [← mem_map_iff_mem hφ' (K := Q k'), hβφ, ← hQeq, mem_map_iff_mem hφ]
  have hιβ : ∀ m : M k, ((ι m : C))⁻¹ * (β (inclusion le_sup_right m) : C) ∈ Q k' := by
    intro m
    have h1 := hspec m
    have h3 : φ (m : C) = φ' (β (inclusion le_sup_right m)) :=
      (hβφ (inclusion le_sup_right m)).symm
    rw [hQeq, h3, ← map_inv φ', ← map_mul φ', mem_map_iff_mem hφ'] at h1
    exact h1
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    F4Pilot.exists_le_range_inf_centralizer_perfectCore_of_le_conj hφ' hq₀' hXq
  obtain ⟨eD⟩ := hF56 k k' β hβQ ι hιβ
  refine ⟨k, g₁, hrep1, hg₁, P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  exact (hP.trans inf_le_left).trans (hφ'r ▸ EPilot.conjugate_le_centralizer_conj htC g₁)

theorem not_normal_map_oddCore_of_twoSided_compat (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {x z : G} (hzL : z ∈ L)
    (hzLx : z ∈ CFSG.conjugate L x) (hxt : x⁻¹ * t * x = t * z) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hzU' : ∃ U' : Sylow 2 (CFSG.conjugate L x),
      ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u)
    (hact : ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF2 : ∀ (U : Sylow 2 C) (w : C), (∀ u ∈ (U : Subgroup C), u * w = w * u) → w ≠ 1 →
      ∃ (k : κ) (c : C), c * w * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {DC : Subgroup C} (hrepD : ∀ k, rep k ∈ DC)
    (hF56 : ∀ (k k' : κ) (β : (Q k ⊔ M k : Subgroup C) ≃* (Q k' ⊔ M k' : Subgroup C)),
      (∀ y : (Q k ⊔ M k : Subgroup C), ((β y : C) ∈ Q k' ↔ (y : C) ∈ Q k)) →
      ∀ ι : M k ≃* M k',
      (∀ m : M k, ((ι m : C))⁻¹ * (β (inclusion le_sup_right m) : C) ∈ Q k') →
      Nonempty (perfectCore (centralizer
        ((((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype : Subgroup C) : Set C)) ≃*
          DC))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    (hDX : (DC.map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple ((DC.map e.symm.toMonoidHom).map L.subtype))
    (hZD : center ((DC.map e.symm.toMonoidHom).map L.subtype) = ⊥)
    (hOutD : Group.IsSolvable (Outer ((DC.map e.symm.toMonoidHom).map L.subtype)))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((((DC.map e.symm.toMonoidHom).map L.subtype).subgroupOf
          (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((((DC.map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨k, g, hrep1, hg, P, hP, ⟨eP⟩⟩ := exists_le_centralizer_perfectCore_of_twoSided_compat
    hset hOut e htC ht hzL hzLx hxt hz1 hzU hzU' hact rep hF2 Q M hF3 hQ hMN hQM hM hJ hF56 hXodd
    hXJ
  set DG := (DC.map e.symm.toMonoidHom).map L.subtype with hDG
  have hDGL : DG ≤ L := map_subtype_le _
  have hDt : DG ≤ centralizer ({t} : Set G) := hDGL.trans (le_centralizer_of_mem_centralizer htC)
  have hyD : (e.symm (rep k) : G) ∈ DG := ⟨e.symm (rep k), ⟨rep k, hrepD k, rfl⟩, rfl⟩
  have hy1 : (e.symm (rep k) : G) ≠ 1 := by
    intro h
    apply hrep1
    have h' : e.symm (rep k) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (rep k), h', map_one]
  have eDG : DC ≃* DG :=
    (DC.equivMapOfInjective _ e.symm.injective).trans
      ((DC.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX hDq hZD hOutD hDt hsyl
    hyD hy1 (Or.inr hg) hP ⟨eP.trans eDG⟩

end Skeleton

end CFSG.SeitzReduction.SymplecticPilot
