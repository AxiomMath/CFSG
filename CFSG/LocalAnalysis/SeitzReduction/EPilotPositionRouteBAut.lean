module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteB
public import CFSG.LocalAnalysis.SeitzReduction.EPilotIntertwine
public import CFSG.LocalAnalysis.SeitzReduction.EPilotO2

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section LeviAut

variable {C : Type*} [Group C]

@[expose] def leviImage (Q M : Subgroup C) (β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C)) :
    Subgroup C :=
  ((M.subgroupOf (Q ⊔ M)).map β.toMonoidHom).map (Q ⊔ M).subtype

variable {Q M : Subgroup C} {β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C)}

theorem mem_leviImage_iff {c : C} :
    c ∈ leviImage Q M β ↔ ∃ m : M, (β (inclusion le_sup_right m) : C) = c := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, mem_subgroupOf.1 hx⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, ⟨inclusion le_sup_right m, mem_subgroupOf.2 m.2, rfl⟩, rfl⟩

theorem leviImage_le : leviImage Q M β ≤ Q ⊔ M := map_subtype_le _

theorem coe_mem_iff_of_map_eq
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M))
    (x : (Q ⊔ M : Subgroup C)) : (β x : C) ∈ Q ↔ (x : C) ∈ Q := by
  constructor
  · intro h
    have h' : β x ∈ (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom := by
      rw [hβ]
      exact mem_subgroupOf.2 h
    obtain ⟨y, hy, hyx⟩ := h'
    have hyx' : β y = β x := hyx
    rw [← β.injective hyx']
    exact mem_subgroupOf.1 hy
  · intro h
    have h' : β x ∈ Q.subgroupOf (Q ⊔ M) := by
      rw [← hβ]
      exact ⟨x, mem_subgroupOf.2 h, rfl⟩
    exact mem_subgroupOf.1 h'

theorem disjoint_leviImage (hQM : Disjoint Q M)
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) :
    Disjoint Q (leviImage Q M β) := by
  rw [disjoint_iff_inf_le]
  intro c hc
  obtain ⟨hcQ, hcM⟩ := mem_inf.1 hc
  obtain ⟨m, rfl⟩ := mem_leviImage_iff.1 hcM
  have hm : (m : C) ∈ Q := (coe_mem_iff_of_map_eq hβ (inclusion le_sup_right m)).1 hcQ
  have hm1 : m = 1 :=
    Subtype.ext (mem_bot.1 ((disjoint_iff_inf_le.1 hQM) (mem_inf.2 ⟨hm, m.2⟩)))
  subst hm1
  simp

theorem sup_leviImage (hMN : M ≤ normalizer (Q : Set C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) :
    Q ⊔ M = Q ⊔ leviImage Q M β := by
  apply le_antisymm
  · refine sup_le le_sup_left fun m hm => ?_
    set y := β.symm (inclusion le_sup_right (⟨m, hm⟩ : M)) with hydef
    have hy : (y : C) ∈ ((Q ⊔ M : Subgroup C) : Set C) := y.2
    rw [coe_mul_of_right_le_normalizer_left Q M hMN] at hy
    obtain ⟨q, hq, m₀, hm₀, hqm⟩ := hy
    have hyqm : y = ⟨q, mem_sup_left hq⟩ * inclusion le_sup_right (⟨m₀, hm₀⟩ : M) :=
      Subtype.ext hqm.symm
    have hβy : β y = inclusion le_sup_right (⟨m, hm⟩ : M) := β.apply_symm_apply _
    have e : m = (β ⟨q, mem_sup_left hq⟩ : C) *
        (β (inclusion le_sup_right (⟨m₀, hm₀⟩ : M)) : C) := by
      have h1 := congrArg Subtype.val hβy
      rw [hyqm, map_mul] at h1
      exact h1.symm
    rw [e]
    exact mul_mem (mem_sup_left ((coe_mem_iff_of_map_eq hβ _).2 hq))
      (mem_sup_right (mem_leviImage_iff.2 ⟨⟨m₀, hm₀⟩, rfl⟩))
  · exact sup_le le_sup_left leviImage_le

variable (Q M β) in
@[expose] noncomputable def leviImageEquiv : M ≃* leviImage Q M β :=
  (subgroupOfEquivOfLe (le_sup_right : M ≤ Q ⊔ M)).symm.trans
    (((M.subgroupOf (Q ⊔ M)).equivMapOfInjective β.toMonoidHom β.injective).trans
      (((M.subgroupOf (Q ⊔ M)).map β.toMonoidHom).equivMapOfInjective (Q ⊔ M).subtype
        (Q ⊔ M).subtype_injective))

theorem coe_leviImageEquiv (m : M) :
    (leviImageEquiv Q M β m : C) = (β (inclusion le_sup_right m) : C) := rfl

variable (Q M) in
@[expose] noncomputable def leviAutOfAut (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    (β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) : M ≃* M :=
  (leviImageEquiv Q M β).trans
    (mulEquivOfComplements hMN hQM (disjoint_leviImage hQM hβ) (sup_leviImage hMN hβ)).symm

theorem inv_mul_leviAutOfAut_mem (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) (m : M) :
    (β (inclusion le_sup_right m) : C)⁻¹ * (leviAutOfAut Q M hQM hMN β hβ m : C) ∈ Q := by
  set ι₀ := mulEquivOfComplements hMN hQM (disjoint_leviImage hQM hβ) (sup_leviImage hMN hβ)
    with hι₀
  have h := mulEquivOfComplements_inv_mul_mem hMN hQM (disjoint_leviImage hQM hβ)
    (sup_leviImage hMN hβ) (leviAutOfAut Q M hQM hMN β hβ m)
  have e : ι₀ (leviAutOfAut Q M hQM hMN β hβ m) = leviImageEquiv Q M β m :=
    ι₀.apply_symm_apply _
  rw [← hι₀, e, coe_leviImageEquiv] at h
  exact h

theorem leviAutOfAut_inv_mul_mem (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) (m : M) :
    (leviAutOfAut Q M hQM hMN β hβ m : C)⁻¹ * (β (inclusion le_sup_right m) : C) ∈ Q := by
  have h := Q.inv_mem (inv_mul_leviAutOfAut_mem hQM hMN hβ m)
  rwa [mul_inv_rev, inv_inv] at h

theorem leviAutOfAut_eq_iff (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) (m m' : M) :
    leviAutOfAut Q M hQM hMN β hβ m = m' ↔
      (m' : C)⁻¹ * (β (inclusion le_sup_right m) : C) ∈ Q := by
  constructor
  · rintro rfl
    exact leviAutOfAut_inv_mul_mem hQM hMN hβ m
  · intro h
    set ι := leviAutOfAut Q M hQM hMN β hβ with hι
    have h1 := leviAutOfAut_inv_mul_mem hQM hMN hβ m
    rw [← hι] at h1
    have h2 : (m' : C)⁻¹ * (ι m : C) ∈ Q ⊓ M := by
      refine ⟨?_, M.mul_mem (M.inv_mem m'.2) (ι m).2⟩
      have e : (m' : C)⁻¹ * (ι m : C) = ((m' : C)⁻¹ * (β (inclusion le_sup_right m) : C)) *
          ((ι m : C)⁻¹ * (β (inclusion le_sup_right m) : C))⁻¹ := by group
      rw [e]
      exact Q.mul_mem h (Q.inv_mem h1)
    rw [disjoint_iff.1 hQM, mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2.symm

theorem leviAutOfAut_conj_eq (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M))
    (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (m : M) (q : (Q ⊔ M : Subgroup C))
    (hq : (q : C) ∈ Q) :
    (leviAutOfAut Q M hQM hMN β hβ m : C) * (β q : C) *
        (leviAutOfAut Q M hQM hMN β hβ m : C)⁻¹ =
      (β (inclusion le_sup_right m * q * (inclusion le_sup_right m)⁻¹) : C) := by
  rw [map_mul, map_mul, map_inv]
  simp only [coe_mul, coe_inv]
  exact conj_eq_conj_of_inv_mul_mem hQ (inv_mul_leviAutOfAut_mem hQM hMN hβ m)
    ((coe_mem_iff_of_map_eq hβ q).2 hq)

theorem leviAutOfAut_commutatorElement_eq (hQM : Disjoint Q M)
    (hMN : M ≤ normalizer (Q : Set C))
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M))
    (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (m : M) (q : (Q ⊔ M : Subgroup C))
    (hq : (q : C) ∈ Q) :
    ⁅(β q : C), (leviAutOfAut Q M hQM hMN β hβ m : C)⁆ =
      (β ⁅q, inclusion le_sup_right m⁆ : C) := by
  have h := conj_eq_conj_of_inv_mul_mem hQ (inv_mul_leviAutOfAut_mem hQM hMN hβ m)
    (Q.inv_mem ((coe_mem_iff_of_map_eq hβ q).2 hq))
  rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  simp only [coe_mul, coe_inv]
  calc (β q : C) * (leviAutOfAut Q M hQM hMN β hβ m : C) * (β q : C)⁻¹ *
        (leviAutOfAut Q M hQM hMN β hβ m : C)⁻¹
      = (β q : C) * ((leviAutOfAut Q M hQM hMN β hβ m : C) * (β q : C)⁻¹ *
          (leviAutOfAut Q M hQM hMN β hβ m : C)⁻¹) := by group
    _ = (β q : C) * ((β (inclusion le_sup_right m) : C) * (β q : C)⁻¹ *
          (β (inclusion le_sup_right m) : C)⁻¹) := by rw [h]
    _ = (β q : C) * (β (inclusion le_sup_right m) : C) * (β q : C)⁻¹ *
          (β (inclusion le_sup_right m) : C)⁻¹ := by group

end LeviAut

section Coordinates

variable {G : Type*} [Group G] {L : Subgroup G}

theorem exists_eq_conj_of_mem_conjugate {C : Type*} [Group C] (e : L ≃* C) {g w' : G}
    (hw' : w' ∈ CFSG.conjugate L g) : ∃ x' : C, g⁻¹ * (e.symm x' : G) * g = w' := by
  obtain ⟨l, hl, rfl⟩ := hw'
  refine ⟨e ⟨l, hl⟩, ?_⟩
  simp

theorem orderOf_conj_symm {C : Type*} [Group C] (e : L ≃* C) (g : G) (x : C) :
    orderOf (g⁻¹ * (e.symm x : G) * g) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (e.symm x : G)
  rw [MulAut.conj_apply, inv_inv] at h
  rw [h, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem exists_coords_conjugate {C : Type*} [Group C] (e : L ≃* C) (g : G) {x' y' c' : C}
    (hc' : c' * x' * c'⁻¹ = y') :
    ∃ φ' : C →* G, Function.Injective φ' ∧ φ'.range = CFSG.conjugate L g ∧
      φ' y' = g⁻¹ * (e.symm x' : G) * g := by
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := by
    ext a
    constructor
    · rintro ⟨c, rfl⟩
      exact (e.symm c).2
    · intro ha
      exact ⟨e ⟨a, ha⟩, by simp [hφdef]⟩
  set φ'₀ : C →* G := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  refine ⟨φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom, hφ'₀.comp (MulAut.conj c'⁻¹).injective, ?_,
    ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  · have e1 : (MulAut.conj c'⁻¹).toMonoidHom y' = x' := by
      rw [← hc']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [MonoidHom.comp_apply, e1, hφ'₀def, MonoidHom.comp_apply]
    simp [hφdef]

theorem not_mem_closure_odd_of_map {C : Type*} [Group C] {φ : C →* G}
    (hφ : Function.Injective φ) {H : Subgroup G} (hH : φ.range ≤ H) {x : C}
    (h : φ x ∉ closure {y : G | y ∈ H ⊓ centralizer ({φ x} : Set G) ∧ Odd (orderOf y)}) :
    x ∉ closure {c : C | c ∈ centralizer ({x} : Set C) ∧ Odd (orderOf c)} := by
  intro hx
  apply h
  have hle : (closure {c : C | c ∈ centralizer ({x} : Set C) ∧ Odd (orderOf c)}).map φ ≤
      closure {y : G | y ∈ H ⊓ centralizer ({φ x} : Set G) ∧ Odd (orderOf y)} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨c, ⟨hcx, hco⟩, rfl⟩
    refine ⟨mem_inf.2 ⟨hH ⟨c, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff] at hcx ⊢
      rw [← map_mul, ← map_mul, hcx]
    · rw [orderOf_injective φ hφ c]
      exact hco
  exact hle ⟨x, hx, rfl⟩

end Coordinates

section RouteB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_le_centralizer_mulEquiv_of_coords_aut (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {g : G} {κ : Type*}
    (rep : κ → C) {k k' : κ}
    (hg : g⁻¹ * t * g = (e.symm (rep k) : G) ∨ g⁻¹ * t * g = t * (e.symm (rep k) : G))
    {φ' : C →* G} (hφ' : Function.Injective φ') (hφ'r : φ'.range = CFSG.conjugate L g)
    (hact : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = φ' (rep k') * l * (φ' (rep k'))⁻¹)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k)
    (hsame : ∀ k₁ k₂, Nonempty ((Q k₁ ⊔ M k₁ : Subgroup C) ≃* (Q k₂ ⊔ M k₂ : Subgroup C)) →
      k₁ = k₂)
    {D : Type*} [Group D]
    (hF5 : ∀ k (β : (Q k ⊔ M k : Subgroup C) ≃* (Q k ⊔ M k : Subgroup C))
      (hβ : ((Q k).subgroupOf (Q k ⊔ M k)).map β.toMonoidHom = (Q k).subgroupOf (Q k ⊔ M k)),
      Nonempty (centralizer ((((J.subgroupOf (M k)).map
        (leviAutOfAut (Q k) (M k) (hQM k) (hMN k) β hβ).toMonoidHom).map (M k).subtype :
          Subgroup C) : Set C) ≃* D))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype) :
    ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧
      Nonempty (P ≃* D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_mulEquiv_symm e
  have hg' : g⁻¹ * t * g = φ (rep k) ∨ g⁻¹ * t * g = t * φ (rep k) := hg
  have hΛ := map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r hg' hact
  rw [hF3 k, hF3 k'] at hΛ
  obtain rfl : k = k' := hsame k k' ⟨((Q k ⊔ M k).equivMapOfInjective φ hφ).trans
    ((MulEquiv.subgroupCongr hΛ).trans ((Q k' ⊔ M k').equivMapOfInjective φ' hφ').symm)⟩
  have hXJ' : X ≤ J.map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  have hX2 : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h)
  obtain ⟨hQeq, ι, hspec, q₀, hq₀, hXq⟩ := exists_conj_le_map_of_two_decompositions hφ hφ'
    (hQ k) (hQ k) (hM k) (hM k) (hMN k) (hMN k) (hQM k) (hQM k) hΛ (hJ k) hXJ' hX2
  set β : (Q k ⊔ M k : Subgroup C) ≃* (Q k ⊔ M k : Subgroup C) :=
    ((Q k ⊔ M k).equivMapOfInjective φ hφ).trans
      ((MulEquiv.subgroupCongr hΛ).trans ((Q k ⊔ M k).equivMapOfInjective φ' hφ').symm)
    with hβdef
  have hβφ : ∀ x : (Q k ⊔ M k : Subgroup C), φ' (β x) = φ x := by
    intro x
    have h1 : ((Q k ⊔ M k).equivMapOfInjective φ' hφ') (β x) =
        MulEquiv.subgroupCongr hΛ ((Q k ⊔ M k).equivMapOfInjective φ hφ x) := by
      rw [hβdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [coe_equivMapOfInjective_apply] at h2
    rw [h2]
    rfl
  have hβmem : ∀ x : (Q k ⊔ M k : Subgroup C), ((β x : C) ∈ Q k ↔ (x : C) ∈ Q k) := by
    intro x
    rw [← mem_map_iff_mem hφ' (K := Q k), hβφ, ← hQeq, mem_map_iff_mem hφ]
  have hβ : ((Q k).subgroupOf (Q k ⊔ M k)).map β.toMonoidHom =
      (Q k).subgroupOf (Q k ⊔ M k) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_subgroupOf.2 ((hβmem y).2 (mem_subgroupOf.1 hy))
    · intro hx
      refine ⟨β.symm x, mem_subgroupOf.2 ?_, by simp⟩
      rw [← hβmem, MulEquiv.apply_symm_apply]
      exact mem_subgroupOf.1 hx
  have hι : ι = leviAutOfAut (Q k) (M k) (hQM k) (hMN k) β hβ := by
    refine MulEquiv.ext fun m => ?_
    symm
    rw [leviAutOfAut_eq_iff]
    have h1 := hspec m
    have h3 : φ (m : C) = φ' (β (inclusion le_sup_right m)) :=
      (hβφ (inclusion le_sup_right m)).symm
    rw [hQeq, h3, ← map_inv φ', ← map_mul φ', mem_map_iff_mem hφ'] at h1
    exact h1
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_range_inf_centralizer_of_le_conj hφ' hq₀' hXq
  subst hι
  obtain ⟨eD⟩ := hF5 k β hβ
  refine ⟨P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  exact (hP.trans inf_le_left).trans (hφ'r ▸ conjugate_le_centralizer_conj htC g)

theorem exists_conj_le_centralizer_mulEquiv_of_fusion_aut (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {g : G} {κ : Type*} (rep : κ → C) {k : κ}
    (hg : g⁻¹ * t * g = (e.symm (rep k) : G) ∨ g⁻¹ * t * g = t * (e.symm (rep k) : G))
    (hne : g⁻¹ * t * g ≠ t)
    (hinner : ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g,
      t * l * t⁻¹ = w' * l * w'⁻¹)
    (hF1 : ∀ x : C, orderOf x = 2 → ∃ (k' : κ) (c : C), c * x * c⁻¹ = rep k')
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k)
    (hsame : ∀ k₁ k₂, Nonempty ((Q k₁ ⊔ M k₁ : Subgroup C) ≃* (Q k₂ ⊔ M k₂ : Subgroup C)) →
      k₁ = k₂)
    {D : Type*} [Group D]
    (hF5 : ∀ k (β : (Q k ⊔ M k : Subgroup C) ≃* (Q k ⊔ M k : Subgroup C))
      (hβ : ((Q k).subgroupOf (Q k ⊔ M k)).map β.toMonoidHom = (Q k).subgroupOf (Q k ⊔ M k)),
      Nonempty (centralizer ((((J.subgroupOf (M k)).map
        (leviAutOfAut (Q k) (M k) (hQM k) (hMN k) β hβ).toMonoidHom).map (M k).subtype :
          Subgroup C) : Set C) ≃* D))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype) :
    ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧
      Nonempty (P ≃* D) := by
  have htC := mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  obtain ⟨w', hw'L, hact⟩ := hinner
  have hw'2 : orderOf w' = 2 :=
    orderOf_eq_two_of_inner ht hKt (e.symm (rep k)).2 hg hne hw'L hact
  obtain ⟨x', hx'⟩ := exists_eq_conj_of_mem_conjugate e hw'L
  have hx'2 : orderOf x' = 2 := by rw [← orderOf_conj_symm e g x', hx', hw'2]
  obtain ⟨k', c', hc'⟩ := hF1 x' hx'2
  obtain ⟨φ', hφ', hφ'r, hφ'rep⟩ := exists_coords_conjugate e g hc'
  rw [hx'] at hφ'rep
  exact exists_le_centralizer_mulEquiv_of_coords_aut hset hOut e ht htC rep hg hφ' hφ'r
    (by rw [hφ'rep]; exact hact) Q M hF3 hQ hMN hQM hM hJ hsame hF5 hXodd hXJ

theorem exists_conj_le_centralizer_mulEquiv_of_conj_mem_aut (hset : StandardSetting G L)
    (hOut : IsCyclic (Outer L)) (hZ : center L = ⊥) {C : Type*} [Group C] (e : L ≃* C)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {g : G} (hw : g⁻¹ * t * g ∈ L)
    (hinner : ∀ g : G, g⁻¹ * t * g ∈ L →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF1 : ∀ x : C, orderOf x = 2 →
      x ∉ closure {c : C | c ∈ centralizer ({x} : Set C) ∧ Odd (orderOf c)} →
        ∃ (k : κ) (c : C), c * x * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k)
    (hsame : ∀ k₁ k₂, Nonempty ((Q k₁ ⊔ M k₁ : Subgroup C) ≃* (Q k₂ ⊔ M k₂ : Subgroup C)) →
      k₁ = k₂)
    {D : Type*} [Group D]
    (hF5 : ∀ k (β : (Q k ⊔ M k : Subgroup C) ≃* (Q k ⊔ M k : Subgroup C))
      (hβ : ((Q k).subgroupOf (Q k ⊔ M k)).map β.toMonoidHom = (Q k).subgroupOf (Q k ⊔ M k)),
      Nonempty (centralizer ((((J.subgroupOf (M k)).map
        (leviAutOfAut (Q k) (M k) (hQM k) (hMN k) β hβ).toMonoidHom).map (M k).subtype :
          Subgroup C) : Set C) ≃* D))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype) :
    ∃ (k : κ) (g₁ : G), g₁⁻¹ * t * g₁ = (e.symm (rep k) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
        Nonempty (P ≃* D) := by
  classical
  have htC := mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have hOut' : Group.IsSolvable (Outer L) := inferInstance
  have htL : t ∉ L := not_mem_of_mem_centralizer_of_center_eq_bot htC hZ (by
    rintro rfl
    simp at ht)
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_mulEquiv_symm e
  have hφL : ∀ c : C, φ c ∈ L := fun c => hφr ▸ ⟨c, rfl⟩
  have hφx : φ (e ⟨g⁻¹ * t * g, hw⟩) = g⁻¹ * t * g := by simp [hφdef]
  have hx2 : orderOf (e ⟨g⁻¹ * t * g, hw⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  have hxodd := not_mem_closure_odd_of_map hφ hφr.le (x := e ⟨g⁻¹ * t * g, hw⟩)
    (by rw [hφx]; exact not_mem_closure_odd_of_conj_mem ht hKt hCN hZ hOut g)
  obtain ⟨k, c, hc⟩ := hF1 _ hx2 hxodd
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = φ (rep k) := by
    rw [← hc, map_mul, map_mul, map_inv, hφx, hg₁def]
    group
  have hw₁ : g₁⁻¹ * t * g₁ ∈ L := by
    rw [hg₁]
    exact hφL _
  have hne₁ : g₁⁻¹ * t * g₁ ≠ t := fun h => htL (h ▸ hw₁)
  obtain ⟨w', hw'L, hact⟩ := hinner g₁ hw₁
  have htw' := eq_or_eq_mul_conj_of_inner ht hKt hw₁ (Or.inl rfl) hw'L hact
  have hw'2 : orderOf w' = 2 := orderOf_eq_two_of_inner ht hKt hw₁ (Or.inl rfl) hne₁ hw'L hact
  have hw'odd := not_mem_closure_odd_of_inner ht hKt hCN hZ hOut hw₁ htw'
  obtain ⟨x', hx'⟩ := exists_eq_conj_of_mem_conjugate e hw'L
  have hx'2 : orderOf x' = 2 := by rw [← orderOf_conj_symm e g₁ x', hx', hw'2]
  obtain ⟨φ'₀, hφ'₀, hφ'₀r, hφ'₀x⟩ :=
    exists_coords_conjugate e g₁ (x' := x') (c' := 1) (by rw [one_mul, inv_one, mul_one])
  rw [hx'] at hφ'₀x
  have hx'odd := not_mem_closure_odd_of_map hφ'₀ hφ'₀r.le (x := x')
    (by rw [hφ'₀x]; exact hw'odd)
  obtain ⟨k', c', hc'⟩ := hF1 x' hx'2 hx'odd
  obtain ⟨φ', hφ', hφ'r, hφ'rep⟩ := exists_coords_conjugate e g₁ hc'
  rw [hx'] at hφ'rep
  obtain ⟨P, hP, hPD⟩ := exists_le_centralizer_mulEquiv_of_coords_aut hset hOut' e ht htC rep
    (k := k) (k' := k') (Or.inl hg₁) hφ' hφ'r (by rw [hφ'rep]; exact hact) Q M hF3 hQ hMN hQM
    hM hJ hsame hF5 hXodd hXJ
  exact ⟨k, g₁, hg₁, P, hP, hPD⟩

end RouteB

end CFSG.SeitzReduction.EPilot
