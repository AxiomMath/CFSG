module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionCore
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem range_subtype_comp_mulEquiv_symm {C : Type*} [Group C] (e : L ≃* C) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact (e.symm c).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

theorem exists_conj_le_centralizer_mulEquiv_of_inner (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hHR4 : ∃ g : G, g⁻¹ * t * g ≠ t ∧ g⁻¹ * t * g ∈ L ⊔ zpowers t)
    (hinner : ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ L ⊔ zpowers t →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF1 : ∀ x : C, orderOf x = 2 → ∃ (k : κ) (c : C), c * x * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {D : Type*} [Group D]
    (hF56 : ∀ (k k' : κ) (ι : M k ≃* M k'), Nonempty (centralizer
      ((((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype : Subgroup C) : Set C) ≃* D))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype) :
    ∃ (k : κ) (g : G), rep k ≠ 1 ∧
      (g⁻¹ * t * g = (e.symm (rep k) : G) ∨ g⁻¹ * t * g = t * (e.symm (rep k) : G)) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧
        Nonempty (P ≃* D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_mulEquiv_symm e
  have hφL : ∀ c : C, φ c ∈ L := fun c => hφr ▸ ⟨c, rfl⟩
  obtain ⟨g, hne, hmem⟩ := hHR4
  obtain ⟨y, hyL, hy2, hgy⟩ := exists_involution_of_conj_mem_sup_zpowers ht htC hne hmem
  have hx2 : orderOf (e ⟨y, hyL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk, hy2]
  obtain ⟨k, c, hc⟩ := hF1 _ hx2
  have hφx : φ (e ⟨y, hyL⟩) = y := by simp [hφdef]
  have hrep1 : rep k ≠ 1 := by
    intro h1
    have hx1 : e ⟨y, hyL⟩ = 1 := by
      have h' : c * e ⟨y, hyL⟩ * c⁻¹ = 1 := hc.trans h1
      have : e ⟨y, hyL⟩ = c⁻¹ * (c * e ⟨y, hyL⟩ * c⁻¹) * c := by group
      rw [this, h']
      group
    rw [hx1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = φ (rep k) ∨ g₁⁻¹ * t * g₁ = t * φ (rep k) := by
    have h := conj_mul_inv_eq_or_eq_mul htC (hφL c) hgy
    have hrep : φ c * y * (φ c)⁻¹ = φ (rep k) := by
      rw [← hc, map_mul, map_mul, map_inv, hφx]
    rwa [hrep] at h
  have htc : φ c * t = t * φ c := mem_centralizer_iff.1 htC _ (hφL c)
  have hne₁ : g₁⁻¹ * t * g₁ ≠ t := by
    intro h
    apply hne
    have e1 : g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by
      rw [hg₁def]
      group
    rw [e1] at h
    calc g⁻¹ * t * g = (φ c)⁻¹ * (φ c * (g⁻¹ * t * g) * (φ c)⁻¹) * φ c := by group
      _ = (φ c)⁻¹ * (t * φ c) := by rw [h, mul_assoc]
      _ = t := by rw [← htc]; group
  have hmem₁ : g₁⁻¹ * t * g₁ ∈ L ⊔ zpowers t := by
    rcases hg₁ with h | h <;> rw [h]
    · exact mem_sup_left (hφL _)
    · exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hφL _))
  obtain ⟨w', hw'L, hact⟩ := hinner g₁ hne₁ hmem₁
  have hw'2 : orderOf w' = 2 := orderOf_eq_two_of_inner ht hKt (hφL (rep k)) hg₁ hne₁ hw'L hact
  set φ'₀ : C →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  obtain ⟨x', hx'⟩ : w' ∈ φ'₀.range := hφ'₀r ▸ hw'L
  have hx'2 : orderOf x' = 2 := by rw [← orderOf_injective φ'₀ hφ'₀ x', hx', hw'2]
  obtain ⟨k', c', hc'⟩ := hF1 x' hx'2
  set φ' : C →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'rep : φ' (rep k') = w' := by
    rw [hφ'def, MonoidHom.comp_apply, ← hc', ← hx']
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ := map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r hg₁
    (by rw [hφ'rep]; exact hact)
  rw [hF3 k, hF3 k'] at hΛ
  have hXJ' : X ≤ J.map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨ι, -, P, hP, ⟨eP⟩⟩ := exists_le_centralizer_mulEquiv_of_two_decompositions hφ hφ'
    (hQ k) (hQ k') (hM k) (hM k') (hMN k) (hMN k') (hQM k) (hQM k') hΛ (hJ k) hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  obtain ⟨eD⟩ := hF56 k k' ι
  refine ⟨k, g₁, hrep1, hg₁, P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  exact (hP.trans inf_le_left).trans (hφ'r ▸ conjugate_le_centralizer_conj htC g₁)

theorem not_normal_map_oddCore_of_inner (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hHR4 : ∃ g : G, g⁻¹ * t * g ≠ t ∧ g⁻¹ * t * g ∈ L ⊔ zpowers t)
    (hinner : ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ L ⊔ zpowers t →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF1 : ∀ x : C, orderOf x = 2 → ∃ (k : κ) (c : C), c * x * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {DC : Subgroup C} (hrepD : ∀ k, rep k ∈ DC)
    (hF56 : ∀ (k k' : κ) (ι : M k ≃* M k'), Nonempty (centralizer
      ((((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype : Subgroup C) : Set C) ≃* DC))
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
  obtain ⟨k, g, hrep1, hg, P, hP, ⟨eP⟩⟩ := exists_conj_le_centralizer_mulEquiv_of_inner hset hOut
    e ht hKt hHR4 hinner rep hF1 Q M hF3 hQ hMN hQM hM hJ hF56 hXodd hXJ
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  set DG := (DC.map e.symm.toMonoidHom).map L.subtype with hDG
  have hDGL : DG ≤ L := map_subtype_le _
  have hDt : DG ≤ centralizer ({t} : Set G) := hDGL.trans (le_centralizer_of_mem_centralizer htK.1)
  have hyD : (e.symm (rep k) : G) ∈ DG := ⟨e.symm (rep k), ⟨rep k, hrepD k, rfl⟩, rfl⟩
  have hy1 : (e.symm (rep k) : G) ≠ 1 := by
    intro h
    apply hrep1
    have h' : e.symm (rep k) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (rep k), h', map_one]
  have eDG : DC ≃* DG :=
    (DC.equivMapOfInjective _ e.symm.injective).trans
      ((DC.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)
  exact not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX hDq hZD hOutD hDt hsyl hyD hy1
    hg hP ⟨eP.trans eDG⟩

end CFSG.SeitzReduction.EPilot
