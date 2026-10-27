module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidity
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusion

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open LinearPilot (autFixSubgroup mem_autFixSubgroup conjChart conjChart_apply conjugateToSelf
  coe_conjugateToSelf coe_conjugateToSelf_symm mem_conjugate_iff_mul_mul_inv_mem)

section Chart

variable {G : Type*} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem normalizerAut_conjChart' (e : L ≃* C) (g : G) {y : G}
    (hy : y ∈ normalizer (CFSG.conjugate L g : Set G))
    (hgy : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    E6Pilot.normalizerAut (conjChart e g) ⟨y, hy⟩ = E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgy⟩ := by
  ext p
  apply e.symm.injective
  apply Subtype.ext
  obtain ⟨l, rfl⟩ := e.surjective p
  have hp : e l = conjChart e g ((conjugateToSelf L g).symm l) := by
    rw [conjChart_apply, MulEquiv.apply_symm_apply]
  have h2 := E6Pilot.coe_symm_normalizerAut_apply e ⟨g * y * g⁻¹, hgy⟩ (e l)
  have h1 := E6Pilot.coe_symm_normalizerAut_apply (conjChart e g) ⟨y, hy⟩
    (conjChart e g ((conjugateToSelf L g).symm l))
  rw [← hp] at h1
  rw [h2]
  have h3 : e.symm (E6Pilot.normalizerAut (conjChart e g) ⟨y, hy⟩ (e l)) =
      conjugateToSelf L g ((conjChart e g).symm
        (E6Pilot.normalizerAut (conjChart e g) ⟨y, hy⟩ (e l))) := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, ← conjChart_apply, MulEquiv.apply_symm_apply]
  rw [h3, coe_conjugateToSelf, h1, MulEquiv.symm_apply_apply, hp, MulEquiv.symm_apply_apply,
    coe_conjugateToSelf_symm]
  group

theorem map_inf_centralizer_eq_autFixSubgroup' (e : L ≃* C) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    ((L ⊓ centralizer ({x} : Set G)).subgroupOf L).map e.toMonoidHom =
      autFixSubgroup (E6Pilot.normalizerAut e ⟨x, hx⟩) := by
  ext p
  obtain ⟨l, rfl⟩ := e.surjective p
  have h := E6Pilot.coe_symm_normalizerAut_apply e ⟨x, hx⟩ (e l)
  rw [MulEquiv.symm_apply_apply] at h
  rw [mem_autFixSubgroup]
  constructor
  · rintro ⟨m, hm, hml⟩
    have hml' : m = l := e.injective hml
    subst hml'
    have hm' : (m : G) ∈ L ⊓ centralizer ({x} : Set G) := hm
    have hc := mem_centralizer_singleton_iff.1 hm'.2
    apply e.symm.injective
    apply Subtype.ext
    rw [h, MulEquiv.symm_apply_apply]
    rw [← hc]
    group
  · intro hfix
    refine ⟨l, ?_, rfl⟩
    show (l : G) ∈ L ⊓ centralizer ({x} : Set G)
    refine ⟨l.2, ?_⟩
    rw [hfix, MulEquiv.symm_apply_apply] at h
    show (l : G) ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc (l : G) * x = (x * l * x⁻¹) * x := by rw [← h]
      _ = x * l := by group

omit [Group C] in
theorem perfectCore_subgroupOf_of_le' [Finite G] {H M : Subgroup G} (hHM : H ≤ M) :
    perfectCore (H.subgroupOf M) = (perfectCore H).subgroupOf M := by
  apply map_injective M.subtype_injective
  rw [map_perfectCore, subgroupOf_map_subtype, inf_of_le_left hHM,
    subgroupOf_map_subtype, inf_of_le_left ((perfectCore_le H).trans hHM)]

theorem map_perfectCore_inf_centralizer_eq' [Finite G] [Finite C] (e : L ≃* C) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    ((perfectCore (L ⊓ centralizer ({x} : Set G))).subgroupOf L).map e.toMonoidHom =
      perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨x, hx⟩)) := by
  rw [← perfectCore_subgroupOf_of_le' inf_le_left, map_perfectCore,
    map_inf_centralizer_eq_autFixSubgroup']

theorem normalizerAut_sq_eq_one' (e : L ≃* C) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hx2 : x * x = 1) : E6Pilot.normalizerAut e ⟨x, hx⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have h : (⟨x, hx⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]
    exact hx2)
  rw [h, map_one]

theorem normalizerAut_ne_one' (e : L ≃* C) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hxC : x ∉ centralizer (L : Set G)) : E6Pilot.normalizerAut e ⟨x, hx⟩ ≠ 1 :=
  fun h => hxC ((E6Pilot.normalizerAut_eq_one_iff e _).1 h)

end Chart

section Defs

variable {C : Type*} [Group C] {K : Type*} [Field K]

@[expose] def FieldRigidInOf (fp : MulAut C →* (K ≃+* K)) (X₁ X₂ : Subgroup C) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : C →* Γ),
    Function.Injective φ₁ → Function.Injective φ₂ → X₁.map φ₁ = X₂.map φ₂ →
      ∀ (γ : Γ) (β₁ β₂ : MulAut C), (∀ x ∈ X₁, β₁ x ∈ X₁) →
        (∀ x, φ₁ (β₁ x) = γ * φ₁ x * γ⁻¹) → (∀ x, φ₂ (β₂ x) = γ * φ₂ x * γ⁻¹) → fp β₁ = fp β₂

@[expose] def NonFieldCoresRigid (fp : MulAut C →* (K ≃+* K)) : Prop :=
  ∀ α₁ α₂ : MulAut C, α₁ ^ 2 = 1 → α₂ ^ 2 = 1 → α₁ ≠ 1 → α₂ ≠ 1 → fp α₁ = 1 → fp α₂ = 1 →
    FieldRigidInOf fp (perfectCore (autFixSubgroup α₁)) (perfectCore (autFixSubgroup α₂))

end Defs

section Reduction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C] [Finite C]
  {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem fp_eq_of_fieldRigidIn (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    (e : L ≃* C) (fp : MulAut C →* (K ≃+* K)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hrig : FieldRigidInOf fp
      (perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hg⟩)))
      (perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨g * t * g⁻¹,
        hCN (LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg)⟩))))
    {y : G} (hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y)
    (hyN : y ∈ normalizer (L : Set G)) (hgyN : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    fp (E6Pilot.normalizerAut e ⟨y, hyN⟩) = fp (E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgyN⟩) := by
  set t' := g⁻¹ * t * g with ht'
  set L' := CFSG.conjugate L g with hL'
  set Λ := perfectCore (L ⊓ centralizer ({t'} : Set G)) with hΛ
  have hsym : Λ = perfectCore (L' ⊓ centralizer ({t} : Set G)) :=
    LinearPilot.perfectCore_inf_centralizer_conj_eq hset hOut htC ht g
  have hΛL : Λ ≤ L := (perfectCore_le _).trans inf_le_left
  have hΛL' : Λ ≤ L' := by rw [hsym]; exact (perfectCore_le _).trans inf_le_left
  have hyt' : y ∈ centralizer ({t'} : Set G) := mem_centralizer_singleton_iff.2 hyt
  have hyN' : y ∈ normalizer (L' : Set G) :=
    LinearPilot.centralizer_conj_le_normalizer_conjugate hCN g hyt'
  have hyΛ : y ∈ normalizer (Λ : Set G) :=
    LinearPilot.mem_normalizer_perfectCore_inf_centralizer hyN hyt'
  have htN' : t ∈ normalizer (L' : Set G) :=
    LinearPilot.centralizer_conj_le_normalizer_conjugate hCN g
      (mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hg).symm)
  set e' := conjChart e g with he'
  set φ₁ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφ₁
  set φ₂ : C →* G := L'.subtype.comp e'.symm.toMonoidHom with hφ₂
  have hinj₁ : Function.Injective φ₁ := L.subtype_injective.comp e.symm.injective
  have hinj₂ : Function.Injective φ₂ := L'.subtype_injective.comp e'.symm.injective
  have hφe₁ : φ₁.comp e.toMonoidHom = L.subtype := by
    ext x
    simp [hφ₁]
  have hφe₂ : φ₂.comp e'.toMonoidHom = L'.subtype := by
    ext x
    simp [hφ₂]
  have hX₁ : (perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨t', hCN hg⟩))).map φ₁ = Λ := by
    rw [← map_perfectCore_inf_centralizer_eq' e (hCN hg), Subgroup.map_map, hφe₁,
      subgroupOf_map_subtype, inf_of_le_left hΛL]
  have hX₂ : (perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨g * t * g⁻¹,
      hCN (LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg)⟩))).map φ₂ = Λ := by
    rw [← normalizerAut_conjChart' e g htN', ← he', ← map_perfectCore_inf_centralizer_eq' e' htN',
      ← hsym, Subgroup.map_map, hφe₂, subgroupOf_map_subtype, inf_of_le_left hΛL']
  have h₁ : ∀ x, φ₁ (E6Pilot.normalizerAut e ⟨y, hyN⟩ x) = y * φ₁ x * y⁻¹ := by
    intro x
    have h := E6Pilot.coe_symm_normalizerAut_apply e ⟨y, hyN⟩ x
    exact h
  have h₂ : ∀ x, φ₂ (E6Pilot.normalizerAut e' ⟨y, hyN'⟩ x) = y * φ₂ x * y⁻¹ := by
    intro x
    have h := E6Pilot.coe_symm_normalizerAut_apply e' ⟨y, hyN'⟩ x
    exact h
  have hβX : ∀ x ∈ perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨t', hCN hg⟩)),
      E6Pilot.normalizerAut e ⟨y, hyN⟩ x ∈
        perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨t', hCN hg⟩)) := by
    intro x hx
    have hxΛ : φ₁ x ∈ Λ := hX₁ ▸ ⟨x, hx, rfl⟩
    have hyx : φ₁ (E6Pilot.normalizerAut e ⟨y, hyN⟩ x) ∈ Λ := by
      rw [h₁]
      exact (mem_normalizer_iff.1 hyΛ _).1 hxΛ
    rw [← hX₁] at hyx
    obtain ⟨z, hz, hzx⟩ := hyx
    rw [← hinj₁ hzx]
    exact hz
  have key := hrig G φ₁ φ₂ hinj₁ hinj₂ (hX₁.trans hX₂.symm) y _ _ hβX h₁ h₂
  rw [key, he', normalizerAut_conjChart' e g hyN' hgyN]

omit [Finite G] in
theorem conj_not_mem_centralizer' {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hne : g⁻¹ * t * g ≠ t) :
    g⁻¹ * t * g ∉ centralizer (L : Set G) :=
  LinearPilot.conj_not_mem_centralizer ht hKt hg hne

theorem fp_eq_of_nonField (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    (e : L ≃* C) (fp : MulAut C →* (K ≃+* K)) (hFR : NonFieldCoresRigid fp) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hfp : fp (E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hg⟩) = 1)
    (hfp' : fp (E6Pilot.normalizerAut e ⟨g * t * g⁻¹,
      hCN (LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg)⟩) = 1)
    {y : G} (hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y)
    (hyN : y ∈ normalizer (L : Set G)) (hgyN : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    fp (E6Pilot.normalizerAut e ⟨y, hyN⟩) = fp (E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgyN⟩) := by
  have htC := mem_centralizer_of_inf_eq hKt
  by_cases hne : g⁻¹ * t * g = t
  · have hgC : g ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * t = g * (g⁻¹ * t * g) := by rw [hne]
        _ = t * g := by group
    have hconj : (⟨g * y * g⁻¹, hgyN⟩ : normalizer (L : Set G)) =
        ⟨g, hCN hgC⟩ * ⟨y, hyN⟩ * (⟨g, hCN hgC⟩ : normalizer (L : Set G))⁻¹ := rfl
    rw [hconj, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
      LinearPilot.ringEquiv_mul_comm (fp (E6Pilot.normalizerAut e ⟨g, hCN hgC⟩)), mul_assoc,
      mul_inv_cancel, mul_one]
  have hg' : (g⁻¹)⁻¹ * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [inv_inv]
    exact LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg
  have hne' : (g⁻¹)⁻¹ * t * g⁻¹ ≠ t := by
    rw [inv_inv]
    intro h
    apply hne
    calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = t := by group
  have hC := conj_not_mem_centralizer' ht hKt hg hne
  have hC' := conj_not_mem_centralizer' ht hKt hg' hne'
  rw [inv_inv] at hC'
  refine fp_eq_of_fieldRigidIn hset hOut e fp htC ht hCN hg ?_ hyt hyN hgyN
  refine hFR _ _ (normalizerAut_sq_eq_one' e _ (LinearPilot.conj_mul_conj_eq_one ht g))
    (normalizerAut_sq_eq_one' e _ ?_) (normalizerAut_ne_one' e _ hC)
    (normalizerAut_ne_one' e _ hC') hfp hfp'
  have := LinearPilot.conj_mul_conj_eq_one ht g⁻¹
  rwa [inv_inv] at this

end Reduction

section Recentre

variable {C : Type*} [Group C] {K : Type*} [Field K]

@[expose] def FieldRecentreIn (fp : MulAut C →* (K ≃+* K)) (R : C → Prop) : Prop :=
  ∀ α β : MulAut C, α ^ 2 = 1 → fp α ≠ 1 → β ^ 2 = 1 → β ≠ 1 →
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : C →* Γ),
      Function.Injective φ₁ → Function.Injective φ₂ →
        (perfectCore (autFixSubgroup α)).map φ₁ = (perfectCore (autFixSubgroup β)).map φ₂ →
          ∃ m : C, (α m)⁻¹ * m ∈ perfectCore (autFixSubgroup α) ∧
            ∃ z : C, R z ∧ φ₂ z = φ₁ ((α m)⁻¹ * m)

end Recentre

section RecentreG

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C] [Finite C]
  {K : Type*} [Field K]

theorem exists_conj_eq_mul_of_fp_ne_one (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* C) (fp : MulAut C →* (K ≃+* K)) (R : C → Prop)
    (hRC : FieldRecentreIn fp R) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {g : G}
    (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hfp : fp (E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgC⟩) ≠ 1) :
    ∃ (h : G) (z : L), R (e z) ∧ h⁻¹ * t * h = t * (z : G) := by
  have htC := mem_centralizer_of_inf_eq hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hgtC : g * t * g⁻¹ ∈ centralizer ({t} : Set G) :=
    LinearPilot.conj_inv_mem_centralizer_self_iff.2 hgC
  have hgtN : g * t * g⁻¹ ∈ normalizer (L : Set G) := hCN hgtC
  set t' := g⁻¹ * t * g with ht'
  set L' := CFSG.conjugate L g with hL'
  set Λ := perfectCore (L ⊓ centralizer ({t'} : Set G)) with hΛ
  have hsym : Λ = perfectCore (L' ⊓ centralizer ({t} : Set G)) :=
    LinearPilot.perfectCore_inf_centralizer_conj_eq hset hOut htC ht g
  have hΛL : Λ ≤ L := (perfectCore_le _).trans inf_le_left
  have hΛL' : Λ ≤ L' := by
    rw [hsym]
    exact (perfectCore_le _).trans inf_le_left
  have htN' : t ∈ normalizer (L' : Set G) :=
    LinearPilot.centralizer_conj_le_normalizer_conjugate hCN g
      (mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hgC).symm)
  set e' := conjChart e g with he'
  set φ₁ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφ₁
  set φ₂ : C →* G := L'.subtype.comp e'.symm.toMonoidHom with hφ₂
  have hinj₁ : Function.Injective φ₁ := L.subtype_injective.comp e.symm.injective
  have hinj₂ : Function.Injective φ₂ := L'.subtype_injective.comp e'.symm.injective
  have hφe₁ : φ₁.comp e.toMonoidHom = L.subtype := by
    ext x
    simp [hφ₁]
  have hφe₂ : φ₂.comp e'.toMonoidHom = L'.subtype := by
    ext x
    simp [hφ₂]
  set α := E6Pilot.normalizerAut e ⟨t', hCN hgC⟩ with hα
  set β := E6Pilot.normalizerAut e' ⟨t, htN'⟩ with hβ
  have hX₁ : (perfectCore (autFixSubgroup α)).map φ₁ = Λ := by
    rw [hα, ← map_perfectCore_inf_centralizer_eq' e (hCN hgC), Subgroup.map_map, hφe₁,
      subgroupOf_map_subtype, inf_of_le_left hΛL]
  have hX₂ : (perfectCore (autFixSubgroup β)).map φ₂ = Λ := by
    rw [hβ, ← map_perfectCore_inf_centralizer_eq' e' htN', ← hsym, Subgroup.map_map, hφe₂,
      subgroupOf_map_subtype, inf_of_le_left hΛL']
  have hα2 : α ^ 2 = 1 :=
    normalizerAut_sq_eq_one' e (hCN hgC) (LinearPilot.conj_mul_conj_eq_one ht g)
  have hβ2 : β ^ 2 = 1 := normalizerAut_sq_eq_one' e' htN' ht2
  have hβ1 : β ≠ 1 := by
    rw [hβ, normalizerAut_conjChart' e g htN' hgtN]
    refine normalizerAut_ne_one' e hgtN fun hC => hfp ?_
    have hmem : g * t * g⁻¹ ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hC, hgtC⟩
    rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
    · exfalso
      have h0 : t = 1 := by
        have e1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
        rw [e1, h1]
        group
      rw [h0, orderOf_one] at ht
      exact absurd ht (by decide)
    · have htt : t' = t := by
        rw [ht']
        calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h1]
          _ = t := by group
      have h2 : t' ∈ centralizer (L : Set G) := htt ▸ htC
      have h3 : α = 1 := (E6Pilot.normalizerAut_eq_one_iff e _).2 h2
      rw [h3, map_one]
  obtain ⟨m, hmΛ, z, hz, hzy⟩ :=
    hRC α β hα2 hfp hβ2 hβ1 G φ₁ φ₂ hinj₁ hinj₂ (hX₁.trans hX₂.symm)
  have hαm : φ₁ (α m) = t' * φ₁ m * t'⁻¹ := E6Pilot.coe_symm_normalizerAut_apply e _ m
  set y := φ₁ ((α m)⁻¹ * m) with hy
  have ht't' : t' * t' = 1 := LinearPilot.conj_mul_conj_eq_one ht g
  have hxy : (φ₁ m)⁻¹ * t' * φ₁ m = t' * y := by
    have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht't'
    rw [hy, map_mul, map_inv, hαm]
    calc (φ₁ m)⁻¹ * t' * φ₁ m = (t' * t') * ((φ₁ m)⁻¹ * t'⁻¹ * φ₁ m) := by
          rw [ht't', one_mul, hti]
      _ = t' * ((t' * φ₁ m * t'⁻¹)⁻¹ * φ₁ m) := by group
  have hyL' : y ∈ L' := by
    rw [← hzy]
    exact (e'.symm z).2
  have hgyL : g * y * g⁻¹ ∈ L := mem_conjugate_iff_mul_mul_inv_mem.1 hyL'
  refine ⟨g * φ₁ m * g⁻¹, ⟨g * y * g⁻¹, hgyL⟩, ?_, ?_⟩
  · have hzy' : ((e'.symm z : L') : G) = y := hzy
    have h1 : (⟨g * y * g⁻¹, hgyL⟩ : L) = conjugateToSelf L g (e'.symm z) :=
      Subtype.ext (by rw [coe_conjugateToSelf, hzy'])
    rw [h1, ← conjChart_apply, ← he', MulEquiv.apply_symm_apply]
    exact hz
  · calc (g * φ₁ m * g⁻¹)⁻¹ * t * (g * φ₁ m * g⁻¹) =
          g * ((φ₁ m)⁻¹ * t' * φ₁ m) * g⁻¹ := by rw [ht']; group
      _ = g * (t' * y) * g⁻¹ := by rw [hxy]
      _ = t * (g * y * g⁻¹) := by rw [ht']; group

end RecentreG

section Residual

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C] [Finite C]
  {K : Type*} [Field K] [Finite K]

omit [Finite C] in
theorem false_of_fp_rigid (hset : SeitzSetting G L) (e : L ≃* C) (fp : MulAut C →* (K ≃+* K))
    {t : G} (ht : orderOf t = 2) (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (S : Sylow 2 G) (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hS : ∃ (s : G) (hs : s ∈ (S : Subgroup G)),
      fp (E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩) ≠ 1)
    (hrig : ∀ g y : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ≠ t →
      ∀ (hy : y ∈ normalizer (L : Set G)) (hgy : g * y * g⁻¹ ∈ normalizer (L : Set G)),
        y ∈ centralizer ({t} : Set G) → y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y →
          fp (E6Pilot.normalizerAut e ⟨y, hy⟩) = fp (E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgy⟩)) :
    False := by
  have := LinearPilot.isCyclic_ringEquiv (K := K)
  set φ : centralizer ({t} : Set G) →* (K ≃+* K) :=
    (fp.comp (E6Pilot.normalizerAut e)).comp (inclusion hCN) with hφ
  set SC : Sylow 2 (centralizer ({t} : Set G)) := S.subtype hSt with hSC
  have hφS : ∃ s ∈ (SC : Subgroup (centralizer ({t} : Set G))), φ s ≠ 1 := by
    obtain ⟨s, hs, hs1⟩ := hS
    refine ⟨⟨s, hSt hs⟩, ?_, hs1⟩
    rw [hSC, Sylow.coe_subtype, mem_subgroupOf]
    exact hs
  obtain ⟨χ, hker, s, hsS, hχs⟩ := LinearPilot.exists_zmod_two_hom_of_isCyclic φ SC hφS
  refine LinearPilot.false_of_rigid hset ht S hSt χ ⟨s, ?_, ?_⟩ fun g y hgt hy hgy hyt => ?_
  · rw [hSC, Sylow.coe_subtype, mem_subgroupOf] at hsS
    exact hsS
  · exact hχs
  · by_cases hne : g⁻¹ * t * g = t
    · have hg : g ∈ centralizer ({t} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc g * t = g * (g⁻¹ * t * g) := by rw [hne]
          _ = t * g := by group
      have hconj : (⟨g * y * g⁻¹, hgy⟩ : centralizer ({t} : Set G)) =
          ⟨g, hg⟩ * ⟨y, hy⟩ * (⟨g, hg⟩ : centralizer ({t} : Set G))⁻¹ := rfl
      rw [hconj, map_mul, map_mul, map_inv]
      exact (mul_inv_cancel_comm _ _).symm
    · have h := hrig g y hgt hne (hCN hy) (hCN hgy) hy hyt
      have hmem : (⟨y, hy⟩ : centralizer ({t} : Set G))⁻¹ * ⟨g * y * g⁻¹, hgy⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact h
      have h2 := hker hmem
      rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
      exact inv_mul_eq_one.1 h2

theorem exists_conj_eq_mul_of_residual (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* C) (fp : MulAut C →* (K ≃+* K)) (R : C → Prop)
    (hFR : NonFieldCoresRigid fp) (hRC : FieldRecentreIn fp R) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hS : ∃ (s : G) (hs : s ∈ (S : Subgroup G)),
      fp (E6Pilot.normalizerAut e ⟨s, CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
        hset.standardSetting.standard (mem_centralizer_of_inf_eq hKt) ht (hSt hs)⟩) ≠ 1) :
    ∃ (h : G) (z : L), R (e z) ∧ h⁻¹ * t * h = t * (z : G) := by
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  by_contra hno
  have hfp1 : ∀ (g : G) (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G)),
      fp (E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hg⟩) = 1 := fun g hg => by
    by_contra h
    exact hno (exists_conj_eq_mul_of_fp_ne_one hset.standardSetting hOut e fp R hRC ht hKt hCN hg h)
  refine false_of_fp_rigid hset e fp ht hCN S hSt hS fun g y hg _ hy hgy _ hyt => ?_
  have hg' : g * t * g⁻¹ ∈ centralizer ({t} : Set G) :=
    LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg
  have hfp' : fp (E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hg'⟩) = 1 := by
    have h := hfp1 g⁻¹ (by rw [inv_inv]; exact hg')
    simp only [inv_inv] at h
    exact h
  exact fp_eq_of_nonField hset.standardSetting hOut e fp hFR ht hKt hCN hg (hfp1 g hg) hfp' hyt
    hy hgy

end Residual

end CFSG.SeitzReduction.OmegaPilot
