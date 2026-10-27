module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualRigid

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

theorem normalizerAut_trans (e : L ≃* C) (δ : MulAut C) (x : normalizer (L : Set G)) :
    E6Pilot.normalizerAut (e.trans δ) x = δ * E6Pilot.normalizerAut e x * δ⁻¹ := by
  ext c
  rfl

end Chart

section Defs

variable {C : Type*} [Group C] {K : Type*} [Field K]

@[expose] def ConjIntoIn (E : Subgroup (MulAut C)) : Prop :=
  ∀ B : Subgroup (MulAut C), IsPGroup 2 B →
    ∃ δ : MulAut C, B.map (MulAut.conj δ).toMonoidHom ≤ E

@[expose] def FusionStableIn (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) : Prop :=
  ∀ (β γ : MulAut C) (hβ : β ∈ E) (hγ : γ * β * γ⁻¹ ∈ E), fp ⟨γ * β * γ⁻¹, hγ⟩ = fp ⟨β, hβ⟩

@[expose] def FieldRigidInOfE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K))
    (X₁ X₂ : Subgroup C) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : C →* Γ),
    Function.Injective φ₁ → Function.Injective φ₂ → X₁.map φ₁ = X₂.map φ₂ →
      ∀ (γ : Γ) (β₁ β₂ : MulAut C) (h₁ : β₁ ∈ E) (h₂ : β₂ ∈ E), (∀ x ∈ X₁, β₁ x ∈ X₁) →
        (∀ x, φ₁ (β₁ x) = γ * φ₁ x * γ⁻¹) → (∀ x, φ₂ (β₂ x) = γ * φ₂ x * γ⁻¹) →
          fp ⟨β₁, h₁⟩ = fp ⟨β₂, h₂⟩

@[expose] def NonFieldCoresRigidE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) : Prop :=
  ∀ (α₁ α₂ : MulAut C) (h₁ : α₁ ∈ E) (h₂ : α₂ ∈ E), α₁ ^ 2 = 1 → α₂ ^ 2 = 1 → α₁ ≠ 1 →
    α₂ ≠ 1 → fp ⟨α₁, h₁⟩ = 1 → fp ⟨α₂, h₂⟩ = 1 →
      FieldRigidInOfE E fp (perfectCore (autFixSubgroup α₁)) (perfectCore (autFixSubgroup α₂))

@[expose] def FieldRecentreInE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) (R : C → Prop) :
    Prop :=
  ∀ (α β : MulAut C) (hα : α ∈ E), β ∈ E → α ^ 2 = 1 → fp ⟨α, hα⟩ ≠ 1 → β ^ 2 = 1 → β ≠ 1 →
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : C →* Γ),
      Function.Injective φ₁ → Function.Injective φ₂ →
        (perfectCore (autFixSubgroup α)).map φ₁ = (perfectCore (autFixSubgroup β)).map φ₂ →
          ∃ m : C, (α m)⁻¹ * m ∈ perfectCore (autFixSubgroup α) ∧
            ∃ z : C, R z ∧ φ₂ z = φ₁ ((α m)⁻¹ * m)

theorem exists_conj_mem_of_sq_eq_one {E : Subgroup (MulAut C)} (h2 : ConjIntoIn E)
    {α : MulAut C} (hα : α ^ 2 = 1) : ∃ δ : MulAut C, δ * α * δ⁻¹ ∈ E := by
  have hp : IsPGroup 2 (zpowers α) := by
    rintro ⟨x, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (α ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  obtain ⟨δ, hδ⟩ := h2 _ hp
  exact ⟨δ, hδ ⟨α, mem_zpowers α, rfl⟩⟩

end Defs

section RecentreG

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C] [Finite C]
  {K : Type*} [Field K]

theorem exists_conj_eq_mul_of_fp_ne_one_E (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* C) (E : Subgroup (MulAut C))
    (fp : E →* (K ≃+* K)) (R : C → Prop) (h2 : ConjIntoIn E)
    (hR : ∀ (δ : MulAut C) (z : C), R z → R (δ z)) (hRC : FieldRecentreInE E fp R) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {g : G}
    (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hE : E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgC⟩ ∈ E) (hfp : fp ⟨_, hE⟩ ≠ 1) :
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
  set β₀ := E6Pilot.normalizerAut (conjChart e g) ⟨t, htN'⟩ with hβ₀
  have hβ₀2 : β₀ ^ 2 = 1 := normalizerAut_sq_eq_one' (conjChart e g) htN' ht2
  obtain ⟨δ, hδ⟩ := exists_conj_mem_of_sq_eq_one h2 hβ₀2
  set e' := (conjChart e g).trans δ with he'
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
  have hββ₀ : β = δ * β₀ * δ⁻¹ := normalizerAut_trans _ _ _
  have hβE : β ∈ E := hββ₀ ▸ hδ
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
    rw [hββ₀, hβ₀, normalizerAut_conjChart' e g htN' hgtN]
    intro h1
    have h1' : E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hgtN⟩ = 1 := by
      have h3 := congrArg (fun x => δ⁻¹ * x * δ) h1
      simpa [mul_assoc] using h3
    refine hfp ?_
    have hC := (E6Pilot.normalizerAut_eq_one_iff e _).1 h1'
    have hmem : g * t * g⁻¹ ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hC, hgtC⟩
    rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hmem with h4 | h4
    · exfalso
      have h0 : t = 1 := by
        have e1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
        rw [e1, h4]
        group
      rw [h0, orderOf_one] at ht
      exact absurd ht (by decide)
    · have htt : t' = t := by
        rw [ht']
        calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h4]
          _ = t := by group
      have h5 : t' ∈ centralizer (L : Set G) := htt ▸ htC
      have h6 : α = 1 := (E6Pilot.normalizerAut_eq_one_iff e _).2 h5
      have h7 : (⟨α, hE⟩ : E) = 1 := Subtype.ext h6
      rw [h7, map_one]
  obtain ⟨m, hmΛ, z, hz, hzy⟩ :=
    hRC α β hE hβE hα2 hfp hβ2 hβ1 G φ₁ φ₂ hinj₁ hinj₂ (hX₁.trans hX₂.symm)
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
    have h2' : e (conjugateToSelf L g (e'.symm z)) = δ.symm z := by
      rw [← conjChart_apply, he', MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply]
    rw [h1, h2']
    exact hR δ.symm z hz
  · calc (g * φ₁ m * g⁻¹)⁻¹ * t * (g * φ₁ m * g⁻¹) =
          g * ((φ₁ m)⁻¹ * t' * φ₁ m) * g⁻¹ := by rw [ht']; group
      _ = g * (t' * y) * g⁻¹ := by rw [hxy]
      _ = t * (g * y * g⁻¹) := by rw [ht']; group

end RecentreG

section Reduction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C] [Finite C]
  {K : Type*} [Field K]

theorem fp_eq_of_fieldRigidInE (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    (e : L ≃* C) (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (δ : MulAut C)
    (hrig : FieldRigidInOfE E fp
      (perfectCore (autFixSubgroup (E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hg⟩)))
      (perfectCore (autFixSubgroup (δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹,
        hCN (LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg)⟩ * δ⁻¹))))
    {y : G} (hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y)
    (hyN : y ∈ normalizer (L : Set G)) (hgyN : g * y * g⁻¹ ∈ normalizer (L : Set G))
    (hyE : E6Pilot.normalizerAut e ⟨y, hyN⟩ ∈ E)
    (hgyE : δ * E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgyN⟩ * δ⁻¹ ∈ E) :
    fp ⟨_, hyE⟩ = fp ⟨_, hgyE⟩ := by
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
  set e' := (conjChart e g).trans δ with he'
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
  have hX₂ : (perfectCore (autFixSubgroup (δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹,
      hCN (LinearPilot.conj_inv_mem_centralizer_self_iff.2 hg)⟩ * δ⁻¹))).map φ₂ = Λ := by
    rw [← normalizerAut_conjChart' e g htN', ← normalizerAut_trans, ← he',
      ← map_perfectCore_inf_centralizer_eq' e' htN', ← hsym, Subgroup.map_map, hφe₂,
      subgroupOf_map_subtype, inf_of_le_left hΛL']
  have h₁ : ∀ x, φ₁ (E6Pilot.normalizerAut e ⟨y, hyN⟩ x) = y * φ₁ x * y⁻¹ := fun x =>
    E6Pilot.coe_symm_normalizerAut_apply e ⟨y, hyN⟩ x
  have hβ₂ : E6Pilot.normalizerAut e' ⟨y, hyN'⟩ =
      δ * E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgyN⟩ * δ⁻¹ := by
    rw [he', normalizerAut_trans, normalizerAut_conjChart' e g hyN' hgyN]
  have h₂ : ∀ x, φ₂ ((δ * E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hgyN⟩ * δ⁻¹) x) =
      y * φ₂ x * y⁻¹ := fun x => by
    rw [← hβ₂]
    exact E6Pilot.coe_symm_normalizerAut_apply e' ⟨y, hyN'⟩ x
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
  exact hrig G φ₁ φ₂ hinj₁ hinj₂ (hX₁.trans hX₂.symm) y _ _ hyE hgyE hβX h₁ h₂

end Reduction

section Residual

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {C : Type*} [Group C] [Finite C]
  {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem exists_conj_eq_mul_of_conj_fp_ne_one_E (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* C) (E : Subgroup (MulAut C))
    (fp : E →* (K ≃+* K)) (R : C → Prop) (h2 : ConjIntoIn E)
    (hR : ∀ (δ : MulAut C) (z : C), R z → R (δ z)) (hRC : FieldRecentreInE E fp R) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (δ : MulAut C) {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hxc : ∃ g : G, x = g⁻¹ * t * g)
    (hE : δ * E6Pilot.normalizerAut e ⟨x, hCN hx⟩ * δ⁻¹ ∈ E) (hfp : fp ⟨_, hE⟩ ≠ 1) :
    ∃ (h : G) (z : L), R (e z) ∧ h⁻¹ * t * h = t * (z : G) := by
  obtain ⟨g, rfl⟩ := hxc
  have hE' : E6Pilot.normalizerAut (e.trans δ) ⟨g⁻¹ * t * g, hCN hx⟩ ∈ E := by
    rw [normalizerAut_trans]
    exact hE
  have heq : (⟨_, hE'⟩ : E) = ⟨_, hE⟩ := Subtype.ext (normalizerAut_trans _ _ _)
  obtain ⟨h, z, hz, hhz⟩ := exists_conj_eq_mul_of_fp_ne_one_E hset hOut (e.trans δ) E fp R h2 hR
    hRC ht hKt hCN hx hE' (by rw [heq]; exact hfp)
  refine ⟨h, z, ?_, hhz⟩
  have h1 := hR δ.symm _ hz
  rwa [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1

theorem exists_conj_eq_mul_of_residual_E (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* C) (E : Subgroup (MulAut C))
    (fp : E →* (K ≃+* K)) (R : C → Prop) (h2 : ConjIntoIn E) (hst : FusionStableIn E fp)
    (hR : ∀ (δ : MulAut C) (z : C), R z → R (δ z)) (hFR : NonFieldCoresRigidE E fp)
    (hRC : FieldRecentreInE E fp R) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hSE : ∀ (s : G) (hs : s ∈ (S : Subgroup G)),
      E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩ ∈ E)
    (hS : ∃ (s : G) (hs : s ∈ (S : Subgroup G)), fp ⟨_, hSE s hs⟩ ≠ 1) :
    ∃ (h : G) (z : L), R (e z) ∧ h⁻¹ * t * h = t * (z : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC := mem_centralizer_of_inf_eq hKt
  have hstd := hset.standardSetting
  by_contra hno
  have hfp1 : ∀ (δ : MulAut C) (x : G) (hx : x ∈ centralizer ({t} : Set G))
      (_ : ∃ g : G, x = g⁻¹ * t * g)
      (hE : δ * E6Pilot.normalizerAut e ⟨x, hCN hx⟩ * δ⁻¹ ∈ E), fp ⟨_, hE⟩ = 1 :=
    fun δ x hx hxc hE => by
      by_contra h
      exact hno (exists_conj_eq_mul_of_conj_fp_ne_one_E hstd hOut e E fp R h2 hR hRC ht hKt hCN δ
        hx hxc hE h)
  set ρ : (S : Subgroup G) →* E :=
    ((E6Pilot.normalizerAut e).comp (Subgroup.inclusion (hSt.trans hCN))).codRestrict E
      fun s => hSE s s.2 with hρ
  set φ : (S : Subgroup G) →* (K ≃+* K) := fp.comp ρ with hφ
  have hφapp : ∀ (y : G) (hy : y ∈ (S : Subgroup G)), φ ⟨y, hy⟩ = fp ⟨_, hSE y hy⟩ :=
    fun _ _ => rfl
  have := LinearPilot.isCyclic_ringEquiv (K := K)
  set SS : Sylow 2 (S : Subgroup G) := S.subtype le_rfl with hSS
  have hφS : ∃ s ∈ (SS : Subgroup (S : Subgroup G)), φ s ≠ 1 := by
    obtain ⟨s, hs, hs1⟩ := hS
    refine ⟨⟨s, hs⟩, ?_, by rw [hφapp]; exact hs1⟩
    rw [hSS, Sylow.coe_subtype, mem_subgroupOf]
    exact hs
  obtain ⟨χ, hker, s, -, hχs⟩ := LinearPilot.exists_zmod_two_hom_of_isCyclic φ SS hφS
  have htS : t ∈ (S : Subgroup G) := LinearPilot.mem_sylow_of_le_centralizer ht S hSt
  obtain ⟨N, hN, hNi⟩ := exists_normal_index_two_of_rigid_sylow ht S hSt χ ⟨s, hχs⟩
    fun g y hgt hy hgy hyt => by
      suffices hφeq : φ ⟨y, hy⟩ = φ ⟨g * y * g⁻¹, hgy⟩ by
        have hmem : (⟨y, hy⟩ : (S : Subgroup G))⁻¹ * ⟨g * y * g⁻¹, hgy⟩ ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
          exact hφeq
        have h3 := hker hmem
        rw [MonoidHom.mem_ker, map_mul, map_inv] at h3
        exact inv_mul_eq_one.1 h3
      rw [hφapp, hφapp]
      have hgtC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := hSt hgt
      by_cases hne : g⁻¹ * t * g = t
      ·
        have hg : g ∈ centralizer ({t} : Set G) := by
          rw [mem_centralizer_singleton_iff]
          calc g * t = g * (g⁻¹ * t * g) := by rw [hne]
            _ = t * g := by group
        have hconj : E6Pilot.normalizerAut e ⟨g * y * g⁻¹, hCN (hSt hgy)⟩ =
            E6Pilot.normalizerAut e ⟨g, hCN hg⟩ * E6Pilot.normalizerAut e ⟨y, hCN (hSt hy)⟩ *
              (E6Pilot.normalizerAut e ⟨g, hCN hg⟩)⁻¹ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        have hE' : E6Pilot.normalizerAut e ⟨g, hCN hg⟩ * E6Pilot.normalizerAut e
            ⟨y, hCN (hSt hy)⟩ * (E6Pilot.normalizerAut e ⟨g, hCN hg⟩)⁻¹ ∈ E :=
          hconj ▸ hSE _ hgy
        have heq : (⟨_, hSE _ hgy⟩ : E) = ⟨_, hE'⟩ := Subtype.ext hconj
        rw [heq, hst _ _ (hSE y hy) hE']
      ·
        have hgt' : g * t * g⁻¹ ∈ centralizer ({t} : Set G) :=
          LinearPilot.conj_inv_mem_centralizer_self_iff.2 hgtC
        set P : Subgroup G := (S : Subgroup G).map (MulAut.conj g).toMonoidHom ⊓
          normalizer (L : Set G) with hP
        have hP2 : IsPGroup 2 P := (S.isPGroup'.map _).to_inf_left
        set B : Subgroup (MulAut C) := ((P.subgroupOf (normalizer (L : Set G))).map
          (E6Pilot.normalizerAut e)) with hB
        have hB2 : IsPGroup 2 B :=
          (hP2.comap_of_injective (normalizer (L : Set G)).subtype
            (normalizer (L : Set G)).subtype_injective).map _
        obtain ⟨δ, hδ⟩ := h2 B hB2
        have hmemB : ∀ (w : G) (hw : w ∈ (S : Subgroup G)) (hwN : g * w * g⁻¹ ∈ normalizer
            (L : Set G)), δ * E6Pilot.normalizerAut e ⟨g * w * g⁻¹, hwN⟩ * δ⁻¹ ∈ E := by
          intro w hw hwN
          exact hδ ⟨_, ⟨⟨g * w * g⁻¹, hwN⟩, mem_subgroupOf.2 ⟨⟨w, hw, rfl⟩, hwN⟩, rfl⟩, rfl⟩
        have htE := hmemB t htS (hCN hgt')
        have hyE := hmemB y hy (hCN (hSt hgy))
        have hfp' : fp ⟨_, hSE _ hgt⟩ = 1 := by
          have h4 := hfp1 1 _ hgtC ⟨g, rfl⟩ (by
            have h5 : (1 : MulAut C) * E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgtC⟩ * 1⁻¹ =
                E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgtC⟩ := by group
            rw [h5]
            exact hSE _ hgt)
          have h6 : (⟨_, hSE _ hgt⟩ : E) =
              ⟨(1 : MulAut C) * E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgtC⟩ * 1⁻¹, by
                have h5 : (1 : MulAut C) * E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgtC⟩ *
                    1⁻¹ = E6Pilot.normalizerAut e ⟨g⁻¹ * t * g, hCN hgtC⟩ := by group
                rw [h5]
                exact hSE _ hgt⟩ := Subtype.ext (by group)
          rw [h6]
          exact h4
        have hfp'' : fp ⟨_, htE⟩ = 1 :=
          hfp1 δ _ hgt' ⟨g⁻¹, by rw [inv_inv]⟩ htE
        have hC1 := conj_not_mem_centralizer' ht hKt hgtC hne
        have hC2 : g * t * g⁻¹ ∉ centralizer (L : Set G) := by
          have hg' : (g⁻¹)⁻¹ * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
            rw [inv_inv]
            exact hgt'
          have hne' : (g⁻¹)⁻¹ * t * g⁻¹ ≠ t := by
            rw [inv_inv]
            intro h
            apply hne
            calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
              _ = t := by group
          have h7 := conj_not_mem_centralizer' ht hKt hg' hne'
          rwa [inv_inv] at h7
        have hα₁2 := normalizerAut_sq_eq_one' e (hCN hgtC) (LinearPilot.conj_mul_conj_eq_one ht g)
        have hα₂2 : (δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ * δ⁻¹) ^ 2 = 1 := by
          have h8 := normalizerAut_sq_eq_one' e (hCN hgt') (by
            have h9 := LinearPilot.conj_mul_conj_eq_one ht g⁻¹
            rwa [inv_inv] at h9)
          rw [sq] at h8 ⊢
          calc δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ * δ⁻¹ *
                (δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ * δ⁻¹) =
              δ * (E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ *
                E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩) * δ⁻¹ := by group
            _ = 1 := by rw [h8]; group
        have hα₂1 : δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ * δ⁻¹ ≠ 1 := by
          intro h1
          apply normalizerAut_ne_one' e (hCN hgt') hC2
          calc E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ =
              δ⁻¹ * (δ * E6Pilot.normalizerAut e ⟨g * t * g⁻¹, hCN hgt'⟩ * δ⁻¹) * δ := by group
            _ = 1 := by rw [h1]; group
        have hrig := hFR _ _ (hSE _ hgt) htE hα₁2 hα₂2 (normalizerAut_ne_one' e _ hC1) hα₂1
          hfp' hfp''
        have hFOR := fp_eq_of_fieldRigidInE hstd hOut e E fp htC ht hCN hgtC δ hrig hyt
          (hCN (hSt hy)) (hCN (hSt hgy)) (hSE y hy) hyE
        rw [hFOR]
        exact hst _ _ (hSE _ hgy) hyE
  have := hset.standardSetting.simple
  exact CFSG.SeitzReduction.RankOne.Endings.not_exists_normal_index_two
    hset.standardSetting.nonab ⟨N, hN, hNi⟩

end Residual

end CFSG.SeitzReduction.OmegaPilot
