module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityFieldRigid

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)

section Cores

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

theorem map_inf_centralizer_eq_autFixSubgroup (e : L ≃* projectiveSL n K) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    ((L ⊓ centralizer ({x} : Set G)).subgroupOf L).map e.toMonoidHom =
      autFixSubgroup (normalizerAut e ⟨x, hx⟩) := by
  ext p
  obtain ⟨l, rfl⟩ := e.surjective p
  have h := coe_symm_normalizerAut_apply e ⟨x, hx⟩ l
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
    simp only [Subgroup.coe_inv]
    rw [← hc]
    group
  · intro hfix
    refine ⟨l, ?_, rfl⟩
    show (l : G) ∈ L ⊓ centralizer ({x} : Set G)
    refine ⟨l.2, ?_⟩
    rw [hfix, MulEquiv.symm_apply_apply] at h
    show (l : G) ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_inv] at h
    calc (l : G) * x = (x * l * x⁻¹) * x := by rw [← h]
      _ = x * l := by group

private theorem perfectCore_subgroupOf_of_le [Finite G] {H M : Subgroup G} (hHM : H ≤ M) :
    perfectCore (H.subgroupOf M) = (perfectCore H).subgroupOf M := by
  apply map_injective M.subtype_injective
  rw [map_perfectCore, subgroupOf_map_subtype, inf_of_le_left hHM,
    subgroupOf_map_subtype, inf_of_le_left ((perfectCore_le H).trans hHM)]

theorem map_perfectCore_inf_centralizer_eq [Finite G] [Finite K] (e : L ≃* projectiveSL n K)
    {x : G} (hx : x ∈ normalizer (L : Set G)) :
    ((perfectCore (L ⊓ centralizer ({x} : Set G))).subgroupOf L).map e.toMonoidHom =
      perfectCore (autFixSubgroup (normalizerAut e ⟨x, hx⟩)) := by
  rw [← perfectCore_subgroupOf_of_le inf_le_left, map_perfectCore,
    map_inf_centralizer_eq_autFixSubgroup]

end Cores

section Reduction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] [Finite K]

omit [Finite G] in
theorem conj_inv_mem_centralizer_self_iff {t g : G} :
    g * t * g⁻¹ ∈ centralizer ({t} : Set G) ↔ g⁻¹ * t * g ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * t * g * t = g⁻¹ * (t * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * t) * g := by rw [h]
      _ = t * (g⁻¹ * t * g) := by group
  · intro h
    calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [h]
      _ = t * (g * t * g⁻¹) := by group

theorem fieldComponent_eq_of_fieldRigidIn (hset : SeitzSetting G L) (hn : 3 ≤ n)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hrig : FieldRigidIn hn
      (perfectCore (autFixSubgroup (normalizerAut e ⟨g⁻¹ * t * g,
        centralizer_le_normalizer_of_standard hset.standardSetting.standard
          (mem_centralizer_of_inf_eq_zpowers hKt) ht hg⟩)))
      (perfectCore (autFixSubgroup (normalizerAut e ⟨g * t * g⁻¹,
        centralizer_le_normalizer_of_standard hset.standardSetting.standard
          (mem_centralizer_of_inf_eq_zpowers hKt) ht (conj_inv_mem_centralizer_self_iff.2 hg)⟩))))
    {y : G} (hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y)
    (hyN : y ∈ normalizer (L : Set G)) (hgyN : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    fieldComponent hn e ⟨y, hyN⟩ = fieldComponent hn e ⟨g * y * g⁻¹, hgyN⟩ := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  have hOut := isSolvable_outer_of_mulEquiv hn e
  set t' := g⁻¹ * t * g with ht'
  set L' := CFSG.conjugate L g with hL'
  set Λ := perfectCore (L ⊓ centralizer ({t'} : Set G)) with hΛ
  have hsym : Λ = perfectCore (L' ⊓ centralizer ({t} : Set G)) :=
    perfectCore_inf_centralizer_conj_eq hset.standardSetting hOut htC ht g
  have hΛL : Λ ≤ L := (perfectCore_le _).trans inf_le_left
  have hΛL' : Λ ≤ L' := by rw [hsym]; exact (perfectCore_le _).trans inf_le_left
  have hyt' : y ∈ centralizer ({t'} : Set G) := mem_centralizer_singleton_iff.2 hyt
  have hyN' : y ∈ normalizer (L' : Set G) := centralizer_conj_le_normalizer_conjugate hCN g hyt'
  have hyΛ : y ∈ normalizer (Λ : Set G) := mem_normalizer_perfectCore_inf_centralizer hyN hyt'
  have htN' : t ∈ normalizer (L' : Set G) :=
    centralizer_conj_le_normalizer_conjugate hCN g
      (mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hg).symm)
  set e' := conjChart e g with he'
  set φ₁ : projectiveSL n K →* G := L.subtype.comp e.symm.toMonoidHom with hφ₁
  set φ₂ : projectiveSL n K →* G := L'.subtype.comp e'.symm.toMonoidHom with hφ₂
  have hinj₁ : Function.Injective φ₁ := L.subtype_injective.comp e.symm.injective
  have hinj₂ : Function.Injective φ₂ := L'.subtype_injective.comp e'.symm.injective
  have hφe₁ : φ₁.comp e.toMonoidHom = L.subtype := by
    ext x
    simp [hφ₁]
  have hφe₂ : φ₂.comp e'.toMonoidHom = L'.subtype := by
    ext x
    simp [hφ₂]
  have hX₁ : (perfectCore (autFixSubgroup (normalizerAut e ⟨t', hCN hg⟩))).map φ₁ = Λ := by
    rw [← map_perfectCore_inf_centralizer_eq e (hCN hg), Subgroup.map_map, hφe₁,
      subgroupOf_map_subtype, inf_of_le_left hΛL]
  have hX₂ : (perfectCore (autFixSubgroup (normalizerAut e ⟨g * t * g⁻¹,
      hCN (conj_inv_mem_centralizer_self_iff.2 hg)⟩))).map φ₂ = Λ := by
    rw [← normalizerAut_conjChart e g htN', ← he', ← map_perfectCore_inf_centralizer_eq e' htN',
      ← hsym, Subgroup.map_map, hφe₂, subgroupOf_map_subtype, inf_of_le_left hΛL']
  have h₁ : ∀ x, φ₁ (normalizerAut e ⟨y, hyN⟩ x) = y * φ₁ x * y⁻¹ := by
    intro x
    have h := coe_symm_normalizerAut_apply e ⟨y, hyN⟩ (e.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have h₂ : ∀ x, φ₂ (normalizerAut e' ⟨y, hyN'⟩ x) = y * φ₂ x * y⁻¹ := by
    intro x
    have h := coe_symm_normalizerAut_apply e' ⟨y, hyN'⟩ (e'.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hβX : ∀ x ∈ perfectCore (autFixSubgroup (normalizerAut e ⟨t', hCN hg⟩)),
      normalizerAut e ⟨y, hyN⟩ x ∈ perfectCore (autFixSubgroup (normalizerAut e ⟨t', hCN hg⟩)) := by
    intro x hx
    have hxΛ : φ₁ x ∈ Λ := hX₁ ▸ ⟨x, hx, rfl⟩
    have hyx : φ₁ (normalizerAut e ⟨y, hyN⟩ x) ∈ Λ := by
      rw [h₁]
      exact (mem_normalizer_iff.1 hyΛ _).1 hxΛ
    rw [← hX₁] at hyx
    obtain ⟨z, hz, hzx⟩ := hyx
    rw [← hinj₁ hzx]
    exact hz
  have key := hrig G φ₁ φ₂ hinj₁ hinj₂ (hX₁.trans hX₂.symm) y _ _ hβX h₁ h₂
  rw [fieldComponent_apply, key, ← fieldComponent_apply, he',
    fieldComponent_conjChart hn e g hyN' hgyN]

end Reduction

section Types

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] [Finite K]

omit [Finite G] [Finite K] in
theorem normalizerAut_sq_eq_one (e : L ≃* projectiveSL n K) {x : G}
    (hx : x ∈ normalizer (L : Set G)) (hx2 : x * x = 1) :
    normalizerAut e ⟨x, hx⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have h : (⟨x, hx⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]
    exact hx2)
  rw [h, map_one]

omit [Finite G] [Finite K] in
theorem normalizerAut_ne_one (e : L ≃* projectiveSL n K) {x : G}
    (hx : x ∈ normalizer (L : Set G)) (hxC : x ∉ centralizer (L : Set G)) :
    normalizerAut e ⟨x, hx⟩ ≠ 1 := by
  intro h
  apply hxC
  have hker : (⟨x, hx⟩ : normalizer (L : Set G)) ∈ (normalizerAut e).ker := h
  rw [ker_normalizerAut, mem_subgroupOf] at hker
  exact hker

omit [Finite G] in
theorem conj_not_mem_centralizer {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hne : g⁻¹ * t * g ≠ t) :
    g⁻¹ * t * g ∉ centralizer (L : Set G) := by
  intro hC
  have hmem : g⁻¹ * t * g ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hC, hg⟩
  rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hmem with h | h
  · have h1 : t = 1 := by
      have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      rw [this, h]
      group
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  · exact hne h

omit [Finite G] in
theorem conj_mul_conj_eq_one {t : G} (ht : orderOf t = 2) (g : G) :
    (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [ht2]; group

theorem fieldComponent_eq_of_inner_graph (hset : SeitzSetting G L) (hn : 3 ≤ n)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : InnerGraphFieldRigid K hn) {g : G} (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (htN : g⁻¹ * t * g ∈ normalizer (L : Set G))
    (hfc : fieldComponent hn e ⟨g⁻¹ * t * g, htN⟩ = 1)
    (htN' : g * t * g⁻¹ ∈ normalizer (L : Set G))
    (hfc' : fieldComponent hn e ⟨g * t * g⁻¹, htN'⟩ = 1)
    {y : G} (hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y)
    (hyN : y ∈ normalizer (L : Set G)) (hgyN : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    fieldComponent hn e ⟨y, hyN⟩ = fieldComponent hn e ⟨g * y * g⁻¹, hgyN⟩ := by
  by_cases hne : g⁻¹ * t * g = t
  ·
    have htC := mem_centralizer_of_inf_eq_zpowers hKt
    have hCN := centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
    have hgC : g ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * t = g * (g⁻¹ * t * g) := by rw [hne]
        _ = t * g := by group
    have hconj : (⟨g * y * g⁻¹, hgyN⟩ : normalizer (L : Set G)) =
        ⟨g, hCN hgC⟩ * ⟨y, hyN⟩ * (⟨g, hCN hgC⟩ : normalizer (L : Set G))⁻¹ := rfl
    rw [hconj, fieldComponent_conj]
  have hg' : (g⁻¹)⁻¹ * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [inv_inv]
    exact conj_inv_mem_centralizer_self_iff.2 hg
  have hne' : (g⁻¹)⁻¹ * t * g⁻¹ ≠ t := by
    rw [inv_inv]
    intro h
    apply hne
    calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = t := by group
  have hC := conj_not_mem_centralizer ht hKt hg hne
  have hC' := conj_not_mem_centralizer ht hKt hg' hne'
  rw [inv_inv] at hC'
  refine fieldComponent_eq_of_fieldRigidIn hset hn e ht hKt hg ?_ hyt hyN hgyN
  refine hFR _ _ (normalizerAut_sq_eq_one e _ (conj_mul_conj_eq_one ht g))
    (normalizerAut_sq_eq_one e _ ?_) (normalizerAut_ne_one e _ hC)
    (normalizerAut_ne_one e _ hC') hfc hfc'
  have := conj_mul_conj_eq_one ht g⁻¹
  rwa [inv_inv] at this

theorem false_of_innerGraphFieldRigid (hset : SeitzSetting G L) (hn : 3 ≤ n)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : InnerGraphFieldRigid K hn)
    (hfc : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      ∀ h : g⁻¹ * t * g ∈ normalizer (L : Set G), fieldComponent hn e ⟨g⁻¹ * t * g, h⟩ = 1)
    (S : Sylow 2 G) (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hS : ∃ (s : G) (hs : s ∈ normalizer (L : Set G)), s ∈ (S : Subgroup G) ∧
      fieldComponent hn e ⟨s, hs⟩ ≠ 1) :
    False := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  obtain ⟨s, hsN, hsS, hs1⟩ := hS
  refine false_of_fieldComponent_rigid hset hn e ht hCN S hSt ⟨s, hsS, hs1⟩
    fun g y hg _ hy hgy _ hyt => ?_
  have hg' : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := conj_inv_mem_centralizer_self_iff.2 hg
  have hfc' : fieldComponent hn e ⟨g * t * g⁻¹, hCN hg'⟩ = 1 := by
    have h := hfc g⁻¹ (by rw [inv_inv]; exact hg') (by rw [inv_inv]; exact hCN hg')
    simp only [inv_inv] at h
    exact h
  exact fieldComponent_eq_of_inner_graph hset hn e ht hKt hFR hg (hCN hg) (hfc g hg _)
    (hCN hg') hfc' hyt hy hgy

end Types

end CFSG.SeitzReduction.LinearPilot
