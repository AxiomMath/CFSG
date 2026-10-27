module

public import CFSG.LocalAnalysis.ComponentInitial.TwoCentralizerIntersectionCenter
public import CFSG.GroupActions.SubgroupStabilizerOuterBound

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.GroupActions
open scoped Pointwise

variable {G : Type*} [Group G]

theorem map_centralizer_singleton_of_apply_eq {α : MulAut G} {x : G} (hx : α x = x) :
    (centralizer ({x} : Set G)).map α.toMonoidHom = centralizer ({x} : Set G) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : h * x = x * h := mem_centralizer_singleton_iff.1 hh
    rw [mem_centralizer_singleton_iff]
    change α h * x = x * α h
    rw [← hx, ← map_mul, hh', map_mul]
  · intro hg
    have hg' : g * x = x * g := mem_centralizer_singleton_iff.1 hg
    refine ⟨α.symm g, ?_, α.apply_symm_apply g⟩
    rw [mem_centralizer_singleton_iff]
    have hx' : α.symm x = x := by rw [MulEquiv.symm_apply_eq, hx]
    rw [← hx', ← map_mul, hg', map_mul]

theorem inner_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (φ : K ≃* K')
    (h : ∀ β : MulAut K, ∃ k, β = MulAut.conj k) : ∀ γ : MulAut K', ∃ k', γ = MulAut.conj k' := by
  intro γ
  obtain ⟨k, hk⟩ := h ((φ.trans γ).trans φ.symm)
  refine ⟨φ k, ?_⟩
  ext k'
  have h1 := congrArg (fun β : MulAut K => φ (β (φ.symm k'))) hk
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

variable [Finite G]

theorem two_centralizers_force_global_inner_automorphisms {x : G} (hx : orderOf x = 2)
    (T : Sylow 2 G) (hT : (center T).map (T : Subgroup G).subtype = zpowers x)
    {Q : Subgroup G} (hQH : Q ≤ centralizer ({x} : Set G))
    (hQn : (Q.subgroupOf (centralizer ({x} : Set G))).Normal)
    (hQe : CFSG.IsExtraspecialPGroup 2 Q) (hZQ : (center Q).map Q.subtype = zpowers x)
    (hker : ∀ h ∈ centralizer ({x} : Set G),
      (∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ zpowers x) ↔ h ∈ Q)
    (hautH : ∀ β : MulAut (centralizer ({x} : Set G)), ∃ h, β = MulAut.conj h)
    {τ : G} (hyQ : τ⁻¹ * x * τ ∈ Q) (hyx : τ⁻¹ * x * τ ∉ zpowers x)
    (hgen : centralizer ({x} : Set G) ⊔ centralizer ({τ⁻¹ * x * τ} : Set G) = ⊤) :
    ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g := by
  classical
  intro α
  set y := τ⁻¹ * x * τ with hydef
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hzx : ∀ z ∈ zpowers x, z = 1 ∨ z = x := by
    intro z hz
    rw [mem_zpowers_iff_mem_range_orderOf, hx] at hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    interval_cases i
    · left
      rw [pow_zero]
    · right
      rw [pow_one]
  have hyord : orderOf y = 2 := by
    have : y = MulAut.conj τ⁻¹ x := by
      rw [MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq, hx]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T (α • T)
  have hgT : MulAut.conj g • (T : Subgroup G) = α • (T : Subgroup G) := by
    have := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
    simp only [Sylow.pointwise_smul_def] at this
    exact this
  set α₁ := (MulAut.conj g)⁻¹ * α with hα₁
  have hα₁T : ∀ t, t ∈ (T : Subgroup G) ↔ α₁ t ∈ (T : Subgroup G) := by
    have hmap : α₁ • (T : Subgroup G) = T := by
      rw [hα₁, mul_smul, ← hgT, inv_smul_smul]
    intro t
    constructor
    · intro ht
      rw [← hmap]
      exact Subgroup.smul_mem_pointwise_smul t α₁ _ ht
    · intro ht
      rw [← hmap] at ht
      obtain ⟨s, hs, hst⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 ht
      rw [← α₁.injective hst]
      exact hs
  have hxT : x ∈ (T : Subgroup G) := by
    have : x ∈ (center T).map (T : Subgroup G).subtype := by rw [hT]; exact mem_zpowers x
    obtain ⟨t, -, rfl⟩ := this
    exact t.2
  have hxZ : ∀ t ∈ (T : Subgroup G), t * x = x * t := by
    intro t ht
    have : x ∈ (center T).map (T : Subgroup G).subtype := by rw [hT]; exact mem_zpowers x
    obtain ⟨z, hz, rfl⟩ := this
    exact congrArg Subtype.val (mem_center_iff.1 hz ⟨t, ht⟩)
  have hα₁x : α₁ x = x := by
    have hmem : α₁ x ∈ zpowers x := by
      rw [← hT]
      refine ⟨⟨α₁ x, (hα₁T x).1 hxT⟩, mem_center_iff.2 fun t => Subtype.ext ?_, rfl⟩
      have ht := (hα₁T (α₁.symm t)).2 (by rw [MulEquiv.apply_symm_apply]; exact t.2)
      have h1 := hxZ _ ht
      have h2 := congrArg α₁ h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    rcases hzx _ hmem with h | h
    · exact absurd (α₁.injective (h.trans (map_one α₁).symm)) hx1
    · exact h
  have hα₁H : α₁ ∈ subgroupStabAut (centralizer ({x} : Set G)) :=
    map_centralizer_singleton_of_apply_eq hα₁x
  obtain ⟨h₀, hh₀⟩ := hautH (subgroupStabRestrict _ ⟨α₁, hα₁H⟩)
  have hα₁h : ∀ h ∈ centralizer ({x} : Set G), α₁ h = h₀ * h * (h₀ : G)⁻¹ := by
    intro h hh
    have := congrArg (fun β : MulAut (centralizer ({x} : Set G)) => ((β ⟨h, hh⟩ : _) : G)) hh₀
    simp only [subgroupStabRestrict_apply, MulAut.conj_apply] at this
    simpa using this
  set α₂ := (MulAut.conj (h₀ : G))⁻¹ * α₁ with hα₂
  have hα₂H : ∀ h ∈ centralizer ({x} : Set G), α₂ h = h := by
    intro h hh
    rw [hα₂, MulAut.mul_apply, hα₁h h hh, MulAut.conj_inv_apply]
    group
  have hyH : y ∈ centralizer ({x} : Set G) := hQH hyQ
  have hxH₁ : x ∈ centralizer ({y} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hyH).symm
  have hα₂y : α₂ y = y := hα₂H y hyH
  have hα₂H₁ : α₂ ∈ subgroupStabAut (centralizer ({y} : Set G)) :=
    map_centralizer_singleton_of_apply_eq hα₂y
  have hHH₁ : (centralizer ({x} : Set G)).map (MulAut.conj τ⁻¹ : G →* G) =
      centralizer ({y} : Set G) := by
    have hyc : y = MulAut.conj τ⁻¹ x := by rw [MulAut.conj_apply, inv_inv]
    ext k
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hh' : h * x = x * h := mem_centralizer_singleton_iff.1 hh
      refine mem_centralizer_singleton_iff.2 ?_
      change (MulAut.conj τ⁻¹ h) * y = y * (MulAut.conj τ⁻¹ h)
      rw [hyc, ← map_mul, hh', map_mul]
    · intro hk
      refine ⟨τ * k * τ⁻¹, ?_, ?_⟩
      · replace hk : k * y = y * k := mem_centralizer_singleton_iff.1 hk
        refine mem_centralizer_singleton_iff.2 ?_
        calc τ * k * τ⁻¹ * x = τ * (k * (τ⁻¹ * x * τ)) * τ⁻¹ := by group
          _ = τ * ((τ⁻¹ * x * τ) * k) * τ⁻¹ := by rw [← hydef, hk]
          _ = x * (τ * k * τ⁻¹) := by group
      · change MulAut.conj τ⁻¹ (τ * k * τ⁻¹) = k
        rw [MulAut.conj_apply, inv_inv]
        group
  have hautH₁ : ∀ γ : MulAut (centralizer ({y} : Set G)), ∃ k, γ = MulAut.conj k :=
    inner_of_mulEquiv (((MulAut.conj τ⁻¹).subgroupMap (centralizer ({x} : Set G))).trans
      (MulEquiv.subgroupCongr hHH₁)) hautH
  obtain ⟨d', hd'⟩ := hautH₁ (subgroupStabRestrict _ ⟨α₂, hα₂H₁⟩)
  have hα₂k : ∀ k ∈ centralizer ({y} : Set G), α₂ k = d' * k * (d' : G)⁻¹ := by
    intro k hk
    have := congrArg (fun β : MulAut (centralizer ({y} : Set G)) => ((β ⟨k, hk⟩ : _) : G)) hd'
    simp only [subgroupStabRestrict_apply, MulAut.conj_apply] at this
    simpa using this
  have hdC : (d' : G) ∈ centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) :
      Subgroup G) : Set G) ⊓ centralizer ({y} : Set G) := by
    refine ⟨mem_centralizer_iff.2 fun e he => ?_, d'.2⟩
    have h2 := hα₂k e he.2
    rw [hα₂H e he.1, eq_mul_inv_iff_mul_eq] at h2
    exact h2
  rw [(two_centralizer_intersection_center hx hQH hQn hQe hZQ hker hyQ hyord hyx).2] at hdC
  have hpow : ∃ c ∈ zpowers x, ∀ k ∈ centralizer ({y} : Set G),
      (d' : G) * k * (d' : G)⁻¹ = c * k * c⁻¹ := by
    refine Subgroup.closure_induction (p := fun d _ => ∃ c ∈ zpowers x,
        ∀ k ∈ centralizer ({y} : Set G), d * k * d⁻¹ = c * k * c⁻¹) ?_ ?_ ?_ ?_ hdC
    · intro z hz
      rcases hz with hz | hz
      · rw [hz]
        exact ⟨x, mem_zpowers x, fun k _ => rfl⟩
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        refine ⟨1, one_mem _, fun k hk => ?_⟩
        rw [mem_centralizer_singleton_iff] at hk
        rw [← hk, mul_inv_cancel_right, one_mul, inv_one, mul_one]
    · exact ⟨1, one_mem _, fun k _ => rfl⟩
    · rintro a b - - ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
      refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, fun k hk => ?_⟩
      have hc₂H₁ : c₂ ∈ centralizer ({y} : Set G) :=
        (zpowers_le.2 hxH₁) hc₂
      have hmem : c₂ * k * c₂⁻¹ ∈ centralizer ({y} : Set G) :=
        mul_mem (mul_mem hc₂H₁ hk) (inv_mem hc₂H₁)
      calc a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
        _ = a * (c₂ * k * c₂⁻¹) * a⁻¹ := by rw [h₂ k hk]
        _ = c₁ * (c₂ * k * c₂⁻¹) * c₁⁻¹ := h₁ _ hmem
        _ = c₁ * c₂ * k * (c₁ * c₂)⁻¹ := by group
    · rintro a - ⟨c, hc, h⟩
      refine ⟨c⁻¹, inv_mem hc, fun k hk => ?_⟩
      have hcH₁ : c ∈ centralizer ({y} : Set G) := (zpowers_le.2 hxH₁) hc
      have hmem : c⁻¹ * k * c ∈ centralizer ({y} : Set G) :=
        mul_mem (mul_mem (inv_mem hcH₁) hk) hcH₁
      have h1 := h _ hmem
      have h2 : a * (c⁻¹ * k * c) * a⁻¹ = k := by rw [h1]; group
      calc a⁻¹ * k * a⁻¹⁻¹ = a⁻¹ * (a * (c⁻¹ * k * c) * a⁻¹) * a := by rw [h2, inv_inv]
        _ = c⁻¹ * k * c⁻¹⁻¹ := by group
  obtain ⟨c, hcx, hck⟩ := hpow
  have hα₂c : α₂ = MulAut.conj c := by
    have hle : centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) ≤
        (α₂.toMonoidHom).eqLocus (MulAut.conj c).toMonoidHom := by
      refine sup_le (fun h hh => ?_) (fun k hk => ?_)
      · change α₂ h = MulAut.conj c h
        rw [hα₂H h hh, MulAut.conj_apply]
        obtain ⟨i, rfl⟩ := hcx
        have hcomm : Commute h (x ^ i) :=
          Commute.zpow_right (mem_centralizer_singleton_iff.1 hh) i
        rw [← hcomm.eq, mul_inv_cancel_right]
      · change α₂ k = MulAut.conj c k
        rw [hα₂k k hk, MulAut.conj_apply, hck k hk]
    rw [hgen] at hle
    ext z
    exact hle (mem_top z)
  refine ⟨g * h₀ * c, ?_⟩
  rw [map_mul, map_mul, ← hα₂c, hα₂, hα₁]
  simp only [mul_assoc, mul_inv_cancel_left]

end CFSG.LocalAnalysis.ComponentInitial
