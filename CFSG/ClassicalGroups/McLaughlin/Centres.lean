module

public import CFSG.ClassicalGroups.McLaughlin.Axes
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ClassicalGroups.McLaughlin

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem isCentre_c_smul {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v : V} {c : K}
    (hv : IsCentre X v) (hc : c ≠ 0) : IsCentre X (c • v) := by
  obtain ⟨hv0, φ, hφ0, hφ⟩ := hv
  refine ⟨smul_ne_zero hc hv0, φ, hφ0, by simp [hφ.1], fun c' => ?_⟩
  obtain ⟨g, hg, hgv⟩ := hφ.2 (c' * c)
  refine ⟨g, hg, ?_⟩
  rw [hgv]
  ext z
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  module

private theorem inv_apply_aux (g : LinearMap.GeneralLinearGroup K V) (y : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) y) = y := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

private theorem apply_injective_aux (g : LinearMap.GeneralLinearGroup K V) {x y : V}
    (h : (g : V →ₗ[K] V) x = (g : V →ₗ[K] V) y) : x = y := by
  have h' := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) h
  rwa [inv_apply_aux, inv_apply_aux] at h'

private theorem mem_axisSpace_of_conj {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {h : LinearMap.GeneralLinearGroup K V} (hh : h ∈ X) {v y : V}
    (hy : y ∈ axisSpace X (((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)) :
    (h : V →ₗ[K] V) y ∈ axisSpace X v := by
  have h1 := (mem_axisSpace_smul_iff (X.inv_mem hh) v y).mp hy
  rwa [inv_inv] at h1

private def stabOrbit (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (p s : V) : Set V :=
  {x | ∃ g ∈ X, (g : V →ₗ[K] V) p ∈ Submodule.span K {p} ∧ (g : V →ₗ[K] V) s = x}

private theorem mem_stabOrbit {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {p s x : V} :
    x ∈ stabOrbit X p s ↔
      ∃ g ∈ X, (g : V →ₗ[K] V) p ∈ Submodule.span K {p} ∧ (g : V →ₗ[K] V) s = x :=
  Iff.rfl

private theorem exists_centre_avoid_both [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hgen : GenByRoots X) (hirr : Irred X)
    {p s : V} (hp : IsCentre X p) (hs : IsCentre X s)
    (hPS : Submodule.span K {p} ≠ Submodule.span K {s}) :
    ∃ q : V, IsCentre X q ∧ p ∉ axisSpace X q ∧ s ∉ axisSpace X q := by
  unfold GenByRoots at hgen
  by_contra hcon
  have H : ∀ q : V, IsCentre X q → p ∉ axisSpace X q → s ∈ axisSpace X q := by
    intro q hq hpq
    by_contra hsq
    exact hcon ⟨q, hq, hpq, hsq⟩
  have fwd : ∀ (v : V) (ψ : Dual K V) (h : LinearMap.GeneralLinearGroup K V), v ≠ 0 → ψ ≠ 0 →
      IsRootElt X v ψ → h ∈ X → (h : V →ₗ[K] V) = 1 + ψ.smulRight v →
      ∀ x ∈ stabOrbit X p s, (h : V →ₗ[K] V) x ∈ stabOrbit X p s := by
    intro v ψ h hv hψ hroot hh hcoe x hx
    rw [mem_stabOrbit] at hx ⊢
    obtain ⟨g, hg, hgp, rfl⟩ := hx
    by_cases hpv : p ∈ axisSpace X v
    · have hψp : ψ p = 0 := mem_axisSpace_iff.mp hpv ψ hroot
      have hhp : (h : V →ₗ[K] V) p = p := by
        rw [hcoe]
        simp [LinearMap.smulRight_apply, hψp]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgp
      refine ⟨h * g, X.mul_mem hh hg, ?_, ?_⟩
      · rw [Units.val_mul, Module.End.mul_apply, ← hc, map_smul, hhp]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self p)
      · rw [Units.val_mul, Module.End.mul_apply]
    · have hvc : IsCentre X v := ⟨hv, ψ, hψ, hroot⟩
      have hpgv : p ∉ axisSpace X (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) := by
        intro hpg
        have h1 := mem_axisSpace_of_conj hg hpg
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgp
        rw [← hc] at h1
        have hc0 : c ≠ 0 := by
          rintro rfl
          apply hp.1
          have h2 := inv_apply_aux g p
          rw [← hc, zero_smul, map_zero] at h2
          exact h2.symm
        apply hpv
        have h3 : p = c⁻¹ • (c • p) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [h3]
        exact Submodule.smul_mem _ _ h1
      have hsv' : s ∈ axisSpace X (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) :=
        H _ (isCentre_smul (X.inv_mem hg) hvc) hpgv
      have hxv : (g : V →ₗ[K] V) s ∈ axisSpace X v := mem_axisSpace_of_conj hg hsv'
      have hψx : ψ ((g : V →ₗ[K] V) s) = 0 := mem_axisSpace_iff.mp hxv ψ hroot
      have heq : (h : V →ₗ[K] V) ((g : V →ₗ[K] V) s) = (g : V →ₗ[K] V) s := by
        rw [hcoe]
        simp [LinearMap.smulRight_apply, hψx]
      rw [heq]
      exact ⟨g, hg, hgp, rfl⟩
  have good : ∀ h : LinearMap.GeneralLinearGroup K V, h ∈ X →
      (∀ x ∈ stabOrbit X p s, (h : V →ₗ[K] V) x ∈ stabOrbit X p s) ∧
        ∀ x ∈ stabOrbit X p s, ((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x ∈
          stabOrbit X p s := by
    intro h hh
    rw [hgen] at hh
    induction hh using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨v, φ, hv, hφ, hroot, hgφ⟩ := hg
      have hgX : g ∈ X := by
        rw [hgen]
        exact Subgroup.subset_closure ⟨v, φ, hv, hφ, hroot, hgφ⟩
      have hinv : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
          1 + ((-1 : K) • φ).smulRight v := by
        apply Units.inv_eq_of_mul_eq_one_right
        rw [hgφ]
        ext z
        simp [LinearMap.smulRight_apply, hroot.1]
      exact ⟨fun x hx => fwd v φ g hv hφ hroot hgX hgφ x hx,
        fun x hx => fwd v ((-1 : K) • φ) (g⁻¹) hv (smul_ne_zero (neg_ne_zero.mpr one_ne_zero) hφ)
          (isRootElt_smul (-1) hroot) (X.inv_mem hgX) hinv x hx⟩
    | one =>
      exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · rw [Units.val_mul, Module.End.mul_apply]
        exact hx.1 _ (hy.1 z hz)
      · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
        exact hy.2 _ (hx.2 z hz)
    | inv x _ hx =>
      refine ⟨fun z hz => hx.2 z hz, fun z hz => ?_⟩
      rw [inv_inv]
      exact hx.1 z hz
  have hsO : s ∈ stabOrbit X p s := by
    rw [mem_stabOrbit]
    exact ⟨1, X.one_mem, by simpa using Submodule.mem_span_singleton_self p, by simp⟩
  obtain ⟨g, hg, c, hgc⟩ := exists_map_centre hirr hs hp
  have hcO : c • p ∈ stabOrbit X p s := by
    rw [← hgc]
    exact (good g hg).1 s hsO
  rw [mem_stabOrbit] at hcO
  obtain ⟨h, _hh, hhp, hhs⟩ := hcO
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hhp
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hp.1
    apply apply_injective_aux h
    rw [map_zero, ← hd, zero_smul]
  have hdsc : d • s = c • p := by
    apply apply_injective_aux h
    rw [map_smul, map_smul, hhs, ← hd, smul_comm]
  have hsp : s = (d⁻¹ * c) • p := by
    rw [mul_smul, ← hdsc, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have he0 : d⁻¹ * c ≠ 0 := by
    intro h0
    apply hs.1
    rw [hsp, h0, zero_smul]
  have hspan : Submodule.span K {s} = Submodule.span K {p} := by
    rw [hsp]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr he0) p
  exact hPS hspan.symm

theorem exists_root_avoid_both [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hgen : GenByRoots X) (hirr : Irred X)
    {p s : V} (hp : IsCentre X p) (hs : IsCentre X s)
    (hPS : Submodule.span K {p} ≠ Submodule.span K {s}) :
    ∃ (q : V) (φ : Dual K V), IsCentre X q ∧ IsRootElt X q φ ∧ φ p ≠ 0 ∧ φ s ≠ 0 ∧
      q ∉ axisSpace X p ∧ q ∉ axisSpace X s := by
  obtain ⟨q, hq, hpq, hsq⟩ := exists_centre_avoid_both hgen hirr hp hs hPS
  obtain ⟨φ, hφ, hφp, hφs⟩ := exists_isRootElt_avoid hpq hsq
  exact ⟨q, φ, hq, hφ, hφp, hφs, fun h => hpq ((mem_axisSpace_comm hirr hp hq).mp h),
    fun h => hsq ((mem_axisSpace_comm hirr hs hq).mp h)⟩

theorem isCentre_of_opposite_root [FiniteDimensional K V]
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hirr : Irred X)
    {p s q : V} {θ : Dual K V} (hp : IsCentre X p) (hs : IsCentre X s) (hq : IsCentre X q)
    (hθ : IsRootElt X q θ) (hθp : θ p ≠ 0) (hθs : θ s ≠ 0)
    (hℓ : Submodule.span K {p, s} ≤ axisSpace X p) {x : V}
    (hx : x ∈ Submodule.span K {p, s}) (hxθ : θ x ≠ 0) : IsCentre X x := by
  have hpq : p ∉ axisSpace X q := fun h => hθp (mem_axisSpace_iff.mp h θ hθ)
  have hqp : q ∉ axisSpace X p := fun h => hpq ((mem_axisSpace_comm hirr hp hq).mp h)
  obtain ⟨φ, hφ, hφq, -⟩ := exists_isRootElt_avoid hqp hqp
  have hsL : s ∈ Submodule.span K {p, s} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton s))
  have hφs : φ s = 0 := mem_axisSpace_iff.mp (hℓ hsL) φ hφ
  obtain ⟨-, hT⟩ := opposite_sl2 hφ hθ hφq hθp
  obtain ⟨α, hα⟩ : ∃ α : K, α = θ s / θ p := ⟨_, rfl⟩
  have hα0 : α ≠ 0 := by
    rw [hα]
    exact div_ne_zero hθs hθp
  have hθsα : θ s = α * θ p := by
    rw [hα, div_mul_cancel₀ _ hθp]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : V, ρ = s - α • p := ⟨_, rfl⟩
  have hsρ : s = ρ + α • p := by
    rw [hρ]
    abel
  have hθρ : θ ρ = 0 := by
    rw [hρ, map_sub, map_smul, smul_eq_mul, hθsα, sub_self]
  have hφρ : φ ρ = 0 := by
    rw [hρ, map_sub, map_smul, hφs, hφ.1, smul_zero, sub_zero]
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  have hxe : x = (a + b * α) • p + b • ρ := by
    rw [← hab, hsρ]
    module
  have hA : a + b * α ≠ 0 := by
    intro h0
    apply hxθ
    rw [← hab, map_add, map_smul, map_smul, hθsα, smul_eq_mul, smul_eq_mul]
    linear_combination (θ p) * h0
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      rw [hb, zero_mul, add_zero] at hA
      exact hA
    have hxa : x = a • p := by
      rw [hxe, hb]
      simp only [zero_mul, add_zero, zero_smul]
    rw [hxa]
    exact isCentre_c_smul hp ha
  · obtain ⟨t, ht⟩ : ∃ t : K, t = (a + b * α) / (α * b) := ⟨_, rfl⟩
    have ht0 : t ≠ 0 := by
      rw [ht]
      exact div_ne_zero hA (mul_ne_zero hα0 hb)
    have hkey : b * (α * t) = a + b * α := by
      rw [ht]
      field_simp
    obtain ⟨g, hg, hgp, -, hgD⟩ := hT t ht0
    have hgρ : (g : V →ₗ[K] V) ρ = ρ := hgD ρ hφρ hθρ
    have hgs : (g : V →ₗ[K] V) s = ρ + (α * t) • p := by
      rw [hsρ, map_add, map_smul, hgp, hgρ, smul_smul]
    have hbx : x = b • (g : V →ₗ[K] V) s := by
      rw [hgs, smul_add, smul_smul, hkey, hxe]
      abel
    rw [hbx]
    exact isCentre_c_smul (isCentre_smul hg hs) hb

theorem isCentre_of_mem_span_pair [FiniteDimensional K V] (hK : 3 ≤ Nat.card K)
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hgen : GenByRoots X) (hirr : Irred X)
    {p s : V} (hp : IsCentre X p) (hs : IsCentre X s)
    (hPS : Submodule.span K {p} ≠ Submodule.span K {s}) (hperp : s ∈ axisSpace X p)
    {x : V} (hx : x ∈ Submodule.span K {p, s}) (hx0 : x ≠ 0) : IsCentre X x := by
  obtain ⟨q, θ, hq, hθ, hθp, hθs, -, -⟩ := exists_root_avoid_both hgen hirr hp hs hPS
  have hpa : p ∈ axisSpace X p := mem_axisSpace_iff.mpr fun φ hφ => hφ.1
  have hℓ : Submodule.span K {p, s} ≤ axisSpace X p := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    rcases hy with h | h
    · rw [h]
      exact hpa
    · rw [h]
      exact hperp
  obtain ⟨α, hα⟩ : ∃ α : K, α = θ s / θ p := ⟨_, rfl⟩
  have hα0 : α ≠ 0 := by
    rw [hα]
    exact div_ne_zero hθs hθp
  have hθsα : θ s = α * θ p := by
    rw [hα, div_mul_cancel₀ _ hθp]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : V, ρ = s - α • p := ⟨_, rfl⟩
  have hsρ : s = ρ + α • p := by
    rw [hρ]
    abel
  have hθρ : θ ρ = 0 := by
    rw [hρ, map_sub, map_smul, smul_eq_mul, hθsα, sub_self]
  have hρL : ρ ∈ Submodule.span K {p, s} :=
    Submodule.mem_span_pair.mpr ⟨-α, 1, by rw [one_smul, hsρ]; module⟩
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hPS
    have hsp : s = α • p := by
      rw [hsρ, h0, zero_add]
    rw [hsp, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hα0) p]
  have hρC : IsCentre X ρ := by
    by_contra hρn
    have hex : ∃ T : V, IsCentre X T ∧ ρ ∉ axisSpace X T := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      apply hρ0
      have hbot := iInf_axisSpace_eq_bot hirr ⟨p, hp⟩
      have hmem : ρ ∈ (⨅ v ∈ {v : V | IsCentre X v}, axisSpace X v) := by
        simp only [Submodule.mem_iInf, Set.mem_setOf_eq]
        exact fun T hT => hall T hT
      rw [hbot] at hmem
      exact (Submodule.mem_bot K).mp hmem
    obtain ⟨T, hT, hρT⟩ := hex
    obtain ⟨μ, hμ, hμρ, -⟩ := exists_isRootElt_avoid hρT hρT
    obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : K, γ₀ = -(μ p) / (μ ρ) := ⟨_, rfl⟩
    have hμγ : ∀ δ : K, δ ≠ γ₀ → μ p + δ * μ ρ ≠ 0 := by
      intro δ hδ h0
      apply hδ
      rw [hγ₀, eq_div_iff hμρ]
      linear_combination h0
    have hK3 : ∃ a b c : K, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card] at hK
      exact Fintype.two_lt_card_iff.mp (by omega)
    obtain ⟨a₀, b₀, c₀, hab', hac', hbc'⟩ := hK3
    obtain ⟨γ, γ', hγγ', hγ, hγ'⟩ : ∃ γ γ' : K, γ ≠ γ' ∧ γ ≠ γ₀ ∧ γ' ≠ γ₀ := by
      by_cases ha : a₀ = γ₀
      · exact ⟨b₀, c₀, hbc', fun h => hab' (ha.trans h.symm), fun h => hac' (ha.trans h.symm)⟩
      · by_cases hb : b₀ = γ₀
        · exact ⟨a₀, c₀, hac', ha, fun h => hbc' (hb.trans h.symm)⟩
        · exact ⟨a₀, b₀, hab', ha, hb⟩
    obtain ⟨p₁, hp₁⟩ : ∃ v : V, v = p + γ • ρ := ⟨_, rfl⟩
    obtain ⟨s₁, hs₁⟩ : ∃ v : V, v = p + γ' • ρ := ⟨_, rfl⟩
    have hp₁L : p₁ ∈ Submodule.span K {p, s} := by
      rw [hp₁]
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.smul_mem _ _ hρL)
    have hs₁L : s₁ ∈ Submodule.span K {p, s} := by
      rw [hs₁]
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.smul_mem _ _ hρL)
    have hθp₁ : θ p₁ ≠ 0 := by
      rw [hp₁, map_add, map_smul, hθρ, smul_zero, add_zero]
      exact hθp
    have hθs₁ : θ s₁ ≠ 0 := by
      rw [hs₁, map_add, map_smul, hθρ, smul_zero, add_zero]
      exact hθp
    have hp₁C : IsCentre X p₁ :=
      isCentre_of_opposite_root hirr hp hs hq hθ hθp hθs hℓ hp₁L hθp₁
    have hs₁C : IsCentre X s₁ :=
      isCentre_of_opposite_root hirr hp hs hq hθ hθp hθs hℓ hs₁L hθs₁
    have hρp : ρ ∈ axisSpace X p := by
      rw [hρ]
      exact Submodule.sub_mem _ hperp (Submodule.smul_mem _ _ hpa)
    have hp₁p : p₁ ∈ axisSpace X p := by
      rw [hp₁]
      exact Submodule.add_mem _ hpa (Submodule.smul_mem _ _ hρp)
    have hpp₁ : p ∈ axisSpace X p₁ := (mem_axisSpace_comm hirr hp hp₁C).mp hp₁p
    have hps : p ∈ axisSpace X s := (mem_axisSpace_comm hirr hp hs).mp hperp
    have hss : s ∈ axisSpace X s := mem_axisSpace_iff.mpr fun φ hφ => hφ.1
    have hρs : ρ ∈ axisSpace X s := by
      rw [hρ]
      exact Submodule.sub_mem _ hss (Submodule.smul_mem _ _ hps)
    have hp₁s : p₁ ∈ axisSpace X s := by
      rw [hp₁]
      exact Submodule.add_mem _ hps (Submodule.smul_mem _ _ hρs)
    have hsp₁ : s ∈ axisSpace X p₁ := (mem_axisSpace_comm hirr hs hp₁C).mp hp₁s
    have hρp₁ : ρ ∈ axisSpace X p₁ := by
      rw [hρ]
      exact Submodule.sub_mem _ hsp₁ (Submodule.smul_mem _ _ hpp₁)
    have hs₁p₁ : s₁ ∈ axisSpace X p₁ := by
      rw [hs₁]
      exact Submodule.add_mem _ hpp₁ (Submodule.smul_mem _ _ hρp₁)
    have hp₁p₁ : p₁ ∈ axisSpace X p₁ := mem_axisSpace_iff.mpr fun φ hφ => hφ.1
    have hℓ₁ : Submodule.span K {p₁, s₁} ≤ axisSpace X p₁ := by
      refine Submodule.span_le.mpr ?_
      intro y hy
      rcases hy with h | h
      · rw [h]
        exact hp₁p₁
      · rw [h]
        exact hs₁p₁
    have hc1 : (γ' - γ)⁻¹ * (γ' - γ) = 1 :=
      inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hγγ'))
    have hρmem₁ : ρ ∈ Submodule.span K {p₁, s₁} := by
      refine Submodule.mem_span_pair.mpr ⟨(-(γ' - γ)⁻¹), (γ' - γ)⁻¹, ?_⟩
      have e : (-(γ' - γ)⁻¹) • p₁ + (γ' - γ)⁻¹ • s₁ = ((γ' - γ)⁻¹ * (γ' - γ)) • ρ := by
        rw [hp₁, hs₁]
        module
      rw [e, hc1, one_smul]
    have hμp₁ : μ p₁ ≠ 0 := by
      rw [hp₁, map_add, map_smul, smul_eq_mul]
      exact hμγ γ hγ
    have hμs₁ : μ s₁ ≠ 0 := by
      rw [hs₁, map_add, map_smul, smul_eq_mul]
      exact hμγ γ' hγ'
    exact hρn (isCentre_of_opposite_root hirr hp₁C hs₁C hT hμ hμp₁ hμs₁ hℓ₁ hρmem₁ hμρ)
  obtain ⟨a, b, hab2⟩ := Submodule.mem_span_pair.mp hx
  have hxe : x = (a + b * α) • p + b • ρ := by
    rw [← hab2, hsρ]
    module
  by_cases hxθ : θ x = 0
  · have hθx : θ x = (a + b * α) * θ p := by
      rw [hxe, map_add, map_smul, map_smul, hθρ, smul_eq_mul, smul_eq_mul]
      ring
    have hA0 : a + b * α = 0 :=
      (mul_eq_zero.mp (hθx.symm.trans hxθ)).resolve_right hθp
    have hxb : x = b • ρ := by
      rw [hxe, hA0, zero_smul, zero_add]
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hx0
      rw [hxb, hb0, zero_smul]
    rw [hxb]
    exact isCentre_c_smul hρC hb0
  · exact isCentre_of_opposite_root hirr hp hs hq hθ hθp hθs hℓ hx hxθ

theorem isCentre_of_ne_zero [FiniteDimensional K V] (hK : 3 ≤ Nat.card K)
    (hn : 2 ≤ Module.finrank K V) {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hgen : GenByRoots X) (hirr : Irred X) {v : V} (hv : v ≠ 0) : IsCentre X v := by
  have hgen' := hgen
  unfold GenByRoots at hgen'
  have hline : ∀ p s : V, IsCentre X p → IsCentre X s →
      Submodule.span K {p} ≠ Submodule.span K {s} →
      ∀ x ∈ Submodule.span K {p, s}, x ≠ 0 → IsCentre X x := by
    intro p s hp hs hPS x hx hx0
    by_cases hperp : s ∈ axisSpace X p
    · exact isCentre_of_mem_span_pair hK hgen hirr hp hs hPS hperp hx hx0
    · have hpn : p ∉ axisSpace X s := fun h => hperp ((mem_axisSpace_comm hirr hp hs).mpr h)
      obtain ⟨φ, hφ, hφs, -⟩ := exists_isRootElt_avoid hperp hperp
      obtain ⟨ψ, hψ, hψp, -⟩ := exists_isRootElt_avoid hpn hpn
      obtain ⟨hT1, -⟩ := opposite_sl2 hφ hψ hφs hψp
      obtain ⟨g, hg, hgp, -⟩ := hT1 x hx hx0
      rw [← hgp]
      exact isCentre_smul hg hp
  have hne : ∃ w : V, IsCentre X w := by
    by_contra hno
    simp only [not_exists] at hno
    have hXbot : X = ⊥ := by
      rw [hgen', eq_bot_iff]
      refine (Subgroup.closure_le ⊥).mpr fun g hg => ?_
      obtain ⟨w, φ, hw, hφ, hroot, -⟩ := hg
      exact (hno w ⟨hw, φ, hφ, hroot⟩).elim
    have hpos : 0 < Module.finrank K V := by omega
    obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hW := hirr (Submodule.span K {e}) (by
      intro g hg w hw
      rw [hXbot, Subgroup.mem_bot] at hg
      rw [hg, Units.val_one, Module.End.one_apply]
      exact hw)
    rcases hW with h | h
    · have he' : e ∈ Submodule.span K {e} := Submodule.mem_span_singleton_self e
      rw [h, Submodule.mem_bot] at he'
      exact he he'
    · have h1 : Module.finrank K (⊤ : Submodule K V) = 1 := by
        rw [← h]
        exact finrank_span_singleton he
      rw [finrank_top] at h1
      omega
  obtain ⟨v₀, hv₀⟩ := hne
  let U : Submodule K V :=
    { carrier := {x | x = 0 ∨ IsCentre X x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rcases hx with rfl | hx
        · rw [zero_add]
          exact hy
        rcases hy with rfl | hy
        · rw [add_zero]
          exact Or.inr hx
        by_cases hxy : x + y = 0
        · exact Or.inl hxy
        right
        by_cases hsp : Submodule.span K {x} = Submodule.span K {y}
        · have hyx : y ∈ Submodule.span K {x} := by
            rw [hsp]
            exact Submodule.mem_span_singleton_self y
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyx
          have hxy' : x + y = (1 + c) • x := by
            rw [← hc]
            module
          by_cases h1 : 1 + c = 0
          · exact (hxy (by rw [hxy', h1, zero_smul])).elim
          · rw [hxy']
            exact isCentre_c_smul hx h1
        · have hmem : x + y ∈ Submodule.span K {x, y} :=
            Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
              (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton y)))
          exact hline x y hx hy hsp (x + y) hmem hxy
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl (smul_zero c)
        by_cases hc : c = 0
        · exact Or.inl (by rw [hc, zero_smul])
        · exact Or.inr (isCentre_c_smul hx hc) }
  have hUmem : ∀ x : V, x ∈ U ↔ x = 0 ∨ IsCentre X x := fun x => Iff.rfl
  have htop := span_isCentre_eq_top hirr ⟨v₀, hv₀⟩
  have hle : Submodule.span K {y : V | IsCentre X y} ≤ U :=
    Submodule.span_le.mpr fun y hy => (hUmem y).mpr (Or.inr hy)
  rw [htop] at hle
  rcases (hUmem v).mp (hle Submodule.mem_top) with h | h
  · exact absurd h hv
  · exact h

end CFSG.ClassicalGroups.McLaughlin
