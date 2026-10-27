module

public import CFSG.LocalAnalysis.SteinbergBXGMSEvenPairAffinePlane

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis.SteinbergBX CFSG.LocalAnalysis.SteinbergBX.GMSAffine

@[expose] def IsDilatation {Ω : Type*} (𝓛 : Set (Set Ω)) (g : Equiv.Perm Ω) : Prop :=
  ∀ ℓ ∈ 𝓛, ⇑g '' ℓ = ℓ ∨ Disjoint (⇑g '' ℓ) ℓ

@[expose] def parallelClass {Ω : Type*} (𝓛 : Set (Set Ω)) (ℓ₀ : Set Ω) : Set (Set Ω) :=
  {ℓ | ℓ ∈ 𝓛 ∧ (ℓ = ℓ₀ ∨ Disjoint ℓ ℓ₀)}

@[expose] def axisInvolutions {Ω : Type*} (N : Subgroup (Equiv.Perm Ω)) (𝒞 : Set (Set Ω)) :
    Set (Equiv.Perm Ω) :=
  {v | v ∈ nonregInvolutions N ∧ Function.fixedPoints ⇑v ∈ 𝒞}

@[expose] def parallelInvolutionGroup {Ω : Type*} (N : Subgroup (Equiv.Perm Ω))
    (𝓛 : Set (Set Ω)) (ℓ₀ : Set Ω) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure (axisInvolutions N (parallelClass 𝓛 ℓ₀))

namespace EvenPairPlane

variable {Ω : Type*} {N : Subgroup (Equiv.Perm Ω)} {τ : Equiv.Perm Ω} {α β : Ω} {s : ℕ}

theorem eq_of_mem_of_mem (hG : InvolutionGeometry N τ α β s) {ℓ m : Set Ω}
    (hℓ : ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ))
    (hm : m ∈ permTranslates N (Function.fixedPoints ⇑τ)) (hne : ℓ ≠ m) {x y : Ω}
    (hxℓ : x ∈ ℓ) (hxm : x ∈ m) (hyℓ : y ∈ ℓ) (hym : y ∈ m) : x = y := by
  by_contra hxy
  exact hne ((hG.existsUnique_line hxy).unique ⟨hℓ, hxℓ, hyℓ⟩ ⟨hm, hxm, hym⟩)

theorem exists_not_mem [Finite Ω] (hG : InvolutionGeometry N τ α β s) {ℓ : Set Ω}
    (hℓ : ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ)) : ∃ z, z ∉ ℓ := by
  by_contra hall
  push Not at hall
  have h1 := hG.ncard_line hℓ
  rw [Set.eq_univ_of_forall hall, Set.ncard_univ, hG.card] at h1
  have := hG.two_le
  nlinarith

theorem eq_or_disjoint_of_disjoint [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {ℓ m p : Set Ω} (hℓ : ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ))
    (hm : m ∈ permTranslates N (Function.fixedPoints ⇑τ))
    (hp : p ∈ permTranslates N (Function.fixedPoints ⇑τ)) (hℓp : Disjoint ℓ p)
    (hmp : Disjoint m p) : ℓ = m ∨ Disjoint ℓ m := by
  by_cases hd : Disjoint ℓ m
  · exact Or.inr hd
  · left
    obtain ⟨x, hxℓ, hxm⟩ := Set.not_disjoint_iff.1 hd
    have hxp : x ∉ p := fun h1 => Set.disjoint_left.1 hℓp hxℓ h1
    exact (hG.existsUnique_parallel hp hxp).unique ⟨hℓ, hxℓ, hℓp⟩ ⟨hm, hxm, hmp⟩

theorem parallelClass_eq_or_disjoint [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {ℓ₀ ℓ m : Set Ω} (hℓ₀ : ℓ₀ ∈ permTranslates N (Function.fixedPoints ⇑τ))
    (hℓ : ℓ ∈ parallelClass (permTranslates N (Function.fixedPoints ⇑τ)) ℓ₀)
    (hm : m ∈ parallelClass (permTranslates N (Function.fixedPoints ⇑τ)) ℓ₀) :
    ℓ = m ∨ Disjoint ℓ m := by
  obtain ⟨hℓL, rfl | hℓd⟩ := hℓ
  · obtain ⟨-, rfl | hmd⟩ := hm
    · exact Or.inl rfl
    · exact Or.inr hmd.symm
  · obtain ⟨hmL, rfl | hmd⟩ := hm
    · exact Or.inr hℓd
    · exact eq_or_disjoint_of_disjoint hG hℓL hmL hℓ₀ hℓd hmd

theorem image_eq_of_isDilatation {𝓛 : Set (Set Ω)} {g : Equiv.Perm Ω} (hg : IsDilatation 𝓛 g)
    {ℓ : Set Ω} (hℓ : ℓ ∈ 𝓛) {x : Ω} (hx : x ∈ ℓ) (hgx : g x ∈ ℓ) : ⇑g '' ℓ = ℓ := by
  rcases hg ℓ hℓ with h1 | h1
  · exact h1
  · exact absurd hgx (Set.disjoint_left.1 h1 (Set.mem_image_of_mem _ hx))

theorem apply_eq_of_image_eq (hG : InvolutionGeometry N τ α β s) {g : Equiv.Perm Ω}
    {ℓ m : Set Ω} (hℓ : ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ))
    (hm : m ∈ permTranslates N (Function.fixedPoints ⇑τ)) (hne : ℓ ≠ m)
    (hgℓ : ⇑g '' ℓ = ℓ) (hgm : ⇑g '' m = m) {x : Ω} (hxℓ : x ∈ ℓ) (hxm : x ∈ m) : g x = x := by
  have h1 : g x ∈ ℓ := by
    rw [← hgℓ]
    exact Set.mem_image_of_mem _ hxℓ
  have h2 : g x ∈ m := by
    rw [← hgm]
    exact Set.mem_image_of_mem _ hxm
  exact eq_of_mem_of_mem hG hℓ hm hne h1 h2 hxℓ hxm

theorem eq_one_of_isDilatation_of_fix_two [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {g : Equiv.Perm Ω} (hg : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g)
    {x y : Ω} (hxy : x ≠ y) (hgx : g x = x) (hgy : g y = y) : g = 1 := by
  obtain ⟨ℓ, ⟨hℓ, hxℓ, hyℓ⟩, huniq⟩ := hG.existsUnique_line hxy
  have hgℓ : ⇑g '' ℓ = ℓ := image_eq_of_isDilatation hg hℓ hxℓ (by rw [hgx]; exact hxℓ)
  have hoff : ∀ z, z ∉ ℓ → g z = z := by
    intro z hz
    have hxz : x ≠ z := fun h1 => hz (h1 ▸ hxℓ)
    have hyz : y ≠ z := fun h1 => hz (h1 ▸ hyℓ)
    obtain ⟨m₁, ⟨hm₁, hxm₁, hzm₁⟩, -⟩ := hG.existsUnique_line hxz
    obtain ⟨m₂, ⟨hm₂, hym₂, hzm₂⟩, -⟩ := hG.existsUnique_line hyz
    have h1 : ⇑g '' m₁ = m₁ := image_eq_of_isDilatation hg hm₁ hxm₁ (by rw [hgx]; exact hxm₁)
    have h2 : ⇑g '' m₂ = m₂ := image_eq_of_isDilatation hg hm₂ hym₂ (by rw [hgy]; exact hym₂)
    have hne : m₁ ≠ m₂ := by
      intro h12
      apply hz
      have h3 : m₁ = ℓ := huniq m₁ ⟨hm₁, hxm₁, h12 ▸ hym₂⟩
      exact h3 ▸ hzm₁
    exact apply_eq_of_image_eq hG hm₁ hm₂ hne h1 h2 hzm₁ hzm₂
  obtain ⟨z, hz⟩ := exists_not_mem hG hℓ
  have hgz := hoff z hz
  refine Equiv.ext fun w => ?_
  rw [Equiv.Perm.one_apply]
  by_cases hw : w ∈ ℓ
  · have hzw : z ≠ w := fun h1 => hz (h1 ▸ hw)
    obtain ⟨m, ⟨hm, hzm, hwm⟩, -⟩ := hG.existsUnique_line hzw
    have h1 : ⇑g '' m = m := image_eq_of_isDilatation hg hm hzm (by rw [hgz]; exact hzm)
    have hne : m ≠ ℓ := fun h2 => hz (h2 ▸ hzm)
    exact apply_eq_of_image_eq hG hm hℓ hne h1 hgℓ hwm hw
  · exact hoff w hw

theorem isDilatation_mul [Finite Ω] (hG : InvolutionGeometry N τ α β s) {g h : Equiv.Perm Ω}
    (hgN : g ∈ N) (hhN : h ∈ N) (hg : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g)
    (hh : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) h) :
    IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) (g * h) := by
  intro ℓ hℓ
  have hm : ⇑h '' ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) :=
    image_mem_permTranslates hhN hℓ
  have hgm : ⇑g '' (⇑h '' ℓ) ∈ permTranslates N (Function.fixedPoints ⇑τ) :=
    image_mem_permTranslates hgN hm
  rw [Equiv.Perm.coe_mul, Set.image_comp]
  rcases hh ℓ hℓ with h1 | h1
  · rw [h1]
    exact hg ℓ hℓ
  · rcases hg _ hm with h2 | h2
    · rw [h2]
      exact Or.inr h1
    · exact eq_or_disjoint_of_disjoint hG hgm hℓ hm h2 h1.symm

theorem image_image_inv (g : Equiv.Perm Ω) (ℓ : Set Ω) : ⇑g '' (⇑g⁻¹ '' ℓ) = ℓ := by
  rw [← Set.image_comp, ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one, Set.image_id]

theorem isDilatation_inv {g : Equiv.Perm Ω} (hgN : g ∈ N)
    (hg : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g) :
    IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g⁻¹ := by
  intro ℓ hℓ
  have hm : ⇑g⁻¹ '' ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) :=
    image_mem_permTranslates (inv_mem hgN) hℓ
  rcases hg _ hm with h2 | h2
  · left
    rw [image_image_inv] at h2
    exact h2.symm
  · right
    rw [image_image_inv] at h2
    exact h2.symm

theorem isDilatation_conj {g h : Equiv.Perm Ω} (hhN : h ∈ N)
    (hg : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g) :
    IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) (h * g * h⁻¹) := by
  intro ℓ hℓ
  have hm : ⇑h⁻¹ '' ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) :=
    image_mem_permTranslates (inv_mem hhN) hℓ
  have heq : ⇑(h * g * h⁻¹) '' ℓ = ⇑h '' (⇑g '' (⇑h⁻¹ '' ℓ)) := by
    simp only [Equiv.Perm.coe_mul, Set.image_comp]
  rw [heq]
  rcases hg _ hm with h2 | h2
  · left
    rw [h2, image_image_inv]
  · right
    have h3 := (Set.disjoint_image_iff h.injective).2 h2
    rwa [image_image_inv] at h3

theorem mul_eq_one_of_isDilatation_of_fix [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {t u : Equiv.Perm Ω} (htN : t ∈ N) (huN : u ∈ N)
    (ht : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) t)
    (hu : IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) u)
    (htf : ∀ x, t x ≠ x) (huf : ∀ x, u x ≠ x) {c : Ω} (hc : (t * u) c = c) : t * u = 1 := by
  have htu := isDilatation_mul hG htN huN ht hu
  have hty : t (u c) = c := hc
  have hcy : c ≠ u c := fun h1 => huf c h1.symm
  obtain ⟨m, ⟨hm, hcm, hym⟩, -⟩ := hG.existsUnique_line hcy
  have hum : ⇑u '' m = m := image_eq_of_isDilatation hu hm hcm hym
  have htm : ⇑t '' m = m := image_eq_of_isDilatation ht hm hym (by rw [hty]; exact hcm)
  obtain ⟨x, hx⟩ := exists_not_mem hG hm
  have hcx : c ≠ x := fun h1 => hx (h1 ▸ hcm)
  have hinv : ∀ g : Equiv.Perm Ω, (∀ x, g x ≠ x) → ∀ ℓ₁ ℓ₂ : Set Ω,
      ℓ₁ ∈ permTranslates N (Function.fixedPoints ⇑τ) →
      ℓ₂ ∈ permTranslates N (Function.fixedPoints ⇑τ) → ⇑g '' ℓ₁ = ℓ₁ → ⇑g '' ℓ₂ = ℓ₂ →
      ℓ₁ ≠ ℓ₂ → Disjoint ℓ₁ ℓ₂ := by
    intro g hgf ℓ₁ ℓ₂ h₁ h₂ hg₁ hg₂ hne
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hgf z (apply_eq_of_image_eq hG h₁ h₂ hne hg₁ hg₂ hz₁ hz₂)
  obtain ⟨pu, ⟨hpu, hxpu, huxpu⟩, -⟩ := hG.existsUnique_line (huf x).symm
  obtain ⟨pt, ⟨hpt, hxpt, htxpt⟩, -⟩ := hG.existsUnique_line (htf x).symm
  have hupu : ⇑u '' pu = pu := image_eq_of_isDilatation hu hpu hxpu huxpu
  have htpt : ⇑t '' pt = pt := image_eq_of_isDilatation ht hpt hxpt htxpt
  have hdu : Disjoint pu m := hinv u huf pu m hpu hm hupu hum (fun h1 => hx (h1 ▸ hxpu))
  have hdt : Disjoint pt m := hinv t htf pt m hpt hm htpt htm (fun h1 => hx (h1 ▸ hxpt))
  have hp : pu = pt :=
    (hG.existsUnique_parallel hm hx).unique ⟨hpu, hxpu, hdu⟩ ⟨hpt, hxpt, hdt⟩
  have htupu : ⇑(t * u) '' pu = pu := by
    rw [Equiv.Perm.coe_mul, Set.image_comp, hupu, hp, htpt]
  obtain ⟨r, ⟨hr, hcr, hxr⟩, -⟩ := hG.existsUnique_line hcx
  have htur : ⇑(t * u) '' r = r := image_eq_of_isDilatation htu hr hcr (by rw [hc]; exact hcr)
  have hne : pu ≠ r := by
    intro h1
    rw [← h1] at hcr
    exact Set.disjoint_left.1 hdu hcr hcm
  have hfx : (t * u) x = x := apply_eq_of_image_eq hG hpu hr hne htupu htur hxpu hxr
  exact eq_one_of_isDilatation_of_fix_two hG htu hcx hc hfx

@[expose] def translationGroup [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    Subgroup (Equiv.Perm Ω) where
  carrier := {g | g ∈ N ∧ IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g ∧
    (g = 1 ∨ ∀ x, g x ≠ x)}
  one_mem' := ⟨one_mem N, fun ℓ _ => Or.inl (by rw [Equiv.Perm.coe_one, Set.image_id]),
    Or.inl rfl⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg, hg1⟩ ⟨hhN, hh, hh1⟩
    refine ⟨mul_mem hgN hhN, isDilatation_mul hG hgN hhN hg hh, ?_⟩
    rcases hg1 with rfl | hgf
    · rw [one_mul]
      exact hh1
    rcases hh1 with rfl | hhf
    · rw [mul_one]
      exact Or.inr hgf
    by_cases hfix : ∃ c, (g * h) c = c
    · obtain ⟨c, hc⟩ := hfix
      exact Or.inl (mul_eq_one_of_isDilatation_of_fix hG hgN hhN hg hh hgf hhf hc)
    · push Not at hfix
      exact Or.inr hfix
  inv_mem' := by
    rintro g ⟨hgN, hg, hg1⟩
    refine ⟨inv_mem hgN, isDilatation_inv hgN hg, ?_⟩
    rcases hg1 with rfl | hgf
    · exact Or.inl inv_one
    · right
      intro x hx
      apply hgf x
      have h1 := congrArg (⇑g) hx
      rw [GMSAffine.perm_apply_inv] at h1
      exact h1.symm

theorem mem_translationGroup [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {g : Equiv.Perm Ω} : g ∈ translationGroup hG ↔
      g ∈ N ∧ IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g ∧
        (g = 1 ∨ ∀ x, g x ≠ x) :=
  Iff.rfl

theorem commute_of_disjoint_axes [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ)
    {u w : Equiv.Perm Ω} (hu : u ∈ nonregInvolutions N) (hw : w ∈ nonregInvolutions N)
    (hd : Disjoint (Function.fixedPoints ⇑u) (Function.fixedPoints ⇑w)) : u * w = w * u := by
  obtain ⟨g, hg, rfl⟩ := hG.nonreg_iff.1 hu
  have hw' : g⁻¹ * w * g ∈ nonregInvolutions N := by
    have h1 := conj_mem_nonregInvolutions hw (inv_mem hg)
    rwa [inv_inv] at h1
  have hFw' : Function.fixedPoints ⇑(g⁻¹ * w * g) = ⇑g⁻¹ '' Function.fixedPoints ⇑w := by
    have h1 := fixedPoints_conj g⁻¹ w
    rwa [inv_inv] at h1
  have hFτ : Function.fixedPoints ⇑τ = ⇑g⁻¹ '' Function.fixedPoints ⇑(g * τ * g⁻¹) := by
    rw [fixedPoints_conj, ← Set.image_comp, ← Equiv.Perm.coe_mul, inv_mul_cancel,
      Equiv.Perm.coe_one, Set.image_id]
  have hdisj : Disjoint (Function.fixedPoints ⇑(g⁻¹ * w * g)) (Function.fixedPoints ⇑τ) := by
    rw [hFw', hFτ, Set.disjoint_image_iff (g⁻¹).injective]
    exact hd.symm
  have hline : Function.fixedPoints ⇑(g⁻¹ * w * g) ∈
      permTranslates N (Function.fixedPoints ⇑τ) := hG.bijOn_fixedPoints.mapsTo hw'
  obtain ⟨-, -, himage⟩ := hG.centralizer_involutions hCH
  have hmem : Function.fixedPoints ⇑(g⁻¹ * w * g) ∈
      (fun v : Equiv.Perm Ω => Function.fixedPoints ⇑v) ''
        {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ} := by
    rw [himage]
    exact ⟨hline, hdisj⟩
  obtain ⟨v, ⟨hv, hvc, -⟩, hvF⟩ := hmem
  have hveq : v = g⁻¹ * w * g := hG.bijOn_fixedPoints.injOn hv hw' hvF
  rw [hveq] at hvc
  calc g * τ * g⁻¹ * w = g * (τ * (g⁻¹ * w * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * w * g) * τ) * g⁻¹ := by rw [hvc]
    _ = w * (g * τ * g⁻¹) := by group

theorem axisInvolutions_parallelClass_eq [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ) :
    axisInvolutions N (parallelClass (permTranslates N (Function.fixedPoints ⇑τ))
      (Function.fixedPoints ⇑τ)) =
      insert τ {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ} := by
  obtain ⟨-, -, himage⟩ := hG.centralizer_involutions hCH
  have hτnr : τ ∈ nonregInvolutions N := ⟨hG.mem, hG.orderOf_eq, α, hG.fix_left⟩
  have hαF : α ∈ Function.fixedPoints ⇑τ := hG.fix_left
  ext v
  constructor
  · rintro ⟨hv, -, hvF | hvd⟩
    · exact Or.inl (hG.bijOn_fixedPoints.injOn hv hτnr hvF)
    · right
      have hvτ : v ≠ τ := by
        rintro rfl
        exact Set.disjoint_left.1 hvd hαF hαF
      exact ⟨hv, commute_of_disjoint_axes hG hCH hv hτnr hvd, hvτ⟩
  · rintro (rfl | ⟨hv, hvc, hvτ⟩)
    · exact ⟨hτnr, mem_permTranslates_self N _, Or.inl rfl⟩
    · have h1 : Function.fixedPoints ⇑v ∈ (fun v : Equiv.Perm Ω => Function.fixedPoints ⇑v) ''
          {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ} :=
        Set.mem_image_of_mem _ ⟨hv, hvc, hvτ⟩
      rw [himage] at h1
      exact ⟨hv, h1.1, Or.inr h1.2⟩

theorem isDilatation_of_preserves_parallel_class [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {a : Equiv.Perm Ω} (hafree : ∀ x, a x ≠ x)
    (hpres : ∀ ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ),
      (ℓ = Function.fixedPoints ⇑τ ∨ Disjoint ℓ (Function.fixedPoints ⇑τ)) → ⇑a '' ℓ = ℓ) :
    IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) a := by
  intro m hm
  by_cases hmC : m = Function.fixedPoints ⇑τ ∨ Disjoint m (Function.fixedPoints ⇑τ)
  · exact Or.inl (hpres m hm hmC)
  · right
    rw [Set.disjoint_left]
    rintro _ ⟨x, hxm, rfl⟩ haxm
    obtain ⟨ℓ, hℓ, hxℓ, hℓC⟩ : ∃ ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ), x ∈ ℓ ∧
        (ℓ = Function.fixedPoints ⇑τ ∨ Disjoint ℓ (Function.fixedPoints ⇑τ)) := by
      by_cases hxF : x ∈ Function.fixedPoints ⇑τ
      · exact ⟨_, mem_permTranslates_self N _, hxF, Or.inl rfl⟩
      · obtain ⟨ℓ, ⟨hℓ, hxℓ, hd⟩, -⟩ :=
          hG.existsUnique_parallel (mem_permTranslates_self N _) hxF
        exact ⟨ℓ, hℓ, hxℓ, Or.inr hd⟩
    have haxℓ : a x ∈ ℓ := by
      rw [← hpres ℓ hℓ hℓC]
      exact Set.mem_image_of_mem _ hxℓ
    have hmℓ : m = ℓ := by
      by_contra hne
      exact hafree x (eq_of_mem_of_mem hG hm hℓ hne haxm haxℓ hxm hxℓ)
    exact hmC (hmℓ ▸ hℓC)

theorem parallelInvolutionGroup_fix [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ) :
    (axisInvolutions N (parallelClass (permTranslates N (Function.fixedPoints ⇑τ))
      (Function.fixedPoints ⇑τ))).ncard = s ∧
    parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
      (Function.fixedPoints ⇑τ) ≤ N ∧
    IsElementaryAbelian 2 (parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
      (Function.fixedPoints ⇑τ)) ∧
    (∀ g ∈ parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ),
      ∀ ℓ ∈ parallelClass (permTranslates N (Function.fixedPoints ⇑τ)) (Function.fixedPoints ⇑τ),
        ⇑g '' ℓ = ℓ) ∧
    (∀ g ∈ parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ),
      ((g ≠ 1 ∧ ∃ x, g x = x) ↔ g ∈ axisInvolutions N
        (parallelClass (permTranslates N (Function.fixedPoints ⇑τ)) (Function.fixedPoints ⇑τ)))) ∧
    (∀ v ∈ axisInvolutions N (parallelClass (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ)), ∀ x, v x = x →
      ∀ g ∈ parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ), g x = x ↔ g = 1 ∨ g = v) ∧
    (∀ g ∈ parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ), (∀ x, g x ≠ x) →
      IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g) ∧
    (∃ a ∈ parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ), ∀ x, a x ≠ x) ∧
    ((∃ j, s = 2 ^ j) →
      Nat.card (parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ)) = 2 * s ∧
      {g | g ∈ parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
        (Function.fixedPoints ⇑τ) ∧ ∀ x, g x ≠ x}.ncard = s - 1) := by
  classical
  obtain ⟨hcard, -, -⟩ := hG.centralizer_involutions hCH
  have hSeq := axisInvolutions_parallelClass_eq hG hCH
  set S := axisInvolutions N (parallelClass (permTranslates N (Function.fixedPoints ⇑τ))
    (Function.fixedPoints ⇑τ)) with hSdef
  set S₀ := {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ} with hS₀
  set Q := parallelInvolutionGroup N (permTranslates N (Function.fixedPoints ⇑τ))
    (Function.fixedPoints ⇑τ) with hQdef
  have hFline : Function.fixedPoints ⇑τ ∈ permTranslates N (Function.fixedPoints ⇑τ) :=
    mem_permTranslates_self N _
  have hSnr : ∀ v ∈ S, v ∈ nonregInvolutions N := fun v hv => hv.1
  have hτS : τ ∈ S := by
    rw [hSeq]
    exact Set.mem_insert τ S₀
  have hτS₀ : τ ∉ S₀ := fun h1 => h1.2.2 rfl
  have hScard : S.ncard = s := by
    rw [hSeq, Set.ncard_insert_of_notMem hτS₀, hcard]
    have := hG.two_le
    omega
  have hcomm : S.Pairwise Commute := by
    intro u hu w hw huw
    have hne : Function.fixedPoints ⇑u ≠ Function.fixedPoints ⇑w := fun h1 =>
      huw (hG.bijOn_fixedPoints.injOn hu.1 hw.1 h1)
    exact commute_of_disjoint_axes hG hCH hu.1 hw.1
      ((parallelClass_eq_or_disjoint hG hFline hu.2 hw.2).resolve_left hne)
  have hQcomm : IsMulCommutative Q := Subgroup.isMulCommutative_closure hcomm
  have hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have hQN : Q ≤ N := (Subgroup.closure_le N).2 fun v hv => (hSnr v hv).1
  have hSQ : ∀ v ∈ S, v ∈ Q := fun v hv => Subgroup.subset_closure hv
  have hτQ : τ ∈ Q := hSQ τ hτS
  have hsq : ∀ g ∈ Q, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact mul_self_of_orderOf_eq_two (hSnr x hx).2.1
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hQc y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]
  have hEA : IsElementaryAbelian 2 Q :=
    { toIsMulCommutative := hQcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        exact hsq g g.2) }
  have hpres : ∀ g ∈ Q, ∀ ℓ ∈ parallelClass (permTranslates N (Function.fixedPoints ⇑τ))
      (Function.fixedPoints ⇑τ), ⇑g '' ℓ = ℓ := by
    intro g hg ℓ hℓ
    obtain ⟨u, hu, hu'⟩ := hG.bijOn_fixedPoints.surjOn hℓ.1
    have hu'' : Function.fixedPoints ⇑u = ℓ := hu'
    have huS : u ∈ S := ⟨hu, by rw [hu'']; exact hℓ⟩
    have hgu : g * u = u * g := setLike_mul_comm hg (hSQ u huS)
    have h1 : g * u * g⁻¹ = u := by rw [hgu, mul_inv_cancel_right]
    rw [← hu'', ← fixedPoints_conj, h1]
  have hfixS : ∀ g ∈ Q, ((g ≠ 1 ∧ ∃ x, g x = x) ↔ g ∈ S) := by
    intro g hg
    constructor
    · rintro ⟨hg1, x, hx⟩
      have hg2 : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq g hg) hg1
      have hgnr : g ∈ nonregInvolutions N := ⟨hQN hg, hg2, x, hx⟩
      rw [hSeq]
      by_cases hgτ : g = τ
      · rw [hgτ]
        exact Set.mem_insert τ S₀
      · exact Or.inr ⟨hgnr, setLike_mul_comm hg hτQ, hgτ⟩
    · intro hgS
      obtain ⟨-, hg2, x, hx⟩ := hSnr g hgS
      refine ⟨fun h1 => ?_, x, hx⟩
      rw [h1, orderOf_one] at hg2
      omega
  have hstab : ∀ v ∈ S, ∀ x, v x = x → ∀ g ∈ Q, g x = x ↔ g = 1 ∨ g = v := by
    intro v hv x hvx g hg
    constructor
    · intro hgx
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · right
        have hgS := (hfixS g hg).1 ⟨hg1, x, hgx⟩
        have hFF : Function.fixedPoints ⇑g = Function.fixedPoints ⇑v :=
          (parallelClass_eq_or_disjoint hG hFline hgS.2 hv.2).resolve_right
            (Set.not_disjoint_iff.2 ⟨x, hgx, hvx⟩)
        exact hG.bijOn_fixedPoints.injOn hgS.1 hv.1 hFF
    · rintro (rfl | rfl)
      · rfl
      · exact hvx
  have hdil : ∀ g ∈ Q, (∀ x, g x ≠ x) →
      IsDilatation (permTranslates N (Function.fixedPoints ⇑τ)) g := fun g hg hgf =>
    isDilatation_of_preserves_parallel_class hG hgf fun ℓ hℓ hℓF => hpres g hg ℓ ⟨hℓ, hℓF⟩
  have h1S : (1 : Equiv.Perm Ω) ∉ S := fun h1 => ((hfixS 1 (one_mem Q)).2 h1).1 rfl
  have hcardS1 : (insert 1 S).ncard = s + 1 := by
    rw [Set.ncard_insert_of_notMem h1S, hScard]
  have hsubQ : insert 1 S ⊆ (Q : Set (Equiv.Perm Ω)) := by
    rintro g (rfl | hg)
    · exact Q.one_mem
    · exact hSQ g hg
  have heven : 2 ∣ Nat.card Q := by
    have h1 := Subgroup.orderOf_dvd_natCard Q hτQ
    rwa [hG.orderOf_eq] at h1
  have hQcardS : Nat.card Q = (Q : Set (Equiv.Perm Ω)).ncard := (Nat.card_coe_set_eq _).symm
  have hlt : s + 1 < Nat.card Q := by
    have h1 : s + 1 ≤ Nat.card Q := by
      rw [hQcardS, ← hcardS1]
      exact Set.ncard_le_ncard hsubQ
    rcases h1.lt_or_eq with h2 | h2
    · exact h2
    · exfalso
      rw [← h2] at heven
      obtain ⟨k, hk⟩ := hG.even
      omega
  have hfpf : {g | g ∈ Q ∧ ∀ x, g x ≠ x} = (Q : Set (Equiv.Perm Ω)) \ insert 1 S := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, SetLike.mem_coe, not_or]
    constructor
    · rintro ⟨hg, hgf⟩
      refine ⟨hg, fun h1 => hgf α (by rw [h1]; rfl), fun hgS => ?_⟩
      obtain ⟨-, x, hx⟩ := (hfixS g hg).2 hgS
      exact hgf x hx
    · rintro ⟨hg, hg1, hgS⟩
      exact ⟨hg, fun x hx => hgS ((hfixS g hg).1 ⟨hg1, x, hx⟩)⟩
  have hfpfcard : {g | g ∈ Q ∧ ∀ x, g x ≠ x}.ncard = Nat.card Q - (s + 1) := by
    rw [hfpf, Set.ncard_sdiff hsubQ, hcardS1, hQcardS]
  have hexists : ∃ a ∈ Q, ∀ x, a x ≠ x := by
    have h1 : {g | g ∈ Q ∧ ∀ x, g x ≠ x}.ncard ≠ 0 := by
      rw [hfpfcard]
      omega
    obtain ⟨a, ha, haf⟩ := Set.nonempty_of_ncard_ne_zero h1
    exact ⟨a, ha, haf⟩
  have horder : (∃ j, s = 2 ^ j) →
      Nat.card Q = 2 * s ∧ {g | g ∈ Q ∧ ∀ x, g x ≠ x}.ncard = s - 1 := by
    rintro ⟨j, hj⟩
    have horb : Nat.card ↥(MulAction.orbit Q α) ≤ s := by
      rw [Nat.card_coe_set_eq, ← hG.card_fix]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      rintro _ ⟨g, rfl⟩
      have h1 := hpres g g.2 _ ⟨hFline, Or.inl rfl⟩
      show (g : Equiv.Perm Ω) α ∈ Function.fixedPoints ⇑τ
      rw [← h1]
      exact Set.mem_image_of_mem _ hG.fix_left
    have hstab2 : Nat.card ↥(MulAction.stabilizer Q α) ≤ 2 := by
      have hmaps : ∀ g : MulAction.stabilizer Q α,
          ((g : Q) : Equiv.Perm Ω) ∈ ({1, τ} : Set (Equiv.Perm Ω)) := by
        intro g
        have hgα : ((g : Q) : Equiv.Perm Ω) α = α := MulAction.mem_stabilizer_iff.1 g.2
        exact (hstab τ hτS α hG.fix_left _ (g : Q).2).1 hgα
      calc Nat.card ↥(MulAction.stabilizer Q α) ≤ Nat.card ↥({1, τ} : Set (Equiv.Perm Ω)) :=
            Nat.card_le_card_of_injective (fun g => ⟨_, hmaps g⟩) (fun g g' h1 => by
              have h2 : ((g : Q) : Equiv.Perm Ω) = ((g' : Q) : Equiv.Perm Ω) := Subtype.mk.inj h1
              exact Subtype.ext (Subtype.ext h2))
        _ = ({1, τ} : Set (Equiv.Perm Ω)).ncard := Nat.card_coe_set_eq _
        _ = 2 := Set.ncard_pair hG.tau_ne_one.symm
    have hle : Nat.card Q ≤ 2 * s := by
      rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Q α), Nat.card_prod]
      calc Nat.card ↥(MulAction.orbit Q α) * Nat.card ↥(MulAction.stabilizer Q α) ≤ s * 2 :=
            Nat.mul_le_mul horb hstab2
        _ = 2 * s := by ring
    have hp : IsPGroup 2 Q := fun g => ⟨1, Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
      exact hsq g g.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hp
    subst hj
    have h1j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hjk : j < k := by
      by_contra hkj
      push Not at hkj
      have : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hkj
      omega
    have hkj : k ≤ j + 1 := by
      by_contra hkj
      push Not at hkj
      have h2 : 2 ^ (j + 2) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkj
      rw [pow_succ, pow_succ] at h2
      omega
    have hQ2 : Nat.card Q = 2 * 2 ^ j := by
      rw [hk, show k = j + 1 by omega, pow_succ, mul_comm]
    refine ⟨hQ2, ?_⟩
    rw [hfpfcard, hQ2]
    omega
  exact ⟨hScard, hQN, hEA, hpres, hfixS, hstab, hdil, hexists, horder⟩

theorem exists_translation_preserving_parallel_class [Finite Ω]
    (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ) :
    ∃ a ∈ N, orderOf a = 2 ∧ (∀ x, a x ≠ x) ∧
      ∀ ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ),
        (ℓ = Function.fixedPoints ⇑τ ∨ Disjoint ℓ (Function.fixedPoints ⇑τ)) → ⇑a '' ℓ = ℓ := by
  obtain ⟨-, hQN, hEA, hpres, -, -, -, ⟨a, haQ, hafree⟩, -⟩ := parallelInvolutionGroup_fix hG hCH
  have ha1 : a ≠ 1 := fun h1 => hafree α (by rw [h1]; rfl)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haQ) ha1
  exact ⟨a, hQN haQ, ha2, hafree, fun ℓ hℓ hℓF => hpres a haQ ℓ ⟨hℓ, hℓF⟩⟩

theorem exists_regular_normal_translations [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ) :
    ∃ A : Subgroup (Equiv.Perm Ω), A ≤ N ∧ (A.subgroupOf N).Normal ∧
      (∀ g, g ∈ A ↔ g ∈ N ∧ (∀ ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ),
          ⇑g '' ℓ = ℓ ∨ Disjoint (⇑g '' ℓ) ℓ) ∧ (g = 1 ∨ ∀ x, g x ≠ x)) ∧
      (∀ g, g ∈ A ↔ g = 1 ∨ g ∈ regInvolutions N) ∧
      (∀ x y : Ω, ∃! a : A, (a : Equiv.Perm Ω) x = y) ∧
      Nat.card A = s ^ 2 ∧
      (∀ g ∈ A, g α = α → g = 1) ∧
      (∀ g ∈ N, ∃ a ∈ A, ∃ h ∈ N, h α = α ∧ g = a * h) := by
  classical
  set A := translationGroup hG with hAdef
  have hAN : A ≤ N := fun g hg => hg.1
  have hconj : ∀ g ∈ A, ∀ h ∈ N, h * g * h⁻¹ ∈ A := by
    rintro g ⟨hgN, hg, hg1⟩ h hh
    refine ⟨mul_mem (mul_mem hh hgN) (inv_mem hh), isDilatation_conj hh hg, ?_⟩
    rcases hg1 with rfl | hgf
    · left
      group
    · right
      intro x hx
      apply hgf (h⁻¹ x)
      have h1 : h (g (h⁻¹ x)) = x := hx
      have h2 := congrArg (⇑h⁻¹) h1
      rwa [GMSAffine.perm_inv_apply] at h2
  have hAn : (A.subgroupOf N).Normal := by
    constructor
    intro g hg h
    rw [mem_subgroupOf] at hg ⊢
    exact hconj g hg h h.2
  have hfree : ∀ g ∈ A, ∀ x, g x = x → g = 1 := by
    rintro g ⟨-, -, hg1⟩ x hx
    rcases hg1 with h1 | hgf
    · exact h1
    · exact absurd hx (hgf x)
  obtain ⟨a, haN, ha2, hafree, hpres⟩ := exists_translation_preserving_parallel_class hG hCH
  have haA : a ∈ A :=
    ⟨haN, isDilatation_of_preserves_parallel_class hG hafree hpres, Or.inr hafree⟩
  have htransα : ∀ y, ∃ g ∈ A, g α = y := by
    intro y
    by_cases hy : y = α
    · exact ⟨1, A.one_mem, by rw [hy]; rfl⟩
    · obtain ⟨h, hh, hhα, hhy⟩ := hG.two_trans α (a α) α y (hafree α).symm (Ne.symm hy)
      refine ⟨h * a * h⁻¹, hconj a haA h hh, ?_⟩
      show h (a (h⁻¹ α)) = y
      rw [inv_apply_eq_of_apply_eq hhα, hhy]
  have hreg : ∀ x y : Ω, ∃! g : A, (g : Equiv.Perm Ω) x = y := by
    intro x y
    obtain ⟨g₁, hg₁, hg₁α⟩ := htransα x
    obtain ⟨g₂, hg₂, hg₂α⟩ := htransα y
    refine ⟨⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁)⟩, ?_, ?_⟩
    · show g₂ (g₁⁻¹ x) = y
      rw [← hg₁α, GMSAffine.perm_inv_apply, hg₂α]
    · rintro ⟨g, hg⟩ hgx
      have hgx' : g x = y := hgx
      apply Subtype.ext
      show g = g₂ * g₁⁻¹
      have h1 : (g₂ * g₁⁻¹)⁻¹ * g = 1 := by
        refine hfree _ (mul_mem (inv_mem (mul_mem hg₂ (inv_mem hg₁))) hg) x ?_
        show (g₂ * g₁⁻¹)⁻¹ (g x) = x
        rw [hgx', mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, ← hg₂α,
          GMSAffine.perm_inv_apply, hg₁α]
      calc g = (g₂ * g₁⁻¹) * ((g₂ * g₁⁻¹)⁻¹ * g) := by group
        _ = g₂ * g₁⁻¹ := by rw [h1, mul_one]
  have haR : a ∈ regInvolutions N := ⟨haN, ha2, hafree⟩
  have hregA : ∀ w ∈ regInvolutions N, w ∈ A := by
    intro w hw
    rw [hG.regInvolutions_eq haR] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    exact hconj a haA g hg
  have hchar : ∀ g, g ∈ A ↔ g = 1 ∨ g ∈ regInvolutions N := by
    intro g
    constructor
    · intro hg
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · right
        have hgα : g α ≠ α := fun h1 => hg1 (hfree g hg α h1)
        obtain ⟨w, ⟨hw, hwα⟩, -⟩ := hG.existsUnique_reg hgα
        obtain ⟨c, -, huniq⟩ := hreg α (g α)
        have h1 : (⟨g, hg⟩ : A) = ⟨w, hregA w hw⟩ :=
          (huniq ⟨g, hg⟩ rfl).trans (huniq ⟨w, hregA w hw⟩ hwα).symm
        rw [show g = w from congrArg Subtype.val h1]
        exact hw
    · rintro (rfl | hg)
      · exact A.one_mem
      · exact hregA g hg
  have hcardA : Nat.card A = s ^ 2 := by
    rw [← hG.card]
    refine Nat.card_congr (Equiv.ofBijective (fun g : A => (g : Equiv.Perm Ω) α)
      ⟨fun g g' hgg' => ?_, fun y => ?_⟩)
    · obtain ⟨c, -, hc⟩ := hreg α ((g : Equiv.Perm Ω) α)
      exact (hc g rfl).trans (hc g' hgg'.symm).symm
    · obtain ⟨g, hg, -⟩ := hreg α y
      exact ⟨g, hg⟩
  have hdec : ∀ g ∈ N, ∃ b ∈ A, ∃ h ∈ N, h α = α ∧ g = b * h := by
    intro g hg
    obtain ⟨⟨b, hb⟩, hbα, -⟩ := hreg α (g α)
    have hbα' : b α = g α := hbα
    refine ⟨b, hb, b⁻¹ * g, mul_mem (inv_mem (hAN hb)) hg, ?_, by group⟩
    show b⁻¹ (g α) = α
    rw [← hbα', GMSAffine.perm_inv_apply]
  exact ⟨A, hAN, hAn, fun g => mem_translationGroup hG, hchar, hreg, hcardA,
    fun g hg hgα => hfree g hg α hgα, hdec⟩

end EvenPairPlane

end CFSG.SeitzReduction.RankOne
