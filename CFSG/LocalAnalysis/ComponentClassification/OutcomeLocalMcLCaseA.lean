module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLGenerate
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def GenByTransvections (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
    Prop :=
  ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V), (∀ t ∈ S, IsF2Transvection t) ∧
    G = Subgroup.closure S

@[expose] def IsGInvariant (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (W : Submodule (ZMod 2) V) : Prop :=
  ∀ g ∈ G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W

@[expose] def IsIrreducibleOn (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) : Prop :=
  ∀ W : Submodule (ZMod 2) V, IsGInvariant G W → W = ⊥ ∨ W = ⊤

variable {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

theorem exists_moving_transvection (hgen : GenByTransvections G) {W : Submodule (ZMod 2) V}
    (hW : ¬ IsGInvariant G W) :
    ∃ (φ : Dual (ZMod 2) V) (a : V), φ ≠ 0 ∧ a ≠ 0 ∧ InG G φ a ∧ a ∉ W ∧
      ∃ w ∈ W, φ w = 1 := by
  obtain ⟨S, hS, rfl⟩ := hgen
  by_contra hno
  apply hW
  have hS' : ∀ t ∈ S, ∀ w ∈ W, (t : V →ₗ[ZMod 2] V) w ∈ W := by
    intro t ht w hw
    obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp (hS t ht)
    rw [tv_apply]
    by_cases haW : a ∈ W
    · exact W.add_mem hw (W.smul_mem _ haW)
    · rcases zmod2_eq_zero_or_one (φ w) with h0 | h1
      · rw [h0, zero_smul, add_zero]
        exact hw
      · exact absurd ⟨φ, a, hφ, ha, ⟨h, Subgroup.subset_closure ht⟩, haW, w, hw, h1⟩ hno
  have key : ∀ g ∈ Subgroup.closure S, (∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) ∧
      ∀ w ∈ W, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w ∈ W := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨φ, a, h, -, -, rfl⟩ := (isF2Transvection_iff t).mp (hS t ht)
      have h' := hS' _ ht
      exact ⟨h', by rwa [tv_inv]⟩
    | one => exact ⟨fun w hw => hw, fun w hw => by simpa using hw⟩
    | mul g₁ g₂ _ _ h₁ h₂ =>
      refine ⟨fun w hw => h₁.1 _ (h₂.1 w hw), fun w hw => ?_⟩
      rw [mul_inv_rev]
      exact h₂.2 _ (h₁.2 w hw)
    | inv g _ h => exact ⟨h.2, by simpa using h.1⟩
  exact fun g hg => (key g hg).1

section Dimension

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

theorem finrank_sup_span_of_notMem {X : Submodule (ZMod 2) M} {c : M} (hc : c ∉ X) :
    finrank (ZMod 2) (X ⊔ span (ZMod 2) {c} : Submodule (ZMod 2) M) = finrank (ZMod 2) X + 1 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ X.zero_mem)
  have hinf : X ⊓ span (ZMod 2) {c} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvX, hvc⟩
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hvc
    rcases zmod2_eq_zero_or_one r with rfl | rfl
    · rw [zero_smul]
      exact zero_mem _
    · rw [one_smul] at hvX
      exact absurd hvX hc
  have h := finrank_sup_add_finrank_inf_eq X (span (ZMod 2) {c})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hc0] at h
  exact h

theorem finrank_inf_ker_add_one {X : Submodule (ZMod 2) M} {χ : Dual (ZMod 2) M} {x₁ : M}
    (hx₁ : x₁ ∈ X) (hχx₁ : χ x₁ = 1) :
    finrank (ZMod 2) (X ⊓ LinearMap.ker χ : Submodule (ZMod 2) M) + 1 =
      finrank (ZMod 2) X := by
  have hsup : X ⊔ LinearMap.ker χ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hk : v + χ v • x₁ ∈ LinearMap.ker χ := by
      rw [LinearMap.mem_ker, map_add, LinearMap.map_smul, hχx₁, smul_eq_mul, mul_one,
        zmod2_scalar_add_self]
    have : v = (v + χ v • x₁) + χ v • x₁ := by rw [add_assoc, zmod2_add_self, add_zero]
    rw [this]
    exact add_mem (mem_sup_right hk) (mem_sup_left (X.smul_mem _ hx₁))
  have hker : finrank (ZMod 2) (LinearMap.ker χ) + 1 = finrank (ZMod 2) M := by
    have h := LinearMap.finrank_range_add_finrank_ker χ
    have hrange : LinearMap.range χ = ⊤ := by
      rw [eq_top_iff]
      intro c _
      exact ⟨c • x₁, by rw [LinearMap.map_smul, hχx₁, smul_eq_mul, mul_one]⟩
    rw [hrange, finrank_top, finrank_self] at h
    omega
  have h := finrank_sup_add_finrank_inf_eq X (LinearMap.ker χ)
  rw [hsup, finrank_top] at h
  omega

end Dimension

@[expose] def IsThick (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (X : Submodule (ZMod 2) V) (J : Submodule (ZMod 2) (Dual (ZMod 2) V)) : Prop :=
  ∀ x ∈ X, ∀ θ ∈ J, InG G θ x

theorem IsThick.sup_span {X : Submodule (ZMod 2) V} {J : Submodule (ZMod 2) (Dual (ZMod 2) V)}
    (hXJ : IsThick G X J) {χ : Dual (ZMod 2) V} {c : V} (hχc : InG G χ c)
    (hcJ : ∀ θ ∈ J, θ c = 0) {x₁ : V} (hx₁ : x₁ ∈ X) (hχx₁ : χ x₁ = 1) :
    IsThick G (X ⊔ span (ZMod 2) {c}) J := by
  intro y hy θ hθ
  have hθc : InG G θ c := hχc.of_dihedral (hXJ x₁ hx₁ θ hθ) hχx₁ (hcJ θ hθ)
  have hle : X ⊔ span (ZMod 2) {c} ≤ axisVectors G θ :=
    sup_le (fun x hx => hXJ x hx θ hθ) (span_le.mpr (Set.singleton_subset_iff.mpr hθc))
  exact hle hy

theorem IsThick.inf_ker {X : Submodule (ZMod 2) V} {J : Submodule (ZMod 2) (Dual (ZMod 2) V)}
    (hXJ : IsThick G X J) {χ : Dual (ZMod 2) V} {c : V} (hχc : InG G χ c)
    {θ₀ : Dual (ZMod 2) V} (hθ₀ : θ₀ ∈ J) (hθ₀c : θ₀ c = 1) :
    IsThick G (X ⊓ LinearMap.ker χ) (J ⊔ span (ZMod 2) {χ}) := by
  intro x hx θ hθ
  have hχx : InG G χ x := (hXJ x hx.1 θ₀ hθ₀).of_dihedral hχc hθ₀c hx.2
  have hle : J ⊔ span (ZMod 2) {χ} ≤ centerForms G x :=
    sup_le (fun θ hθ => hXJ x hx.1 θ hθ) (span_le.mpr (Set.singleton_subset_iff.mpr hχx))
  exact hle hθ

theorem isThick_span_singleton (x : V) : IsThick G (span (ZMod 2) {x}) (centerForms G x) :=
  fun _ hy θ hθ =>
    (span_le.mpr (Set.singleton_subset_iff.mpr hθ) : span (ZMod 2) {x} ≤ axisVectors G θ) hy

theorem isThick_span_pair {x y : V} {J : Submodule (ZMod 2) (Dual (ZMod 2) V)}
    (hJx : J ≤ centerForms G x) (hJy : J ≤ centerForms G y) :
    IsThick G (span (ZMod 2) {x} ⊔ span (ZMod 2) {y}) J :=
  fun _ hz θ hθ =>
    (sup_le (span_le.mpr (Set.singleton_subset_iff.mpr (hJx hθ)))
      (span_le.mpr (Set.singleton_subset_iff.mpr (hJy hθ))) :
      span (ZMod 2) {x} ⊔ span (ZMod 2) {y} ≤ axisVectors G θ) hz

theorem add_smul_ne_zero {χ : Dual (ZMod 2) V} {a c : V} (hχc : χ c = 0) (ha : a ≠ 0) :
    a + χ a • c ≠ 0 := by
  intro h
  have h1 : χ a = 0 := by
    have := congrArg χ h
    rwa [map_add, map_smul, hχc, smul_zero, add_zero, map_zero] at this
  rw [h1, zero_smul, add_zero] at h
  exact ha h

theorem exists_form_eq_zero_eq_one {x x' : V} (hx' : x' ∉ span (ZMod 2) {x}) :
    ∃ ω : Dual (ZMod 2) V, ω x = 0 ∧ ω x' = 1 := by
  obtain ⟨f, hf, hmap⟩ := (span (ZMod 2) {x}).exists_dual_map_eq_bot_of_notMem hx'
    inferInstance
  refine ⟨f, ?_, (zmod2_eq_zero_or_one _).resolve_left hf⟩
  have : f x ∈ (span (ZMod 2) {x}).map f := mem_map_of_mem (mem_span_singleton_self x)
  rwa [hmap, mem_bot] at this

theorem notMem_span_of_inG {x y : V} {ψ' : Dual (ZMod 2) V} (hy : y ≠ 0) (hψ' : InG G ψ' y)
    (hψ'x : ψ' x = 1) :
    y ∉ span (ZMod 2) {x} := fun hmem => by
  obtain ⟨r, rfl⟩ := mem_span_singleton.mp hmem
  have h0 := hψ'.apply_eq_zero
  rw [map_smul, hψ'x, smul_eq_mul, mul_one] at h0
  rw [h0, zero_smul] at hy
  exact hy rfl

theorem forall_inG_map {x : V} (hx : ∀ φ : Dual (ZMod 2) V, φ x = 0 → InG G φ x)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V} (hg : g ∈ G) :
    ∀ φ : Dual (ZMod 2) V, φ ((g : V →ₗ[ZMod 2] V) x) = 0 →
      InG G φ ((g : V →ₗ[ZMod 2] V) x) := by
  intro φ hφ
  have h := (hx (φ ∘ₗ (g : V →ₗ[ZMod 2] V)) hφ).conj hg
  have hcomp : (φ ∘ₗ (g : V →ₗ[ZMod 2] V)) ∘ₗ
      ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = φ := by
    ext v
    change φ (((g * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = φ v
    rw [mul_inv_cancel]
    rfl
  rwa [hcomp] at h

@[expose] def fullCentres (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
    Submodule (ZMod 2) V where
  carrier := {x | ∀ φ : Dual (ZMod 2) V, φ x = 0 → InG G φ x}
  zero_mem' φ _ := inG_zero_right φ
  smul_mem' c x hx := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · intro φ _
      rw [zero_smul]
      exact inG_zero_right φ
    · rwa [one_smul]
  add_mem' {x x'} hx hx' := by
    intro φ hφ
    rcases zmod2_eq_zero_or_one (φ x) with h0 | h1
    · have h0' : φ x' = 0 := by
        rw [map_add, h0, zero_add] at hφ
        exact hφ
      exact (hx φ h0).add_right (hx' φ h0')
    · by_cases hxx : x' ∈ span (ZMod 2) {x}
      · obtain ⟨r, rfl⟩ := mem_span_singleton.mp hxx
        rcases zmod2_eq_zero_or_one r with rfl | rfl
        · rw [zero_smul, add_zero] at hφ ⊢
          exact hx φ hφ
        · rw [one_smul, zmod2_add_self]
          exact inG_zero_right φ
      · obtain ⟨ω, hωx, hωx'⟩ := exists_form_eq_zero_eq_one hxx
        obtain ⟨hω, hmem⟩ := hx ω hωx
        have happ : (tv ω x hω : V →ₗ[ZMod 2] V) x' = x + x' := by
          rw [tv_apply, hωx', one_smul, add_comm]
        have h := forall_inG_map hx' hmem φ (by rw [happ]; exact hφ)
        rwa [happ] at h

theorem isGInvariant_fullCentres : IsGInvariant G (fullCentres G) :=
  fun _ hg _ hx => forall_inG_map hx hg

variable [FiniteDimensional (ZMod 2) V]

theorem IsThick.finrank_add_le {X : Submodule (ZMod 2) V}
    {J : Submodule (ZMod 2) (Dual (ZMod 2) V)} (hXJ : IsThick G X J) :
    finrank (ZMod 2) X + finrank (ZMod 2) J ≤ finrank (ZMod 2) V := by
  have hle : J ≤ X.dualAnnihilator := fun θ hθ =>
    (mem_dualAnnihilator θ).mpr fun x hx => (hXJ x hx θ hθ).apply_eq_zero
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq X
  have := Submodule.finrank_mono hle
  omega

theorem IsThick.exists_finrank_le (hgen : GenByTransvections G) (hirr : IsIrreducibleOn G)
    {X : Submodule (ZMod 2) V} {J : Submodule (ZMod 2) (Dual (ZMod 2) V)} (hXJ : IsThick G X J)
    (hX : X ≠ ⊥) (hJ : J ≠ ⊥) :
    ∃ x : V, x ≠ 0 ∧ finrank (ZMod 2) X + finrank (ZMod 2) J ≤
      finrank (ZMod 2) (centerForms G x) + 1 := by
  set N := finrank (ZMod 2) V
  suffices key : ∀ m : ℕ, ∀ (X : Submodule (ZMod 2) V) (J : Submodule (ZMod 2) (Dual (ZMod 2) V)),
      (N + 1 - (finrank (ZMod 2) X + finrank (ZMod 2) J)) * (N + 2) + finrank (ZMod 2) X = m →
      IsThick G X J → X ≠ ⊥ → J ≠ ⊥ → ∃ x : V, x ≠ 0 ∧
        finrank (ZMod 2) X + finrank (ZMod 2) J ≤ finrank (ZMod 2) (centerForms G x) + 1 from
    key _ X J rfl hXJ hX hJ
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X J hm hXJ hX hJ
  have hs := hXJ.finrank_add_le
  by_cases h1 : finrank (ZMod 2) X = 1
  ·
    obtain ⟨x₀, hx₀X, hx₀⟩ := (Submodule.ne_bot_iff X).mp hX
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one h1 hx₀X hx₀
    refine ⟨x₀, hx₀, ?_⟩
    have hle : J ≤ centerForms G x₀ := fun θ hθ => hXJ x₀ hx₀X θ hθ
    have := Submodule.finrank_mono hle
    omega
  ·
    have hXtop : X ≠ ⊤ := by
      rintro rfl
      apply hJ
      rw [eq_bot_iff]
      intro θ hθ
      rw [mem_bot]
      exact LinearMap.ext fun v => (hXJ v mem_top θ hθ).apply_eq_zero
    have hninv : ¬ IsGInvariant G X := fun hinv => by
      rcases hirr X hinv with h | h
      · exact hX h
      · exact hXtop h
    obtain ⟨χ, c, -, -, hχc, hcX, x₁, hx₁, hχx₁⟩ := exists_moving_transvection hgen hninv
    by_cases hcJ : ∀ θ ∈ J, θ c = 0
    ·
      have hthick := hXJ.sup_span hχc hcJ hx₁ hχx₁
      have hdim := finrank_sup_span_of_notMem hcX
      have hs' := hthick.finrank_add_le
      obtain ⟨x, hx, hle⟩ := ih _ (by
        rw [← hm, hdim]
        have : N + 1 - (finrank (ZMod 2) X + 1 + finrank (ZMod 2) J) + 1 =
            N + 1 - (finrank (ZMod 2) X + finrank (ZMod 2) J) := by omega
        nlinarith) _ _ rfl hthick
        (fun h => hX (eq_bot_iff.mpr ((le_sup_left : X ≤ _).trans h.le))) hJ
      exact ⟨x, hx, by omega⟩
    ·
      obtain ⟨θ₀, hθ₀, hθ₀c⟩ : ∃ θ₀ ∈ J, θ₀ c ≠ 0 := by
        by_contra hne
        exact hcJ fun θ hθ => by_contra fun h => hne ⟨θ, hθ, h⟩
      have hθ₀c1 : θ₀ c = 1 := (zmod2_eq_zero_or_one _).resolve_left hθ₀c
      have hthick := hXJ.inf_ker hχc hθ₀ hθ₀c1
      have hdimX := finrank_inf_ker_add_one hx₁ hχx₁
      have hχJ : χ ∉ J := fun h => by
        have := (hXJ x₁ hx₁ χ h).apply_eq_zero
        rw [hχx₁] at this
        exact one_ne_zero this
      have hdimJ := finrank_sup_span_of_notMem hχJ
      have hX' : X ⊓ LinearMap.ker χ ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hdimX
        omega
      have hJ' : J ⊔ span (ZMod 2) {χ} ≠ ⊥ :=
        fun h => hJ (eq_bot_iff.mpr ((le_sup_left : J ≤ _).trans h.le))
      obtain ⟨x, hx, hle⟩ := ih _ (by
        rw [← hm, hdimJ]
        have : finrank (ZMod 2) (X ⊓ LinearMap.ker χ : Submodule (ZMod 2) V) +
            (finrank (ZMod 2) J + 1) = finrank (ZMod 2) X + finrank (ZMod 2) J := by omega
        rw [this]
        omega) _ _ rfl hthick hX' hJ'
      exact ⟨x, hx, by omega⟩

theorem finrank_centerForms_add_one_le {x : V} (hx : x ≠ 0) :
    finrank (ZMod 2) (centerForms G x) + 1 ≤ finrank (ZMod 2) V := by
  have h := (isThick_span_singleton (G := G) x).finrank_add_le
  rw [finrank_span_singleton hx] at h
  omega

@[expose] def ThickBound (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (d : ℕ) :
    Prop :=
  ∀ (X : Submodule (ZMod 2) V) (J : Submodule (ZMod 2) (Dual (ZMod 2) V)), IsThick G X J →
    X ≠ ⊥ → J ≠ ⊥ → finrank (ZMod 2) X + finrank (ZMod 2) J ≤ d + 1

section Centre

variable {d : ℕ} {x y : V} {ψ' : Dual (ZMod 2) V}

theorem exists_centerForms_apply_eq_one (hbound : ThickBound G d)
    (hdx : finrank (ZMod 2) (centerForms G x) = d) (hd : 1 ≤ d) (hx : x ≠ 0) (hy : y ≠ 0)
    (hψ' : InG G ψ' y) (hψ'x : ψ' x = 1) : ∃ θ ∈ centerForms G x, θ y = 1 := by
  by_contra hno
  have hle : centerForms G x ≤ centerForms G y := fun θ hθ =>
    hψ'.of_dihedral (mem_centerForms.mp hθ) hψ'x
      ((zmod2_eq_zero_or_one _).resolve_right fun h => hno ⟨θ, hθ, h⟩)
  have hthick := isThick_span_pair (G := G) (le_refl _) hle
  have hdim := finrank_sup_span_of_notMem (notMem_span_of_inG hy hψ' hψ'x)
  rw [finrank_span_singleton hx] at hdim
  have hX : span (ZMod 2) {x} ⊔ span (ZMod 2) {y} ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  have hJ : centerForms G x ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdx
    omega
  have := hbound _ _ hthick hX hJ
  omega

theorem le_finrank_inf_add_one (hdx : finrank (ZMod 2) (centerForms G x) = d)
    (hψ' : InG G ψ' y) (hψ'x : ψ' x = 1) {θ₁ : Dual (ZMod 2) V} (hθ₁ : θ₁ ∈ centerForms G x)
    (hθ₁y : θ₁ y = 1) :
    d ≤ finrank (ZMod 2) (centerForms G x ⊓ centerForms G y :
      Submodule (ZMod 2) (Dual (ZMod 2) V)) + 1 := by
  have h := finrank_inf_ker_add_one (χ := Module.Dual.eval (ZMod 2) V y) hθ₁
    (by rw [Module.Dual.eval_apply]; exact hθ₁y)
  have hle : centerForms G x ⊓ LinearMap.ker (Module.Dual.eval (ZMod 2) V y) ≤
      centerForms G x ⊓ centerForms G y := fun θ hθ => by
    have h2 : θ y = 0 := by
      have h3 : θ ∈ LinearMap.ker (Module.Dual.eval (ZMod 2) V y) := hθ.2
      rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at h3
    exact ⟨hθ.1, hψ'.of_dihedral (mem_centerForms.mp hθ.1) hψ'x h2⟩
  have := Submodule.finrank_mono hle
  omega

theorem false_of_moving_of_apply_eq_zero (hbound : ThickBound G d)
    (hdx : finrank (ZMod 2) (centerForms G x) = d) (hd : 2 ≤ d) (hx : x ≠ 0) (hy : y ≠ 0)
    (hψ' : InG G ψ' y) (hψ'x : ψ' x = 1) {χ : Dual (ZMod 2) V} {e : V} (hχe : InG G χ e)
    (he : e ≠ 0) (hχx : χ x = 0) (hχy : χ y = 1) {k : V}
    (hk : k ∈ (centerForms G x ⊔ centerForms G y).dualCoannihilator) (hχk : χ k = 1) :
    False := by
  have hχBx : ¬ InG G χ x := fun h => by
    have := (mem_dualCoannihilator k).mp hk χ (mem_sup_left h)
    rw [hχk] at this
    exact one_ne_zero this
  have hBxe : ∀ θ ∈ centerForms G x, θ e = 0 := fun θ hθ =>
    (zmod2_eq_zero_or_one _).resolve_right fun h =>
      hχBx ((mem_centerForms.mp hθ).of_dihedral hχe h hχx)
  obtain ⟨θ₁, hθ₁, hθ₁y⟩ := exists_centerForms_apply_eq_one hbound hdx (by omega) hx hy hψ' hψ'x
  have hdJ := le_finrank_inf_add_one hdx hψ' hψ'x hθ₁ hθ₁y
  have hthick := isThick_span_pair (G := G) (J := centerForms G x ⊓ centerForms G y)
    inf_le_left inf_le_right
  have hthick' := hthick.sup_span hχe (fun θ hθ => hBxe θ hθ.1)
    (mem_sup_right (mem_span_singleton_self y)) hχy
  have hdim2 := finrank_sup_span_of_notMem (notMem_span_of_inG hy hψ' hψ'x)
  rw [finrank_span_singleton hx] at hdim2
  have hJ : centerForms G x ⊓ centerForms G y ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdJ
    omega
  have heX : e ∈ span (ZMod 2) {x} ⊔ span (ZMod 2) {y} := by
    by_contra heX
    have hdim3 := finrank_sup_span_of_notMem heX
    have hX : span (ZMod 2) {x} ⊔ span (ZMod 2) {y} ⊔ span (ZMod 2) {e} ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hdim3
      omega
    have := hbound _ _ hthick' hX hJ
    omega
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup.mp heX
  obtain ⟨r, rfl⟩ := mem_span_singleton.mp hu
  obtain ⟨s, rfl⟩ := mem_span_singleton.mp hw
  rcases zmod2_eq_zero_or_one s with rfl | rfl
  · rw [zero_smul, add_zero] at hχe he
    rcases zmod2_eq_zero_or_one r with rfl | rfl
    · rw [zero_smul] at he
      exact he rfl
    · rw [one_smul] at hχe
      exact hχBx hχe
  · have h := hBxe θ₁ hθ₁
    rw [map_add, map_smul, map_smul, (mem_centerForms.mp hθ₁).apply_eq_zero, smul_zero,
      one_smul, hθ₁y, zero_add] at h
    exact one_ne_zero h

theorem false_of_moving_of_apply_eq_one (hbound : ThickBound G d)
    (hdx : finrank (ZMod 2) (centerForms G x) = d) (hd : 2 ≤ d) (hx : x ≠ 0) (hy : y ≠ 0)
    (hψ' : InG G ψ' y) (hψ'x : ψ' x = 1) {χ : Dual (ZMod 2) V} {e : V} (hχe : InG G χ e)
    (he : e ≠ 0) (hχy : χ y = 1) {k : V}
    (hk : k ∈ (centerForms G x ⊔ centerForms G y).dualCoannihilator) (hχk : χ k = 1) :
    False := by
  rcases zmod2_eq_zero_or_one (χ x) with hχx | hχx
  · exact false_of_moving_of_apply_eq_zero hbound hdx hd hx hy hψ' hψ'x hχe he hχx hχy hk hχk
  · have hψ'k : ψ' k = 0 := (mem_dualCoannihilator k).mp hk ψ' (mem_sup_right hψ')
    have hψ'y := hψ'.apply_eq_zero
    refine false_of_moving_of_apply_eq_zero hbound hdx hd hx hy hψ' hψ'x (hχe.conj_tv hψ')
      (add_smul_ne_zero hψ'y he) ?_ ?_ hk ?_
    · rw [LinearMap.add_apply, LinearMap.smul_apply, hχy, one_smul, hχx, hψ'x]
      exact zmod2_scalar_add_self 1
    · rw [LinearMap.add_apply, LinearMap.smul_apply, hχy, one_smul, hψ'y, add_zero]
    · rw [LinearMap.add_apply, LinearMap.smul_apply, hχk, hψ'k, smul_zero, add_zero]

theorem isGInvariant_dualCoannihilator (hgen : GenByTransvections G) (hbound : ThickBound G d)
    (hdx : finrank (ZMod 2) (centerForms G x) = d) (hd : 2 ≤ d) (hx : x ≠ 0) (hy : y ≠ 0)
    (hψ' : InG G ψ' y) (hψ'x : ψ' x = 1) :
    IsGInvariant G (centerForms G x ⊔ centerForms G y).dualCoannihilator := by
  by_contra hK
  obtain ⟨χ, e, -, he, hχe, heK, k, hk, hχk⟩ := exists_moving_transvection hgen hK
  obtain ⟨θ₁, hθ₁, hθ₁y⟩ := exists_centerForms_apply_eq_one hbound hdx (by omega) hx hy hψ' hψ'x
  rcases zmod2_eq_zero_or_one (χ y) with hχy | hχy
  · rcases zmod2_eq_zero_or_one (χ x) with hχx | hχx
    ·
      apply heK
      rw [mem_dualCoannihilator]
      intro θ hθ
      obtain ⟨θx, hθx, θy, hθy, rfl⟩ := mem_sup.mp hθ
      have hnot : ∀ u, InG G χ u → χ ∈ centerForms G x ⊔ centerForms G y → False :=
        fun u _ hmem => by
          have := (mem_dualCoannihilator k).mp hk χ hmem
          rw [hχk] at this
          exact one_ne_zero this
      have h1 : θx e = 0 := (zmod2_eq_zero_or_one _).resolve_right fun h => by
        have hχ := (mem_centerForms.mp hθx).of_dihedral hχe h hχx
        exact hnot x hχ (mem_sup_left hχ)
      have h2 : θy e = 0 := (zmod2_eq_zero_or_one _).resolve_right fun h => by
        have hχ := (mem_centerForms.mp hθy).of_dihedral hχe h hχy
        exact hnot y hχ (mem_sup_right hχ)
      rw [LinearMap.add_apply, h1, h2, add_zero]
    ·
      have hθ₁k : θ₁ k = 0 := (mem_dualCoannihilator k).mp hk θ₁ (mem_sup_left hθ₁)
      have hθ₁x := (mem_centerForms.mp hθ₁).apply_eq_zero
      refine false_of_moving_of_apply_eq_one hbound hdx hd hx hy hψ' hψ'x
        (hχe.conj_tv (mem_centerForms.mp hθ₁)) (add_smul_ne_zero hθ₁x he) ?_ hk ?_
      · rw [LinearMap.add_apply, LinearMap.smul_apply, hχy, hχx, one_smul, hθ₁y, zero_add]
      · rw [LinearMap.add_apply, LinearMap.smul_apply, hχk, hθ₁k, smul_zero, add_zero]
  · exact false_of_moving_of_apply_eq_one hbound hdx hd hx hy hψ' hψ'x hχe he hχy hk hχk

theorem forall_inG_of_maximal (hgen : GenByTransvections G) (hirr : IsIrreducibleOn G)
    (hbound : ThickBound G d)
    (hmax : ∀ z : V, z ≠ 0 → finrank (ZMod 2) (centerForms G z) ≤ d)
    (hdx : finrank (ZMod 2) (centerForms G x) = d) (hd : 2 ≤ d) (hx : x ≠ 0) :
    ∀ φ : Dual (ZMod 2) V, φ x = 0 → InG G φ x := by
  have h4 := finrank_centerForms_add_one_le (G := G) hx
  have hxinv : ¬ IsGInvariant G (span (ZMod 2) {x}) := fun hinv => by
    rcases hirr _ hinv with h | h
    · exact hx (span_singleton_eq_bot.mp h)
    · have h2 : finrank (ZMod 2) (span (ZMod 2) {x}) = finrank (ZMod 2) V := by
        rw [h, finrank_top]
      rw [finrank_span_singleton hx] at h2
      omega
  obtain ⟨ψ', y, -, hy, hψ', -, w, hw, hψ'w⟩ := exists_moving_transvection hgen hxinv
  have hψ'x : ψ' x = 1 := by
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hw
    rw [map_smul, smul_eq_mul] at hψ'w
    rcases zmod2_eq_zero_or_one r with rfl | rfl
    · rw [zero_mul] at hψ'w
      exact absurd hψ'w zero_ne_one
    · rwa [one_mul] at hψ'w
  have hK := isGInvariant_dualCoannihilator hgen hbound hdx hd hx hy hψ' hψ'x
  have hKbot : (centerForms G x ⊔ centerForms G y).dualCoannihilator = ⊥ := by
    rcases hirr _ hK with h | h
    · exact h
    · exfalso
      have hB : centerForms G x = ⊥ := by
        rw [eq_bot_iff]
        intro θ hθ
        rw [mem_bot]
        ext v
        exact (mem_dualCoannihilator v).mp (h ▸ mem_top) θ (mem_sup_left hθ)
      rw [hB, finrank_bot] at hdx
      omega
  obtain ⟨θ₁, hθ₁, hθ₁y⟩ := exists_centerForms_apply_eq_one hbound hdx (by omega) hx hy hψ' hψ'x
  have hdJ := le_finrank_inf_add_one hdx hψ' hψ'x hθ₁ hθ₁y
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (centerForms G x ⊔ centerForms G y)
  rw [hKbot, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (centerForms G x) (centerForms G y)
  have h3 := hmax y hy
  have hann : centerForms G x = (span (ZMod 2) {x}).dualAnnihilator := by
    apply Submodule.eq_of_le_of_finrank_eq
    · intro θ hθ
      rw [mem_dualAnnihilator]
      intro v hv
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
      rw [map_smul, (mem_centerForms.mp hθ).apply_eq_zero, smul_zero]
    · have := Subspace.finrank_add_finrank_dualAnnihilator_eq (span (ZMod 2) {x})
      rw [finrank_span_singleton hx] at this
      omega
  intro φ hφ
  have hmem : φ ∈ (span (ZMod 2) {x}).dualAnnihilator := by
    rw [mem_dualAnnihilator]
    intro v hv
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
    rw [map_smul, hφ, smul_zero]
  rw [← hann] at hmem
  exact hmem

end Centre

theorem eq_top_of_dihedral (hgen : GenByTransvections G) (hirr : IsIrreducibleOn G)
    {φ ψ : Dual (ZMod 2) V} {a b : V} (ha : a ≠ 0) (hψ : ψ ≠ 0) (hφa : InG G φ a)
    (hψb : InG G ψ b) (hφb : φ b = 1) (hψa : ψ a = 0) : G = ⊤ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Nonempty {z : V // z ≠ 0} := ⟨⟨a, ha⟩⟩
  obtain ⟨⟨x, hx⟩, hxmax⟩ :=
    Finite.exists_max fun z : {z : V // z ≠ 0} => finrank (ZMod 2) (centerForms G z.1)
  have hmax : ∀ z : V, z ≠ 0 → finrank (ZMod 2) (centerForms G z) ≤
      finrank (ZMod 2) (centerForms G x) := fun z hz => hxmax ⟨z, hz⟩
  have hbound : ThickBound G (finrank (ZMod 2) (centerForms G x)) := fun X J hXJ hX hJ => by
    obtain ⟨z, hz, hle⟩ := hXJ.exists_finrank_le hgen hirr hX hJ
    have := hmax z hz
    omega
  have hd : 2 ≤ finrank (ZMod 2) (centerForms G x) := by
    have hψa' : InG G ψ a := hφa.of_dihedral hψb hφb hψa
    have hφ0 : φ ≠ 0 := fun h => by
      rw [h, LinearMap.zero_apply] at hφb
      exact zero_ne_one hφb
    have hψφ : ψ ∉ span (ZMod 2) {φ} := fun hmem => by
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hmem
      have h0 := hψb.apply_eq_zero
      rw [LinearMap.smul_apply, hφb, smul_eq_mul, mul_one] at h0
      rw [h0, zero_smul] at hψ
      exact hψ rfl
    have hdim := finrank_sup_span_of_notMem hψφ
    rw [finrank_span_singleton hφ0] at hdim
    have hle : span (ZMod 2) {φ} ⊔ span (ZMod 2) {ψ} ≤ centerForms G a :=
      sup_le (span_le.mpr (Set.singleton_subset_iff.mpr hφa))
        (span_le.mpr (Set.singleton_subset_iff.mpr hψa'))
    have := Submodule.finrank_mono hle
    have := hmax a ha
    omega
  have hfull : x ∈ fullCentres G := forall_inG_of_maximal hgen hirr hbound hmax rfl hd hx
  have hF : fullCentres G = ⊤ := by
    rcases hirr _ isGInvariant_fullCentres with h | h
    · rw [h, mem_bot] at hfull
      exact absurd hfull hx
    · exact h
  refine eq_top_of_forall_inG fun θ v hθv => ?_
  have hv : v ∈ fullCentres G := hF ▸ mem_top
  exact hv θ hθv

end CFSG.ComponentClassification.OutcomeLocal
