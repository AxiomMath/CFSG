module

public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type*} [Group X]

@[expose] def uniqC (M : Subgroup X) (p : ℕ) : Set X :=
  {x | orderOf x = p ∧ x ∈ M ∧ centralizer ({x} : Set X) ≤ M}

@[expose] def uniqT (M : Subgroup X) (p : ℕ) [Fact p.Prime] : Set X :=
  {x | orderOf x = p ∧ x ∈ M ∧ ∃ P : Sylow p ↥M,
    x ∈ (P : Subgroup ↥M).map M.subtype ∧
      ControlsFusionOf M ((P : Subgroup ↥M).map M.subtype) {x}}

@[expose] def uniqU (M : Subgroup X) (p : ℕ) [Fact p.Prime] : Set X :=
  uniqC M p ∩ uniqT M p

@[expose] def IsUniqueSubgroup (M A : Subgroup X) : Prop :=
  A ≤ M ∧ ∀ g : X, conjugate A g ≤ M → g ∈ M

theorem mem_conjugate_iff {A : Subgroup X} {g x : X} :
    x ∈ conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  simp only [conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem IsUniqueSubgroup.normalizer_le {M W Y : Subgroup X} (hW : IsUniqueSubgroup M W)
    (hWY : W ≤ Y) (hYM : Y ≤ M) : normalizer (Y : Set X) ≤ M := by
  intro g hg
  refine hW.2 g fun x hx => ?_
  have h1 : g * x * g⁻¹ ∈ W := mem_conjugate_iff.mp hx
  exact hYM (((Subgroup.mem_normalizer_iff.mp hg) x).mpr (hWY h1))

theorem IsUniqueSubgroup.le_of_isPGroup [Finite X] {M W R : Subgroup X} (p : ℕ) [Fact p.Prime]
    (hW : IsUniqueSubgroup M W) (hWR : W ≤ R) (hR : IsPGroup p R) : R ≤ M := by
  by_contra hRM
  set R₀ : Subgroup X := R ⊓ M with hR₀
  have hWR₀ : W ≤ R₀ := le_inf hWR hW.1
  have hlt : R₀.subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hRM ?_
    intro r hr
    have : (⟨r, hr⟩ : R) ∈ R₀.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp this).2
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨r, hrN, hrR₀⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hrX : (r : X) ∈ normalizer (R₀ : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hrN) ⟨x, hx.1⟩
      exact h1.mp hx
    · intro hx
      have hxR : x ∈ R := by
        have hrx : (r : X) * x * (r : X)⁻¹ ∈ R := hx.1
        have : (r : X)⁻¹ * ((r : X) * x * (r : X)⁻¹) * (r : X) ∈ R :=
          R.mul_mem (R.mul_mem (R.inv_mem r.2) hrx) r.2
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.mp hrN) ⟨x, hxR⟩
      exact (h1.mpr hx : (⟨x, hxR⟩ : R) ∈ R₀.subgroupOf R)
  have hrM : (r : X) ∈ M := hW.normalizer_le hWR₀ inf_le_right hrX
  exact hrR₀ (Subgroup.mem_inf.mpr ⟨r.2, hrM⟩)

section Finite

variable [Finite X]

omit [Finite X] in
theorem exists_sylow_mem_map {M : Subgroup X} (p : ℕ) [Fact p.Prime] {x : X} (hx : x ∈ M)
    (hord : orderOf x = p) : ∃ P : Sylow p ↥M, x ∈ (P : Subgroup ↥M).map M.subtype := by
  have hpg : IsPGroup p (Subgroup.zpowers (⟨x, hx⟩ : M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one]
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  refine ⟨P, ⟨⟨x, hx⟩, hP (Subgroup.mem_zpowers _), rfl⟩⟩

omit [Finite X] in
theorem mem_map_smul {M : Subgroup X} {p : ℕ} [Fact p.Prime] (P : Sylow p ↥M) (h : M) {y : X}
    (hy : y ∈ (P : Subgroup ↥M).map M.subtype) :
    (h : X) * y * (h : X)⁻¹ ∈ ((h • P : Sylow p ↥M) : Subgroup ↥M).map M.subtype := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨h * y' * h⁻¹, ?_, by simp⟩
  show h * y' * h⁻¹ ∈ ((h • P : Sylow p ↥M) : Subgroup ↥M)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨y', hy', by simp [MulAut.smul_def]⟩

end Finite


section Finite2

variable [Finite X]

omit [Finite X] in
theorem isUniqueSubgroup_zpowers {M : Subgroup X} {x : X} (hxM : x ∈ M)
    (h : ∀ g : X, g⁻¹ * x * g ∈ M → g ∈ M) : IsUniqueSubgroup M (Subgroup.zpowers x) := by
  refine ⟨(Subgroup.zpowers_le).mpr hxM, fun g hg => h g ?_⟩
  have := hg (show g⁻¹ * x * g ∈ conjugate (Subgroup.zpowers x) g from ?_)
  · exact this
  · rw [mem_conjugate_iff, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact Subgroup.mem_zpowers x

end Finite2


section Main

variable [Finite X]

omit [Finite X] in
theorem conjSet_singleton (x g : X) : conjSet ({x} : Set X) g = {g⁻¹ * x * g} := by
  simp [conjSet]

omit [Finite X] in
theorem controlsFusionOf_singleton_iff {M P : Subgroup X} {x : X} :
    ControlsFusionOf M P {x} ↔
      ∀ y ∈ P, (∃ g : X, g⁻¹ * x * g = y) → ∃ m ∈ M, m⁻¹ * x * m = y := by
  constructor
  · intro h y hy ⟨g, hg⟩
    obtain ⟨m, hm, hmeq⟩ := h {y} (by simpa using hy) ⟨g, by rw [conjSet_singleton, hg]⟩
    rw [conjSet_singleton] at hmeq
    exact ⟨m, hm, Set.singleton_eq_singleton_iff.mp hmeq⟩
  · intro h B hB ⟨g, hg⟩
    rw [conjSet_singleton] at hg
    subst hg
    have hy : g⁻¹ * x * g ∈ P := by simpa using hB
    obtain ⟨m, hm, hmeq⟩ := h _ hy ⟨g, rfl⟩
    exact ⟨m, hm, by rw [conjSet_singleton, hmeq]⟩

theorem mem_uniqU_iff (p : ℕ) [Fact p.Prime] {M : Subgroup X} {x : X} :
    x ∈ uniqU M p ↔ orderOf x = p ∧ x ∈ M ∧ ∀ g : X, g⁻¹ * x * g ∈ M → g ∈ M := by
  constructor
  · rintro ⟨⟨hord, hxM, hC⟩, -, -, P, hxP, hctrl⟩
    refine ⟨hord, hxM, fun g hg => ?_⟩
    have hyord : orderOf (g⁻¹ * x * g) = p := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
      simpa [hord] using this
    obtain ⟨P₂, hyP₂⟩ := exists_sylow_mem_map p hg hyord
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M P₂ P
    have hmem := mem_map_smul P₂ h hyP₂
    rw [hh] at hmem
    rw [controlsFusionOf_singleton_iff] at hctrl
    obtain ⟨m, hmM, hm⟩ := hctrl _ hmem ⟨g * (h : X)⁻¹, by group⟩
    have key : m⁻¹ * x = (h : X) * (g⁻¹ * x * g) * (h : X)⁻¹ * m⁻¹ := by
      rw [← hm]; group
    have hc : g * (h : X)⁻¹ * m⁻¹ ∈ centralizer ({x} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * (h : X)⁻¹ * m⁻¹ * x = g * (h : X)⁻¹ * (m⁻¹ * x) := by group
        _ = g * (h : X)⁻¹ * ((h : X) * (g⁻¹ * x * g) * (h : X)⁻¹ * m⁻¹) := by rw [key]
        _ = x * (g * (h : X)⁻¹ * m⁻¹) := by group
    have hcM := hC hc
    have hg' : g = (g * (h : X)⁻¹ * m⁻¹) * m * (h : X) := by group
    rw [hg']
    exact M.mul_mem (M.mul_mem hcM hmM) h.2
  · rintro ⟨hord, hxM, hU⟩
    refine ⟨⟨hord, hxM, fun c hc => ?_⟩, hord, hxM, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hc
      apply hU c
      have : c⁻¹ * x * c = x := by
        rw [mul_assoc, ← hc]
        group
      rwa [this]
    · obtain ⟨P, hxP⟩ := exists_sylow_mem_map p hxM hord
      refine ⟨P, hxP, ?_⟩
      rw [controlsFusionOf_singleton_iff]
      rintro y hy ⟨g, rfl⟩
      have hyM : g⁻¹ * x * g ∈ M := by
        obtain ⟨y', -, hy'⟩ := hy
        rw [← hy']
        exact y'.2
      exact ⟨g, hU g hyM, rfl⟩

end Main

section Lemmas

variable [Finite X]

theorem uniqC_eq_uniqU_of_controlsFusion (p : ℕ) [Fact p.Prime] {M : Subgroup X} (P : Sylow p ↥M)
    (hP : ControlsFusion M ((P : Subgroup ↥M).map M.subtype)) : uniqC M p = uniqU M p := by
  ext x
  constructor
  · intro hx
    refine ⟨hx, hx.1, hx.2.1, ?_⟩
    obtain ⟨P', hxP'⟩ := exists_sylow_mem_map p hx.2.1 hx.1
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M P' P
    refine ⟨P', hxP', ?_⟩
    rw [controlsFusionOf_singleton_iff]
    intro y hy ⟨g, hg⟩
    have hx0 := mem_map_smul P' h hxP'
    have hy0 := mem_map_smul P' h hy
    rw [hh] at hx0 hy0
    have hctrl := controlsFusionOf_singleton_iff.mp (hP {(h : X) * x * (h : X)⁻¹}
      (Set.singleton_subset_iff.mpr hx0)) _ hy0 ⟨(h : X) * g * (h : X)⁻¹, by rw [← hg]; group⟩
    obtain ⟨m₀, hm₀, hm⟩ := hctrl
    refine ⟨(h : X)⁻¹ * m₀ * (h : X), M.mul_mem (M.mul_mem (M.inv_mem h.2) hm₀) h.2, ?_⟩
    have : (h : X)⁻¹ * ((h : X) * y * (h : X)⁻¹) * (h : X) = y := by group
    rw [← this, ← hm]
    group
  · exact fun hx => hx.1

theorem IsUniqueSubgroup.exists_sylow_le {M W H : Subgroup X} (p : ℕ) [Fact p.Prime]
    (hW : IsUniqueSubgroup M W) (hWH : W ≤ H) (hWp : IsPGroup p W) :
    ∃ R : Sylow p ↥H, W ≤ (R : Subgroup ↥H).map H.subtype ∧
      (R : Subgroup ↥H).map H.subtype ≤ M := by
  have hWH' : IsPGroup p (W.subgroupOf H) :=
    hWp.of_surjective (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWH).symm.surjective
  obtain ⟨R, hR⟩ := hWH'.exists_le_sylow
  have hWR : W ≤ (R : Subgroup ↥H).map H.subtype := by
    intro w hw
    exact ⟨⟨w, hWH hw⟩, hR hw, rfl⟩
  have hRp : IsPGroup p ((R : Subgroup ↥H).map H.subtype) := R.isPGroup'.map H.subtype
  exact ⟨R, hWR, hW.le_of_isPGroup p hWR hRp⟩

theorem IsUniqueSubgroup.exists_sylow_normalizer_le {M W : Subgroup X} (p : ℕ) [Fact p.Prime]
    (hW : IsUniqueSubgroup M W) (hWp : IsPGroup p W) :
    ∃ P : Sylow p X, normalizer (P : Set X) ≤ M := by
  obtain ⟨P, hWP⟩ := hWp.exists_le_sylow
  have hPM : (P : Subgroup X) ≤ M := hW.le_of_isPGroup p hWP P.isPGroup'
  exact ⟨P, hW.normalizer_le hWP hPM⟩

omit [Finite X] in
theorem IsUniqueSubgroup.mem_of_le_centralizer_conj {M W : Subgroup X} {p : ℕ} {x : X}
    (hx : x ∈ uniqC M p) (hW : IsUniqueSubgroup M W) {g : X}
    (hWg : W ≤ centralizer ({g⁻¹ * x * g} : Set X)) : g ∈ M := by
  have hconj : conjugate W g⁻¹ ≤ M := by
    intro y hy
    rw [mem_conjugate_iff, inv_inv] at hy
    have hyc : y ∈ centralizer ({x} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hWg hy)
      calc y * x = g * (g⁻¹ * y * g) * g⁻¹ * x := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = x * y := by group
    exact hx.2.2 hyc
  have := hW.2 g⁻¹ hconj
  simpa using this

end Lemmas

end CFSG.GH74.Uniqueness
