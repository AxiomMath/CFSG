module

public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

def IsOrthogonal {α : Type*} [Fintype α] (f h : α → ℂ) : Prop := cfInner f h = 0

theorem isOrthogonal_iff {α : Type*} [Fintype α] {f h : α → ℂ} :
    IsOrthogonal f h ↔ cfInner f h = 0 := Iff.rfl

def IsOrthonormalFamily {α : Type*} [Fintype α] {ι : Type*} [DecidableEq ι] (f : ι → α → ℂ) :
    Prop :=
  ∀ i j, cfInner (f i) (f j) = if i = j then 1 else 0

theorem isOrthonormalFamily_iff {α : Type*} [Fintype α] {ι : Type*} [DecidableEq ι]
    {f : ι → α → ℂ} :
    IsOrthonormalFamily f ↔ ∀ i j, cfInner (f i) (f j) = if i = j then 1 else 0 := Iff.rfl

theorem IsOrthonormalFamily.of_cfInner_eq_ite {α : Type*} [Fintype α] {ι : Type*}
    [DecidableEq ι] {f : ι → α → ℂ}
    (hf : ∀ i j, cfInner (f i) (f j) = if i = j then 1 else 0) : IsOrthonormalFamily f := hf

theorem IsOrthonormalFamily.cfInner_self {α : Type*} [Fintype α] {ι : Type*} [DecidableEq ι]
    {f : ι → α → ℂ} (hf : IsOrthonormalFamily f) (i : ι) : cfInner (f i) (f i) = 1 := by
  simpa using hf i i

theorem IsOrthonormalFamily.isOrthogonal {α : Type*} [Fintype α] {ι : Type*} [DecidableEq ι]
    {f : ι → α → ℂ} (hf : IsOrthonormalFamily f) {i j : ι} (hij : i ≠ j) :
    IsOrthogonal (f i) (f j) := by
  simpa [IsOrthogonal, hij] using hf i j

theorem IsOrthonormalFamily.of_cfInner_self_of_isOrthogonal {α : Type*} [Fintype α] {ι : Type*}
    [DecidableEq ι] {f : ι → α → ℂ} (hone : ∀ i, cfInner (f i) (f i) = 1)
    (horth : ∀ i j, i ≠ j → IsOrthogonal (f i) (f j)) : IsOrthonormalFamily f :=
  IsOrthonormalFamily.of_cfInner_eq_ite fun i j => by
    by_cases h : i = j
    · subst h; simp [hone i]
    · simp [h, isOrthogonal_iff.1 (horth i j h)]

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem inf_centralizer_eq_bot_iff {H : Subgroup K} {g : K} :
    H ⊓ Subgroup.centralizer {g} = ⊥ ↔ ∀ h ∈ H, h * g = g * h → h = 1 := by
  rw [Subgroup.eq_bot_iff_forall]
  constructor
  · intro h x hx hcomm
    exact h x (Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩)
  · intro h x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    exact h x hx1 (Subgroup.mem_centralizer_singleton_iff.1 hx2)

theorem exists_conj_eq_mul_of_inf_centralizer_eq_bot [Finite K] {H : Subgroup K} [H.Normal]
    {g : K} (hg : H ⊓ Subgroup.centralizer {g} = ⊥) {u : K} (hu : u ∈ H) :
    ∃ h ∈ H, u * g = h * g * h⁻¹ := by
  have hmem : ∀ h : H, (h : K) * g * (h : K)⁻¹ * g⁻¹ ∈ H := by
    intro h
    have h1 : g * (h : K)⁻¹ * g⁻¹ ∈ H := ‹H.Normal›.conj_mem _ (inv_mem h.2) g
    have h2 := H.mul_mem h.2 h1
    convert h2 using 1
    group
  set φ : H → H := fun h => ⟨(h : K) * g * (h : K)⁻¹ * g⁻¹, hmem h⟩ with hφ
  have hinj : Function.Injective φ := by
    intro h₁ h₂ h12
    have h1 : (h₁ : K) * g * (h₁ : K)⁻¹ * g⁻¹ = (h₂ : K) * g * (h₂ : K)⁻¹ * g⁻¹ :=
      congrArg Subtype.val h12
    have h2 : (h₁ : K) * g * (h₁ : K)⁻¹ = (h₂ : K) * g * (h₂ : K)⁻¹ := mul_right_cancel h1
    have hc : (h₂ : K)⁻¹ * (h₁ : K) * g = g * ((h₂ : K)⁻¹ * (h₁ : K)) := by
      calc (h₂ : K)⁻¹ * (h₁ : K) * g
          = (h₂ : K)⁻¹ * ((h₁ : K) * g * (h₁ : K)⁻¹) * (h₁ : K) := by group
        _ = (h₂ : K)⁻¹ * ((h₂ : K) * g * (h₂ : K)⁻¹) * (h₁ : K) := by rw [h2]
        _ = g * ((h₂ : K)⁻¹ * (h₁ : K)) := by group
    have h3 := inf_centralizer_eq_bot_iff.1 hg _ (H.mul_mem (inv_mem h₂.2) h₁.2) hc
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨u, hu⟩
  have hh' : (h : K) * g * (h : K)⁻¹ * g⁻¹ = u := congrArg Subtype.val hh
  exact ⟨h, h.2, by rw [← hh']; group⟩

theorem Representation.apply_mem_invariants_comp_subtype (ρ : Representation ℂ K V)
    {H : Subgroup K} [H.Normal] (g : K) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp H.subtype)) :
    ρ g v ∈ Representation.invariants (ρ.comp H.subtype) := by
  rw [Representation.mem_invariants] at hv ⊢
  intro h
  have hmem : g⁻¹ * (h : K) * g ∈ H := by
    simpa using ‹H.Normal›.conj_mem (h : K) h.2 g⁻¹
  have h1 : ρ (g⁻¹ * (h : K) * g) v = v := hv ⟨g⁻¹ * (h : K) * g, hmem⟩
  change ρ (h : K) (ρ g v) = ρ g v
  have h3 : ρ (h : K) (ρ g v) = ρ ((h : K) * g) v := by rw [map_mul]; rfl
  have h2 : (h : K) * g = g * (g⁻¹ * (h : K) * g) := by group
  rw [h3, h2, map_mul]
  change ρ g (ρ (g⁻¹ * (h : K) * g) v) = ρ g v
  rw [h1]

theorem Representation.sum_mem_invariants_comp_subtype (ρ : Representation ℂ K V)
    (H : Subgroup K) [Fintype H] (v : V) :
    (∑ h : H, ρ (h : K) v) ∈ Representation.invariants (ρ.comp H.subtype) := by
  rw [Representation.mem_invariants]
  intro h₀
  change ρ (h₀ : K) (∑ h : H, ρ (h : K) v) = _
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h₀) _ _ fun h => ?_
  change ρ (h₀ : K) (ρ (h : K) v) = ρ ((h₀ * h : H) : K) v
  rw [Subgroup.coe_mul, map_mul]
  rfl

theorem Representation.invariants_comp_subtype_eq_bot [Finite K] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ K V) (hρ : ρ.IsIrreducible) {H : Subgroup K} [H.Normal]
    (hH : ∃ h ∈ H, ρ.character h ≠ ρ.character 1) :
    Representation.invariants (ρ.comp H.subtype) = ⊥ := by
  set τ : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp H.subtype),
      fun g _ hv => Representation.apply_mem_invariants_comp_subtype ρ g hv⟩ with hτ
  rcases hρ.eq_bot_or_eq_top τ with h | h
  · exact congrArg Subrepresentation.toSubmodule h
  · obtain ⟨x, hx, hne⟩ := hH
    have htop : Representation.invariants (ρ.comp H.subtype) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    have hone : ρ x = 1 := by
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ Representation.invariants (ρ.comp H.subtype) := by rw [htop]; trivial
      simpa using (Representation.mem_invariants _ v).1 hv ⟨x, hx⟩
    exact absurd (((Representation.character_eq_finrank_iff_of_finite ρ).2 hone).trans
      (ρ.char_one).symm) hne

theorem Representation.character_eq_zero_of_inf_centralizer_eq_bot [Finite K]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) (hρ : ρ.IsIrreducible) {H : Subgroup K}
    [H.Normal] (hH : ∃ h ∈ H, ρ.character h ≠ ρ.character 1) {g : K}
    (hg : H ⊓ Subgroup.centralizer {g} = ⊥) : ρ.character g = 0 := by
  have hfin : Fintype H := Fintype.ofFinite H
  have hinv := Representation.invariants_comp_subtype_eq_bot ρ hρ hH
  have hzero : ∀ v : V, ∑ h : H, ρ (h : K) v = 0 := by
    intro v
    have h1 := Representation.sum_mem_invariants_comp_subtype ρ H v
    rw [hinv] at h1
    simpa using h1
  have hP : (∑ h : H, ρ ((h : K) * g)) = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.sum_apply]
    have h2 : ∀ h : H, ρ ((h : K) * g) v = ρ (h : K) (ρ g v) := fun h => by rw [map_mul]; rfl
    simp only [h2]
    simpa using hzero (ρ g v)
  have htr : ∑ h : H, ρ.character ((h : K) * g) = 0 := by
    have h3 := congrArg (LinearMap.trace ℂ V) hP
    rwa [map_sum, map_zero] at h3
  have hconj : ∀ h : H, h ∈ (Finset.univ : Finset H) →
      ρ.character ((h : K) * g) = ρ.character g := by
    intro h _
    obtain ⟨c, _, hc⟩ := exists_conj_eq_mul_of_inf_centralizer_eq_bot hg h.2
    rw [hc, ρ.char_conj]
  rw [Finset.sum_congr rfl hconj] at htr
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htr
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := H)
  exact (mul_eq_zero.1 htr).resolve_left hcard

theorem eq_zero_of_inf_centralizer_eq_bot [Finite K] {H : Subgroup K} [H.Normal] {χ : K → ℂ}
    (hχ : χ ∈ irrChar ℂ K) (hH : ¬ (H : Set K) ⊆ charValueKernel χ) {g : K}
    (hg : H ⊓ Subgroup.centralizer {g} = ⊥) : χ g = 0 := by
  obtain ⟨W, hW, rfl⟩ := mem_irrChar.1 hχ
  have hH' : ∃ h ∈ H, Representation.character W.ρ h ≠ Representation.character W.ρ 1 := by
    simp only [Set.subset_def, SetLike.mem_coe, mem_charValueKernel, not_forall] at hH
    obtain ⟨x, hx, hne⟩ := hH
    exact ⟨x, hx, hne⟩
  exact Representation.character_eq_zero_of_inf_centralizer_eq_bot W.ρ hW hH' hg

theorem eq_zero_of_forall_mem_centralizer [Finite K] {H : Subgroup K} [H.Normal] {χ : K → ℂ}
    (hχ : χ ∈ Irr K) (hH : ∃ h ∈ H, χ h ≠ χ 1) {g : K}
    (hg : ∀ h ∈ H, h * g = g * h → h = 1) : χ g = 0 :=
  eq_zero_of_inf_centralizer_eq_bot (mem_irrChar.2 (mem_Irr.1 hχ))
    (fun hsub => by
      obtain ⟨x, hx, hne⟩ := hH
      exact hne (mem_charValueKernel.1 (hsub (SetLike.mem_coe.2 hx))))
    (inf_centralizer_eq_bot_iff.2 hg)

end CFSG.FeitThompson
