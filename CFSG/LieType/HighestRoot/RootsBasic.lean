module

public import CFSG.LieType.HighestRoot.Defs
public import CFSG.ClassicalInvolution.ModelFacts.RootLength

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
open CFSG.ClassicalInvolution.ModelFacts (IsIrreducible)

section Cartan

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

@[expose] def IsDominant (r : I → ℤ) : Prop :=
  ∀ i, 0 ≤ form hA (toRat (Pi.single i 1)) (toRat r)

theorem form_single_eq_coroot (i : I) (v : I → ℤ) :
    form hA (toRat (Pi.single i 1)) (toRat v) = symmetrizer hA i * (coroot A i v : ℚ) := by
  rw [toRat_single, form_single_left, coroot_apply]
  push_cast
  simp [toRat_apply]

theorem form_eq_sum_single (x v : I → ℤ) :
    form hA (toRat v) (toRat x) = ∑ l, (v l : ℚ) * form hA (toRat (Pi.single l 1)) (toRat x) := by
  rw [form_comm, form_eq_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [toRat_apply, form_comm hA (toRat x), toRat_single]

theorem form_nonneg_of_nonneg {r δ : I → ℤ} (hr : IsDominant hA r) (hδ : 0 ≤ δ) :
    0 ≤ form hA (toRat δ) (toRat r) := by
  rw [form_eq_sum_single]
  exact Finset.sum_nonneg fun l _ => mul_nonneg (by exact_mod_cast hδ l) (hr l)

theorem form_nonpos_of_nonpos {r δ : I → ℤ} (hr : IsDominant hA r) (hδ : δ ≤ 0) :
    form hA (toRat δ) (toRat r) ≤ 0 := by
  rw [form_eq_sum_single]
  exact Finset.sum_nonpos fun l _ =>
    mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hδ l) (hr l)

theorem exists_form_single_pos {r : I → ℤ} (hr : IsDominant hA r) (hr0 : r ≠ 0) :
    ∃ i, 0 < form hA (toRat (Pi.single i 1)) (toRat r) := by
  by_contra h
  push Not at h
  have hrr : form hA (toRat r) (toRat r) = 0 := by
    rw [form_eq_sum_single]
    exact Finset.sum_eq_zero fun l _ => by rw [le_antisymm (h l) (hr l), mul_zero]
  have hr0' : toRat r ≠ 0 := fun e => hr0 (toRat_injective (by rw [e, map_zero]))
  exact (form_pos hA hr0').ne' hrr

theorem form_pos_of_pos {r β : I → ℤ} (hr : IsDominant hA r) (hr0 : r ≠ 0)
    (hβ : ∀ j, 0 < β j) : 0 < form hA (toRat β) (toRat r) := by
  obtain ⟨i, hi⟩ := exists_form_single_pos hA hr hr0
  rw [form_eq_sum_single]
  have hnn : ∀ l ∈ Finset.univ,
      0 ≤ (β l : ℚ) * form hA (toRat (Pi.single l 1)) (toRat r) := fun l _ =>
    mul_nonneg (by exact_mod_cast (hβ l).le) (hr l)
  exact lt_of_lt_of_le (mul_pos (by exact_mod_cast hβ i) hi)
    (Finset.single_le_sum hnn (Finset.mem_univ i))

theorem pos_of_isDominant (hirr : IsIrreducible A) {δ : I → ℤ} (hd : IsDominant hA δ)
    (h0 : 0 ≤ δ) (hne : δ ≠ 0) (j : I) : 0 < δ j := by
  have hS : ({i | 0 < δ i} : Set I).Nonempty := by
    by_contra h
    refine hne (funext fun i => le_antisymm (not_lt.1 fun hi => h ⟨i, hi⟩) (h0 i))
  refine hirr {i | 0 < δ i} hS (fun i hi k hik => ?_) j
  by_contra hk
  have hk0 : δ k = 0 := le_antisymm (not_lt.1 hk) (h0 k)
  have hki : k ≠ i := fun e => hk (e ▸ hi)
  have hAki : A k i < 0 := lt_of_le_of_ne (hA.apply_le_zero_of_ne hki)
    fun e => hik (hA.apply_eq_zero_iff.2 e)
  have hle : ∑ l, A k l * δ l ≤ A k i * δ i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have : ∑ l ∈ Finset.univ.erase i, A k l * δ l ≤ 0 := Finset.sum_nonpos fun l hl => by
      by_cases hlk : l = k
      · rw [hlk, hk0, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (hA.apply_le_zero_of_ne (Ne.symm hlk)) (h0 l)
    linarith
  have hc : coroot A k δ < 0 := by
    rw [coroot_apply]
    have : A k i * δ i < 0 := mul_neg_of_neg_of_pos hAki hi
    linarith
  have hdk := hd k
  rw [form_single_eq_coroot] at hdk
  have hc' : (coroot A k δ : ℚ) < 0 := by exact_mod_cast hc
  nlinarith [symmetrizer_pos hA k]

theorem nonneg_of_isDominant {D : Set I} {r : I → ℤ} (hrR : r ∈ roots hA D)
    (hr : IsDominant hA r) : 0 ≤ r := by
  rcases nonneg_or_nonpos hA D hrR with h | h
  · exact h
  · exfalso
    have hr0 : toRat r ≠ 0 := fun e =>
      ne_zero_of_mem_roots hA D hrR (toRat_injective (by rw [e, map_zero]))
    have := form_nonpos_of_nonpos hA hr h
    exact absurd (form_pos hA hr0) (not_lt.2 this)

theorem form_sub_self (δ r : I → ℤ) :
    form hA (toRat (δ - r)) (toRat (δ - r)) =
      form hA (toRat δ) (toRat δ) - 2 * form hA (toRat δ) (toRat r) +
        form hA (toRat r) (toRat r) := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [form_comm hA (toRat r) (toRat δ)]
  ring

variable {D : Set I}

theorem le_of_form_pos {r : I → ℤ} {w : (coxeterMatrix hA).Group} {i : I}
    (hrw : r = weylAction hA w (Pi.single i 1))
    (hl : ∀ δ ∈ roots hA D, form hA (toRat δ) (toRat δ) ≤ form hA (toRat r) (toRat r))
    (hr : IsDominant hA r) {δ : I → ℤ} (hδ : δ ∈ roots hA D)
    (hpos : 0 < form hA (toRat δ) (toRat r)) : δ ≤ r := by
  set c : ℤ := coroot A i (weylAction hA w⁻¹ δ) with hc
  have hcr : (c : ℚ) * form hA (toRat r) (toRat r) = 2 * form hA (toRat r) (toRat δ) := by
    rw [hrw]
    exact OfCartan.coroot_mul_form_self hA w i δ
  have hs : weylAction hA (w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹) δ =
      δ - c • r := by
    rw [hrw]
    exact OfCartan.weylAction_conj_simple hA w i δ
  have hr0 : toRat r ≠ 0 := by
    rw [hrw]
    exact OfCartan.toRat_weylAction_single_ne_zero hA w i
  have hrr : 0 < form hA (toRat r) (toRat r) := form_pos hA hr0
  have hrδ : form hA (toRat r) (toRat δ) = form hA (toRat δ) (toRat r) := form_comm hA _ _
  have hδδ := hl δ hδ
  have hc1 : 0 < c := by
    have : (0 : ℚ) < c := by
      by_contra h
      push Not at h
      nlinarith
    exact_mod_cast this
  have hcs := sq_form_le hA (toRat r) (toRat δ)
  have hle : form hA (toRat r) (toRat δ) ≤ form hA (toRat r) (toRat r) := by nlinarith
  have hc2 : c ≤ 2 := by
    have : (c : ℚ) ≤ 2 := by nlinarith
    exact_mod_cast this
  rcases (by omega : c = 1 ∨ c = 2) with h1 | h2
  ·
    rw [h1, one_smul] at hs
    have hmem : δ - r ∈ roots hA D := hs ▸ weylAction_mem_roots hA _ hδ
    rcases nonneg_or_nonpos hA D hmem with hnn | hnp
    · exfalso
      have hne : toRat (δ - r) ≠ 0 := fun e =>
        ne_zero_of_mem_roots hA D hmem (toRat_injective (by rw [e, map_zero]))
      have h3 := form_pos hA hne
      have h4 := form_nonneg_of_nonneg hA hr hnn
      have e : form hA (toRat (δ - r)) (toRat r) =
          form hA (toRat δ) (toRat r) - form hA (toRat r) (toRat r) := by
        simp only [map_sub, LinearMap.sub_apply]
      rw [form_sub_self] at h3
      linarith
    · exact sub_nonpos.1 hnp
  ·
    rw [h2] at hcr
    push_cast at hcr
    have h3 := form_sub_self hA δ r
    have h4 : form hA (toRat (δ - r)) (toRat (δ - r)) ≤ 0 := by rw [h3]; linarith
    have h5 : toRat (δ - r) = 0 := by
      by_contra hne
      exact absurd (form_pos hA hne) (not_lt.2 h4)
    have h6 : δ - r = 0 := toRat_injective (by rw [h5, map_zero])
    rw [sub_eq_zero.1 h6]

theorem weylAction_simple_eq (k : I) (β : I → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple k) β =
      β - coroot A k β • Pi.single k 1 := by
  rw [weylAction_simple, reflection_apply_coroot]

theorem ht_sub_smul_single (β : I → ℤ) (c : ℤ) (k : I) :
    ht (β - c • (Pi.single k 1 : I → ℤ)) = ht β - c := by
  simp [ht, Finset.sum_sub_distrib, Pi.single_apply]

theorem isDominant_of_ht_le {β : I → ℤ}
    (h : ∀ k, ht (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple k) β) ≤ ht β) :
    IsDominant hA β := by
  intro k
  by_contra hneg
  push Not at hneg
  rw [form_single_eq_coroot] at hneg
  have hc : coroot A k β < 0 := by
    have : (coroot A k β : ℚ) < 0 := by
      by_contra h'
      push Not at h'
      nlinarith [symmetrizer_pos hA k]
    exact_mod_cast this
  have h1 := h k
  rw [weylAction_simple_eq, ht_sub_smul_single] at h1
  omega

theorem isDominant_of_max {δ β : I → ℤ} (hβ : β ∈ roots hA D) (hδβ : δ ≤ β)
    (hmax : ∀ γ ∈ roots hA D, δ ≤ γ → ht γ ≤ ht β) : IsDominant hA β := by
  refine isDominant_of_ht_le hA fun k => ?_
  have hmem := weylAction_mem_roots hA ((coxeterMatrix hA).toCoxeterSystem.simple k) hβ
  rw [weylAction_simple_eq] at hmem ⊢
  rw [ht_sub_smul_single]
  by_cases hc : coroot A k β < 0
  · have hle : δ ≤ β - coroot A k β • Pi.single k 1 := by
      intro j
      have : δ j ≤ β j := hδβ j
      by_cases hj : j = k
      · subst hj
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        omega
      · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero,
          sub_zero]
        exact this
    have h1 := hmax _ hmem hle
    rw [ht_sub_smul_single] at h1
    exact h1
  · omega

theorem le_of_nonneg (hirr : IsIrreducible A) {r : I → ℤ} {w : (coxeterMatrix hA).Group} {i : I}
    (hrw : r = weylAction hA w (Pi.single i 1))
    (hl : ∀ δ ∈ roots hA D, form hA (toRat δ) (toRat δ) ≤ form hA (toRat r) (toRat r))
    (hr : IsDominant hA r) {δ : I → ℤ} (hδ : δ ∈ roots hA D) (h0 : 0 ≤ δ) : δ ≤ r := by
  have hfin : {β | β ∈ roots hA D ∧ δ ≤ β}.Finite :=
    (finite_roots hA D).subset fun β hβ => hβ.1
  obtain ⟨β, ⟨hβR, hδβ⟩, hmax⟩ := Set.exists_max_image _ ht hfin ⟨δ, hδ, le_rfl⟩
  have hdom := isDominant_of_max hA hβR hδβ fun γ hγ hδγ => hmax γ ⟨hγ, hδγ⟩
  have hβ0 : 0 ≤ β := h0.trans hδβ
  have hβne := ne_zero_of_mem_roots hA D hβR
  have hfull := pos_of_isDominant hA hirr hdom hβ0 hβne
  have hrR : r ∈ roots hA D := Or.inl ⟨w, i, hrw⟩
  have hr0 := ne_zero_of_mem_roots hA D hrR
  exact hδβ.trans (le_of_form_pos hA hrw hl hr hβR (form_pos_of_pos hA hr hr0 hfull))

end Cartan

section Datum

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

theorem isHighestRoot_of_isDominant (hirr : IsIrreducible D.cartan) {r : Fin D.rank → ℤ}
    {w : (coxeterMatrix D.isFiniteType).Group} {i : Fin D.rank}
    (hrw : r = weylAction D.isFiniteType w (Pi.single i 1))
    (hl : ∀ δ ∈ D.roots, rootForm D δ δ ≤ rootForm D r r)
    (hr : ∀ j : Fin D.rank, 0 ≤ rootForm D (Pi.single j 1) r) : IsHighestRoot D r where
  mem_roots := Or.inl ⟨w, i, hrw⟩
  longest := hl
  height_le δ hδ := by
    have hr' : IsDominant D.isFiniteType r := hr
    have hr0 : 0 ≤ r :=
      nonneg_of_isDominant D.isFiniteType (D := D.divisible) (Or.inl ⟨w, i, hrw⟩) hr'
    simp only [ht]
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hδ with h | h
    · have hle := le_of_nonneg D.isFiniteType hirr hrw hl hr' hδ h
      exact Finset.sum_le_sum fun j _ => hle j
    · have h1 : ∑ j, δ j ≤ 0 := Finset.sum_nonpos fun j _ => h j
      have h2 : 0 ≤ ∑ j, r j := Finset.sum_nonneg fun j _ => hr0 j
      linarith
  dominant := hr

theorem IsHighestRoot.isLongestRoot {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) :
    CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot D r :=
  ⟨hr.mem_roots, hr.longest⟩

theorem exists_isHighestRoot (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    (hrank : 0 < D.rank) : ∃ r, IsHighestRoot D r := by
  have : Nonempty (Fin D.rank) := ⟨⟨0, hrank⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (symmetrizer D.isFiniteType)
  set O : Set (Fin D.rank → ℤ) :=
    Set.range fun w : (coxeterMatrix D.isFiniteType).Group =>
      weylAction D.isFiniteType w (Pi.single j 1) with hO
  have hOfin : O.Finite := (finite_roots D.isFiniteType D.divisible).subset (by
    rintro _ ⟨w, rfl⟩
    exact Or.inl ⟨w, j, rfl⟩)
  obtain ⟨r, ⟨w, rfl⟩, hmax⟩ := Set.exists_max_image O ht hOfin ⟨_, ⟨1, rfl⟩⟩
  refine ⟨_, isHighestRoot_of_isDominant D hirr (w := w) (i := j) rfl ?_ ?_⟩
  · intro δ hδ
    rcases hδ with ⟨w', k, rfl⟩ | ⟨w', k, hk, rfl⟩
    · simp only [rootForm]
      rw [form_weylAction, form_weylAction]
      simp only [toRat_single, form_single_single]
      linarith [hj k]
    · rw [hdiv] at hk
      exact absurd hk (Set.notMem_empty k)
  · exact isDominant_of_ht_le D.isFiniteType fun k =>
      hmax _ ⟨(coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k * w, by
        simp only [weylAction_mul_apply]⟩

end Datum

end CFSG.LieType.HighestRoot
