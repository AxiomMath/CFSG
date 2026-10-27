module

public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Statement
import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerForm

public section

namespace CFSG.GroupTheory.GomiLeviExc

open CFSG.LieType.Steinberg
open CFSG.Timmesfeld.ARS
open scoped Matrix

private theorem cartanForm_zsmul {I : Type} [Fintype I] (A : Matrix I I ℤ) (a : ℤ)
    (u : I → ℤ) : cartanForm A (a • u) = a ^ 2 * cartanForm A u := by
  simp only [cartanForm, Pi.smul_apply, smul_eq_mul, map_zsmul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

private theorem cartanForm_zsmul_add_zsmul {I : Type} [Fintype I] {A : Matrix I I ℤ}
    (hsymm : ∀ i j, A i j = A j i) (a b : ℤ) (u v : I → ℤ) :
    cartanForm A (a • u + b • v) =
      a ^ 2 * cartanForm A u + b ^ 2 * cartanForm A v + 2 * a * b * cartanPair A u v := by
  rw [cartanForm_add hsymm, cartanForm_zsmul, cartanForm_zsmul,
    CFSG.StandardType.ggRootKer_cartanPair_smul_left,
    CFSG.StandardType.ggRootKer_cartanPair_smul_right]
  ring

private theorem symmetrized_apply {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (i j : I) :
    CFSG.LieType.RootSystem.symmetrized hA i j =
      CFSG.LieType.RootSystem.symmetrizer hA i * (A i j : ℚ) := by
  have h1 : CFSG.LieType.RootSystem.form hA (Pi.single i 1) (Pi.single j 1) =
      CFSG.LieType.RootSystem.symmetrized hA i j := by
    rw [CFSG.LieType.RootSystem.form_apply, single_dotProduct, one_mul, Matrix.mulVec]
    simp
  have h2 : CFSG.LieType.RootSystem.form hA (Pi.single i 1) (Pi.single j 1) =
      CFSG.LieType.RootSystem.symmetrizer hA i * (A i j : ℚ) := by
    rw [CFSG.LieType.RootSystem.form_single_left, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← h1, h2]

private theorem eq_zero_of_symmetrizer_ne {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hsym : A.IsSymm) {i j : I}
    (hij : CFSG.LieType.RootSystem.symmetrizer hA i ≠
      CFSG.LieType.RootSystem.symmetrizer hA j) : A i j = 0 := by
  have hsymm : ∀ a b, A a b = A b a := fun a b => hsym.apply b a
  have hpd : (CFSG.LieType.RootSystem.symmetrized hA).PosDef :=
    CFSG.LieType.RootSystem.posDef_symmetrized hA
  have hentry : CFSG.LieType.RootSystem.symmetrizer hA i * (A i j : ℚ) =
      CFSG.LieType.RootSystem.symmetrizer hA j * (A i j : ℚ) := by
    have h := hpd.isHermitian.apply i j
    have h1 := symmetrized_apply (A := A) hA i j
    have h2 := symmetrized_apply (A := A) hA j i
    rw [h1, h2, hsymm j i] at h
    simpa only [star_trivial] using h.symm
  have hdiff : CFSG.LieType.RootSystem.symmetrizer hA i -
      CFSG.LieType.RootSystem.symmetrizer hA j ≠ 0 := sub_ne_zero.mpr hij
  have hz : (A i j : ℚ) = 0 := by
    have h : (CFSG.LieType.RootSystem.symmetrizer hA i -
        CFSG.LieType.RootSystem.symmetrizer hA j) * (A i j : ℚ) = 0 := by
      rw [sub_mul, hentry, sub_self]
    exact (mul_eq_zero.mp h).resolve_left hdiff
  exact_mod_cast hz

private theorem mulVec_level {I : Type} [Fintype I] (d : I → ℚ) (A : Matrix I I ℤ)
    (N : Matrix I I ℚ) (x : I → ℚ) (c : ℚ)
    (hN : ∀ i j, N i j = d i * (A i j : ℚ))
    (hvan : ∀ i j, d i ≠ d j → A i j = 0) {i : I} (hi : d i = c) :
    (N *ᵥ fun j => if d j = c then x j else 0) i =
      d i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i := by
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, hN i j]
  by_cases hdj : d j = c
  · rw [if_pos hdj]
    ring_nf
  · have hne : d j ≠ d i := by rw [hi]; exact hdj
    rw [if_neg hdj, hvan i j (Ne.symm hne)]
    simp

private theorem sum_level_eq {I : Type} [Fintype I] (d : I → ℚ) (A : Matrix I I ℤ)
    (N : Matrix I I ℚ) (x : I → ℚ) {c : ℚ} (hc : c ≠ 0)
    (hN : ∀ i j, N i j = d i * (A i j : ℚ))
    (hvan : ∀ i j, d i ≠ d j → A i j = 0) :
    ∑ i ∈ Finset.univ.filter (fun i => d i = c),
        x i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i =
      (1 / c) * ((fun i => if d i = c then x i else 0) ⬝ᵥ
        (N *ᵥ fun i => if d i = c then x i else 0)) := by
  have hpoint : ∀ i ∈ Finset.univ.filter (fun i => d i = c),
      x i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i =
        (1 / c) * ((if d i = c then x i else 0) *
          (N *ᵥ fun j => if d j = c then x j else 0) i) := by
    intro i hi
    have hdi : d i = c := (Finset.mem_filter.mp hi).2
    rw [mulVec_level d A N x c hN hvan hdi, if_pos hdi, hdi]
    field_simp [hc]
  calc ∑ i ∈ Finset.univ.filter (fun i => d i = c),
          x i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i
      = ∑ i ∈ Finset.univ.filter (fun i => d i = c),
          (1 / c) * ((if d i = c then x i else 0) *
            (N *ᵥ fun j => if d j = c then x j else 0) i) :=
        Finset.sum_congr rfl hpoint
    _ = (1 / c) * ∑ i ∈ Finset.univ.filter (fun i => d i = c),
          (if d i = c then x i else 0) *
            (N *ᵥ fun j => if d j = c then x j else 0) i := by
        rw [← Finset.mul_sum]
    _ = (1 / c) * ∑ i, (if d i = c then x i else 0) *
            (N *ᵥ fun j => if d j = c then x j else 0) i := by
        congr 1
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro i _ hi
        have hdi : d i ≠ c := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        rw [if_neg hdi, zero_mul]
    _ = (1 / c) * ((fun i => if d i = c then x i else 0) ⬝ᵥ
          (N *ᵥ fun i => if d i = c then x i else 0)) := rfl

private theorem posDef_map_intCast_of_isSymm {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hsym : A.IsSymm) :
    (A.map (Int.cast : ℤ → ℚ)).PosDef := by
  classical
  have hsymm : ∀ i j, A i j = A j i := fun i j => hsym.apply j i
  have hAqSymm : (A.map (Int.cast : ℤ → ℚ)).IsSymm :=
    Matrix.IsSymm.ext fun i j => by
      simp only [Matrix.map_apply]
      exact_mod_cast hsymm j i
  have hAqHerm : (A.map (Int.cast : ℤ → ℚ)).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr hAqSymm
  set d : I → ℚ := CFSG.LieType.RootSystem.symmetrizer hA with hd
  have hdpos : ∀ i, 0 < d i := CFSG.LieType.RootSystem.symmetrizer_pos hA
  set N : Matrix I I ℚ := CFSG.LieType.RootSystem.symmetrized hA with hN
  have hNpd : N.PosDef := by rw [hN]; exact CFSG.LieType.RootSystem.posDef_symmetrized hA
  have hNapply : ∀ i j, N i j = d i * (A i j : ℚ) := fun i j => by
    rw [hN]; exact symmetrized_apply hA i j
  have hvan : ∀ i j, d i ≠ d j → A i j = 0 := fun i j hij =>
    eq_zero_of_symmetrizer_ne hA hsym hij
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hAqHerm ?_
  intro x hx
  simp only [star_trivial]
  have hsplit := Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image d) (g := d)
    (f := fun i => x i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i)
    (fun i _ => Finset.mem_image_of_mem d (Finset.mem_univ i))
  rw [dotProduct, ← hsplit]
  refine Finset.sum_pos' ?_ ?_
  · intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    rw [sum_level_eq d A N x (hdpos i).ne' hNapply hvan]
    refine mul_nonneg (one_div_pos.mpr (hdpos i)).le ?_
    by_cases hxc : (fun j => if d j = d i then x j else 0) = 0
    · rw [hxc]
      simp
    · have h := hNpd.dotProduct_mulVec_pos hxc
      simpa only [star_trivial] using h.le
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    refine ⟨d i, Finset.mem_image_of_mem d (Finset.mem_univ i), ?_⟩
    rw [sum_level_eq d A N x (hdpos i).ne' hNapply hvan]
    refine mul_pos (one_div_pos.mpr (hdpos i)) ?_
    have hxc : (fun j => if d j = d i then x j else 0) ≠ 0 := by
      intro h
      exact hi (by simpa [h] using congrFun h i)
    have h := hNpd.dotProduct_mulVec_pos hxc
    simpa only [star_trivial] using h

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem expPairs_eq_of_isSymm (hsym : A.IsSymm) {α β : I → ℤ}
    (hα : α ∈ CFSG.LieType.RootSystem.roots hA ∅) (hβ : β ∈ CFSG.LieType.RootSystem.roots hA ∅)
    (hαβ : α + β ≠ 0) {p : ℕ × ℕ} (hp : p ∈ expPairs (RootSystem.ofCartan hA ∅) α β) :
    p = (1, 1) := by
  obtain ⟨i, j⟩ := p
  simp only [expPairs, Set.mem_ofPred_eq] at hp
  have hsymm : ∀ a b, A a b = A b a := fun a b => hsym.apply b a
  have hpd := posDef_map_intCast_of_isSymm hA hsym
  have hqα := cartanForm_eq_two hA hsymm hα
  have hqβ := cartanForm_eq_two hA hsymm hβ
  have hroot : (i : ℤ) • α + (j : ℤ) • β ∈ CFSG.LieType.RootSystem.roots hA ∅ := by
    simpa only [Nat.cast_smul_eq_nsmul, RootSystem.ofCartan_roots] using hp.2.2
  have hq := cartanForm_eq_two hA hsymm hroot
  rw [cartanForm_zsmul_add_zsmul hsymm, hqα, hqβ] at hq
  set m : ℤ := cartanPair A α β with hm
  have hq' : (i : ℤ) ^ 2 + (j : ℤ) ^ 2 + (i : ℤ) * (j : ℤ) * m = 1 := by linarith
  have hi1 : (1 : ℤ) ≤ i := by exact_mod_cast hp.1
  have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast hp.2.1
  have hi0 : (0 : ℤ) ≤ i := by linarith
  have hj0 : (0 : ℤ) ≤ j := by linarith
  have hi2 : (1 : ℤ) ≤ (i : ℤ) ^ 2 := by nlinarith [sq_nonneg ((i : ℤ) - 1)]
  have hj2 : (1 : ℤ) ≤ (j : ℤ) ^ 2 := by nlinarith [sq_nonneg ((j : ℤ) - 1)]
  have hml : -2 < m := by
    have hpos := cartanForm_pos hpd hαβ
    rw [cartanForm_add hsymm, hqα, hqβ] at hpos
    linarith
  have hm2 : m < 2 := by
    by_contra hnot
    have hmge : 2 ≤ m := by omega
    have hij1 : (1 : ℤ) ≤ (i : ℤ) * (j : ℤ) := by
      calc (1 : ℤ) = 1 * 1 := by norm_num
        _ ≤ (i : ℤ) * (j : ℤ) := mul_le_mul hi1 hj1 (by norm_num) (by norm_num)
    have hprod : 2 * ((i : ℤ) * (j : ℤ)) ≤ m * ((i : ℤ) * (j : ℤ)) :=
      mul_le_mul_of_nonneg_right hmge (by linarith)
    nlinarith
  interval_cases m
  · have hsq : 0 ≤ ((i : ℤ) - (j : ℤ)) ^ 2 := sq_nonneg _
    have hle : (i : ℤ) * (j : ℤ) ≤ 1 := by nlinarith
    have hge : (1 : ℤ) ≤ (i : ℤ) * (j : ℤ) := by
      calc (1 : ℤ) = 1 * 1 := by norm_num
        _ ≤ (i : ℤ) * (j : ℤ) := mul_le_mul hi1 hj1 (by norm_num) (by norm_num)
    have heq : (i : ℤ) * (j : ℤ) = 1 := le_antisymm hle hge
    have hi : i = 1 := by
      exact_mod_cast Int.eq_one_of_mul_eq_one_right hi0 heq
    have hj : j = 1 := by
      exact_mod_cast Int.eq_one_of_mul_eq_one_left hj0 heq
    simp [hi, hj]
  · nlinarith
  · nlinarith

end CFSG.GroupTheory.GomiLeviExc
