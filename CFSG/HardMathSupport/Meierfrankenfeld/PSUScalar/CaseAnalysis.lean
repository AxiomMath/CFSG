module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WeylOrbitBounds
public import CFSG.LieType.SpecialLinear.ExteriorModel.OrbitCount
public import Mathlib.Data.Nat.Prime.Basic

public section

open Finset CFSG.LieType.SpecialLinear.ExteriorModel

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

@[expose] def movedTop {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n)) : ℕ :=
  ((Fintype.piFinset fun i => rearr (topWt (ε i))).filter
    fun μ => ∃ i, μ i ∘ Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ μ i).card

@[expose] def orbitSize {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  (rearr (topWt S)).card

@[expose] def movedOrbit {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) : ℕ :=
  ((rearr (topWt S)).filter fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩).card

@[expose] def fixedOrbit {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) : ℕ :=
  ((rearr (topWt S)).filter
    fun μ => μ ∘ Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ = μ).card

theorem comp_swap_eq_iff {n : ℕ} {z o : Fin n} (hzo : z ≠ o) (μ : Fin n → ℤ) :
    μ ∘ Equiv.swap z o = μ ↔ μ z = μ o := by
  constructor
  · intro h
    have h' := congrFun h z
    simp only [Function.comp_apply, Equiv.swap_apply_left] at h'
    exact h'.symm
  · intro h
    ext x
    by_cases hx : x = z
    · subst hx
      simp [Equiv.swap_apply_left, h]
    · by_cases hy : x = o
      · subst hy
        simp [Equiv.swap_apply_right, h]
      · have h1 : Equiv.swap z o x = x := Equiv.swap_apply_of_ne_of_ne hx hy
        simp [h1]

theorem comp_swap_zero_one_eq_iff {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → ℤ) :
    μ ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = μ ↔
      μ ⟨0, by omega⟩ = μ ⟨1, by omega⟩ :=
  comp_swap_eq_iff (Fin.ne_of_val_ne (by simp)) μ

theorem topWt_empty {n : ℕ} : topWt (∅ : Finset (Fin n)) = fun _ => (0 : ℤ) := by
  funext a
  simp [topWt]

theorem rearr_const {n : ℕ} (a : ℤ) :
    rearr (fun _ : Fin n => a) = {(fun _ : Fin n => a)} := by
  ext μ
  rw [mem_rearr, Finset.mem_singleton]
  constructor
  · rintro ⟨σ, rfl⟩
    funext x
    rfl
  · intro h
    exact ⟨1, by rw [h]; rfl⟩

theorem orbitSize_empty {n : ℕ} : orbitSize (∅ : Finset (Fin n)) = 1 := by
  rw [orbitSize, topWt_empty, rearr_const]
  exact Finset.card_singleton _

theorem fixedOrbit_empty {n : ℕ} (hn : 2 ≤ n) :
    fixedOrbit hn (∅ : Finset (Fin n)) = 1 := by
  classical
  rw [fixedOrbit, topWt_empty, rearr_const, Finset.filter_singleton]
  have h : (fun _ : Fin n => (0 : ℤ)) ∘
      Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) =
      (fun _ : Fin n => (0 : ℤ)) := by
    funext x
    rfl
  rw [if_pos h]
  exact Finset.card_singleton _

theorem movedOrbit_add_fixedOrbit {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) :
    movedOrbit hn S + fixedOrbit hn S = orbitSize S := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := rearr (topWt S))
    (p := fun μ : Fin n → ℤ =>
      μ ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = μ)
  have hnot : (rearr (topWt S)).filter (fun μ : Fin n → ℤ =>
      ¬ μ ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = μ) =
      (rearr (topWt S)).filter
        (fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩) := by
    apply Finset.filter_congr
    intro μ _
    rw [comp_swap_zero_one_eq_iff hn]
  rw [hnot] at h
  have h' : fixedOrbit hn S + movedOrbit hn S = orbitSize S := by
    simpa [movedOrbit, fixedOrbit, orbitSize] using h
  omega

theorem fixedOrbit_eq {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) :
    fixedOrbit hn S = orbitSize S - movedOrbit hn S := by
  have h := movedOrbit_add_fixedOrbit hn S
  omega

theorem n_le_orbitSize {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅) :
    n ≤ orbitSize S := by
  classical
  have hn0 : 0 < n := by omega
  by_cases h1 : S.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    rw [orbitSize, card_rearr_topWt_singleton]
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0
      rw [Finset.mem_singleton]
      exact Fin.ext h.symm
    exact le_choose (Nat.one_le_iff_ne_zero.mpr hj0) (by omega)
  · have h2 : 2 ≤ S.card := by
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    rw [orbitSize, card_rearr_topWt]
    have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
    have hsum := sum_blocks S
    have hl : 3 ≤ S.card + 1 := by omega
    have hN := multinomial_lower (b := blocks S) hb hsum hl
    calc n ≤ n * (n - 1) := by
          have h1' : 1 ≤ n - 1 := by omega
          calc n = n * 1 := (Nat.mul_one n).symm
            _ ≤ n * (n - 1) := Nat.mul_le_mul_left n h1'
      _ ≤ Nat.multinomial univ (blocks S) := hN

theorem two_mul_two_mul_sub_three_le_movedOrbit {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hS : 3 ≤ S.card + 1) :
    2 * (2 * n - 3) ≤ movedOrbit hn S := by
  classical
  have hn0 : 0 < n := by omega
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hkey := two_mul_mul_add_multinomial_le (b := blocks S) hb hsum hS
  set N := Nat.multinomial univ (blocks S) with hNdef
  set T := ∑ i, blocks S i ^ 2 with hTdef
  have hkey' : 2 * n * (n - 1) * (2 * n - 3) + N * T ≤ N * n ^ 2 := hkey
  have hmoved := card_moved_rearr_topWt S hn
  have hmoved' : movedOrbit hn S * (n * (n - 1)) = N * (n ^ 2 - T) := by
    simpa [movedOrbit, hNdef, hTdef] using hmoved
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Nat.multinomial_pos _ _
  have hA : 2 * n * (n - 1) * (2 * n - 3) ≤ N * (n ^ 2 - T) := by
    have h1 : 2 * n * (n - 1) * (2 * n - 3) ≤ N * n ^ 2 - N * T :=
      Nat.le_sub_of_add_le hkey'
    rwa [← Nat.mul_sub_left_distrib] at h1
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.le_of_mul_le_mul_right (c := n * (n - 1)) _ hpos
  rw [hmoved']
  calc 2 * (2 * n - 3) * (n * (n - 1)) = 2 * n * (n - 1) * (2 * n - 3) := by ring
    _ ≤ N * (n ^ 2 - T) := hA

theorem two_le_movedOrbit {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅) :
    2 ≤ movedOrbit hn S := by
  classical
  by_cases h1 : S.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0
      rw [Finset.mem_singleton]
      exact Fin.ext h.symm
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
    rw [movedOrbit, card_moved_rearr_topWt_singleton hn j hj1]
    have hpos : 0 < (n - 2).choose (j - 1) :=
      Nat.choose_pos (by omega)
    omega
  · have h2 : 2 ≤ S.card := by
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    have hM := two_mul_two_mul_sub_three_le_movedOrbit hn h0 (by omega : 3 ≤ S.card + 1)
    have : 2 * (2 * n - 3) = 4 * n - 6 := by omega
    omega

theorem orbitSize_singleton {n : ℕ} (j : Fin n) :
    orbitSize ({j} : Finset (Fin n)) = n.choose j :=
  card_rearr_topWt_singleton j

theorem movedOrbit_singleton {n : ℕ} (hn : 2 ≤ n) {j : Fin n} (hj : 1 ≤ (j : ℕ)) :
    movedOrbit hn ({j} : Finset (Fin n)) = 2 * (n - 2).choose (j - 1) :=
  card_moved_rearr_topWt_singleton hn j hj

theorem orbitSize_natural_left {n : ℕ} (hn : 2 ≤ n) :
    orbitSize ({(⟨1, by omega⟩ : Fin n)} : Finset (Fin n)) = n := by
  rw [orbitSize_singleton, Nat.choose_one_right]

theorem orbitSize_natural_right {n : ℕ} (hn : 2 ≤ n) :
    orbitSize ({(⟨n - 1, by omega⟩ : Fin n)} : Finset (Fin n)) = n := by
  rw [orbitSize_singleton]
  show n.choose (n - 1) = n
  rw [Nat.choose_symm (k := 1) (by omega : 1 ≤ n), Nat.choose_one_right]

theorem movedOrbit_natural_left {n : ℕ} (hn : 2 ≤ n) :
    movedOrbit hn ({(⟨1, by omega⟩ : Fin n)} : Finset (Fin n)) = 2 := by
  rw [movedOrbit_singleton hn (j := ⟨1, by omega⟩)
    (by show 1 ≤ (1 : ℕ); omega)]
  simp

theorem choose_two_le_orbitSize_of_nonnatural {n : ℕ} {S : Finset (Fin n)} (hn : 5 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅)
    (hnon : ¬ (S = {(⟨1, by omega⟩ : Fin n)} ∨ S = {(⟨n - 1, by omega⟩ : Fin n)})) :
    n.choose 2 ≤ orbitSize S := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  by_cases h1 : S.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    rw [orbitSize_singleton]
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0
      rw [Finset.mem_singleton]
      exact Fin.ext h.symm
    have hjne1 : (j : ℕ) ≠ 1 := by
      intro h
      apply hnon
      left
      have h' : j = (⟨1, by omega⟩ : Fin n) := Fin.ext (by simpa using h)
      rw [h']
    have hjn : (j : ℕ) ≠ n - 1 := by
      intro h
      apply hnon
      right
      have h' : j = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext (by simpa using h)
      rw [h']
    have hj2 : 2 ≤ (j : ℕ) := by omega
    have hjn2 : (j : ℕ) ≤ n - 2 := by omega
    exact choose_two_le_choose hj2 hjn2
  · have h2 : 2 ≤ S.card := by
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    rw [orbitSize, card_rearr_topWt]
    have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
    have hsum := sum_blocks S
    have hl : 3 ≤ S.card + 1 := by omega
    have hN := multinomial_lower (b := blocks S) hb hsum hl
    calc n.choose 2 ≤ n * (n - 1) := by
          rw [Nat.choose_two_right]
          exact Nat.div_le_self _ _
      _ ≤ Nat.multinomial univ (blocks S) := hN

theorem two_mul_pred_le_movedOrbit_of_nonnatural {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (hn5 : 5 ≤ n) (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅)
    (hnon : ¬ (S = {(⟨1, by omega⟩ : Fin n)} ∨ S = {(⟨n - 1, by omega⟩ : Fin n)})) :
    2 * (n - 2) ≤ movedOrbit hn S := by
  classical
  by_cases h1 : S.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0
      rw [Finset.mem_singleton]
      exact Fin.ext h.symm
    have hjne1 : (j : ℕ) ≠ 1 := by
      intro h
      apply hnon
      left
      have h' : j = (⟨1, by omega⟩ : Fin n) := Fin.ext (by simpa using h)
      rw [h']
    have hjn : (j : ℕ) ≠ n - 1 := by
      intro h
      apply hnon
      right
      have h' : j = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext (by simpa using h)
      rw [h']
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
    rw [movedOrbit_singleton hn hj1]
    have hle : n - 2 ≤ (n - 2).choose (j - 1) := by
      apply le_choose
      · omega
      · omega
    exact Nat.mul_le_mul_left 2 hle
  · have h2 : 2 ≤ S.card := by
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    have hM := two_mul_two_mul_sub_three_le_movedOrbit hn h0 (by omega : 3 ≤ S.card + 1)
    omega

theorem movedTop_add_prod_fixed {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n)) :
    movedTop hn ε + ∏ i, fixedOrbit hn (ε i) = ∏ i, orbitSize (ε i) := by
  classical
  have h := card_piFinset_moved (O := fun i => rearr (topWt (ε i)))
    (π := Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n))
  simpa [movedTop, fixedOrbit, orbitSize] using h

theorem prod_eq_single_of_empty_other {n f : ℕ} (g : Finset (Fin n) → ℕ) (hg : g ∅ = 1)
    (ε : Fin f → Finset (Fin n)) (i₀ : Fin f) (h : ∀ i, i ≠ i₀ → ε i = ∅) :
    ∏ i, g (ε i) = g (ε i₀) := by
  classical
  rw [Finset.prod_eq_single i₀]
  · intro i _ hi
    rw [h i hi, hg]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem prod_eq_mul_two_of_empty_other {n f : ℕ} (g : Finset (Fin n) → ℕ) (hg : g ∅ = 1)
    (ε : Fin f → Finset (Fin n)) {i₁ i₂ : Fin f} (hne : i₁ ≠ i₂)
    (h : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅) :
    ∏ i, g (ε i) = g (ε i₁) * g (ε i₂) := by
  classical
  have hzero : ∀ i ∈ (univ : Finset (Fin f)), i ∉ ({i₁, i₂} : Finset (Fin f)) →
      g (ε i) = 1 := by
    intro i _ hi
    have hi1 : i ≠ i₁ := by
      intro hh
      apply hi
      rw [hh]
      exact Finset.mem_insert_self i₁ {i₂}
    have hi2 : i ≠ i₂ := by
      intro hh
      apply hi
      rw [hh]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i₂)
    rw [h i hi1 hi2, hg]
  have hmain := Finset.prod_subset (s₁ := ({i₁, i₂} : Finset (Fin f)))
    (s₂ := (univ : Finset (Fin f))) (subset_univ _) hzero
  rw [← hmain, Finset.prod_pair hne]

theorem mul_prod_erase_le_movedTop {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n))
    (j : Fin f) :
    movedOrbit hn (ε j) * ∏ i : {i : Fin f // i ≠ j}, orbitSize (ε i) ≤ movedTop hn ε := by
  classical
  let src : Finset ((Fin n → ℤ) × ({i : Fin f // i ≠ j} → Fin n → ℤ)) :=
    ((rearr (topWt (ε j))).filter (fun μ => μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩)) ×ˢ
      (Fintype.piFinset fun i : {i : Fin f // i ≠ j} => rearr (topWt (ε i)))
  let φ : (Fin n → ℤ) × ({i : Fin f // i ≠ j} → Fin n → ℤ) → (Fin f → Fin n → ℤ) :=
    fun x i => if h : i = j then x.1 else x.2 ⟨i, h⟩
  have hmem : ∀ x ∈ src, φ x ∈
      (Fintype.piFinset fun i => rearr (topWt (ε i))).filter
        (fun μ => ∃ i, μ i ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) ≠ μ i) := by
    rintro ⟨a, g⟩ hx
    simp only [src, Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨⟨haO, hamoved⟩, hg⟩ := hx
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i = j
      · subst hi
        simpa [φ] using haO
      · have hφi : φ (a, g) i = g ⟨i, hi⟩ := by simp [φ, hi]
        rw [hφi]
        exact hg ⟨i, hi⟩
    · refine ⟨j, ?_⟩
      have hφj : φ (a, g) j = a := by simp [φ]
      rw [hφj]
      exact (comp_swap_zero_one_eq_iff hn a).not.mpr hamoved
  have hinj : Function.Injective φ := by
    rintro ⟨a, g⟩ ⟨a', g'⟩ h
    have h1 : a = a' := by
      have hh := congrFun h j
      simpa [φ] using hh
    have h2 : g = g' := by
      funext i
      have hh := congrFun h i.1
      have hi : i.1 ≠ j := i.2
      simpa [φ, hi] using hh
    subst h1
    subst h2
    rfl
  have himage : src.image φ ⊆
      (Fintype.piFinset fun i => rearr (topWt (ε i))).filter
        (fun μ => ∃ i, μ i ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) ≠ μ i) := by
    intro μ hμ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hμ
    exact hmem x hx
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_of_injective src hinj] at hcard
  have hsrccard : src.card = movedOrbit hn (ε j) *
      ∏ i : {i : Fin f // i ≠ j}, orbitSize (ε i) := by
    simp [src, movedOrbit, orbitSize]
  rw [hsrccard] at hcard
  simpa [movedTop] using hcard

theorem pow_card_le_prod_orbitSize {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i) (j : Fin f) (hj : ε j ≠ ∅) :
    n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1) ≤
      ∏ i : {i : Fin f // i ≠ j}, orbitSize (ε i) := by
  classical
  set T : Finset (Fin f) := univ.filter (fun i => ε i ≠ ∅) with hT
  have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hcard : (T.erase j).card = T.card - 1 := Finset.card_erase_of_mem hjT
  have h1 : ∏ i : {i : Fin f // i ≠ j}, orbitSize (ε i) =
      ∏ i ∈ (univ.erase j : Finset (Fin f)), orbitSize (ε i) := by
    rw [← Finset.prod_subtype (s := (univ.erase j : Finset (Fin f)))
      (p := fun i => i ≠ j) (fun i => by simp) (fun i => orbitSize (ε i))]
  have h2 : ∏ i ∈ (univ.erase j : Finset (Fin f)), orbitSize (ε i) =
      ∏ i ∈ T.erase j, orbitSize (ε i) := by
    refine (Finset.prod_subset (s₁ := T.erase j) (s₂ := (univ.erase j : Finset (Fin f)))
      ?_ ?_).symm
    · intro i hi
      rw [Finset.mem_erase] at hi ⊢
      exact ⟨hi.1, Finset.mem_univ _⟩
    · intro i hi hni
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      have hnotT : i ∉ T := by
        intro hiT
        exact hni (Finset.mem_erase.mpr ⟨hij, hiT⟩)
      have hempty : ε i = ∅ := by
        by_contra hne
        exact hnotT (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      rw [hempty, orbitSize_empty]
  have h3 : ∏ i ∈ T.erase j, n ≤ ∏ i ∈ T.erase j, orbitSize (ε i) := by
    apply Finset.prod_le_prod
    intro i hi
    have hiT : i ∈ T := (Finset.mem_erase.mp hi).2
    exact n_le_orbitSize hn (h0 i) (Finset.mem_filter.mp hiT).2
  calc n ^ (T.card - 1) = n ^ (T.erase j).card := by rw [hcard]
    _ = ∏ i ∈ T.erase j, n := by rw [Finset.prod_const]
    _ ≤ ∏ i ∈ T.erase j, orbitSize (ε i) := h3
    _ = ∏ i : {i : Fin f // i ≠ j}, orbitSize (ε i) := by rw [← h2, ← h1]

theorem two_mul_pow_le_movedTop_of_three {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i)
    (hT : 3 ≤ (univ.filter fun i => ε i ≠ ∅).card) :
    2 * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1) ≤ movedTop hn ε := by
  classical
  obtain ⟨j, hjT⟩ := Finset.card_pos.mp (show 0 < (univ.filter fun i => ε i ≠ ∅).card by omega)
  have hj : ε j ≠ ∅ := (Finset.mem_filter.mp hjT).2
  have hM := two_le_movedOrbit hn (h0 j) hj
  have hprod := pow_card_le_prod_orbitSize hn ε h0 j hj
  have hinj := mul_prod_erase_le_movedTop hn ε j
  calc 2 * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1)
      ≤ movedOrbit hn (ε j) * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1) :=
        Nat.mul_le_mul_right _ hM
    _ ≤ movedOrbit hn (ε j) * ∏ i : {i : Fin f // i ≠ j}, orbitSize (ε i) :=
        Nat.mul_le_mul_left _ hprod
    _ ≤ movedTop hn ε := hinj

theorem movedTop_of_two {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n))
    {i₁ i₂ : Fin f} (hne : i₁ ≠ i₂) (h : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅) :
    movedTop hn ε = movedOrbit hn (ε i₁) * orbitSize (ε i₂) +
      movedOrbit hn (ε i₂) * (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) := by
  classical
  have hmain := movedTop_add_prod_fixed hn ε
  have hN := prod_eq_mul_two_of_empty_other (g := orbitSize) orbitSize_empty ε hne h
  have hF := prod_eq_mul_two_of_empty_other (g := fun S => fixedOrbit hn S)
    (fixedOrbit_empty hn) ε hne h
  rw [hN, hF] at hmain
  rw [fixedOrbit_eq hn, fixedOrbit_eq hn] at hmain
  have hle1 : movedOrbit hn (ε i₁) ≤ orbitSize (ε i₁) := by
    have := movedOrbit_add_fixedOrbit hn (ε i₁)
    omega
  have hle2 : movedOrbit hn (ε i₂) ≤ orbitSize (ε i₂) := by
    have := movedOrbit_add_fixedOrbit hn (ε i₂)
    omega
  have hN1 : orbitSize (ε i₁) =
      movedOrbit hn (ε i₁) + (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) :=
    (Nat.add_sub_of_le hle1).symm
  have hN2 : orbitSize (ε i₂) =
      movedOrbit hn (ε i₂) + (orbitSize (ε i₂) - movedOrbit hn (ε i₂)) :=
    (Nat.add_sub_of_le hle2).symm
  have hprod1 : orbitSize (ε i₁) * orbitSize (ε i₂) =
      movedOrbit hn (ε i₁) * orbitSize (ε i₂) +
        (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) * orbitSize (ε i₂) := by
    conv_lhs => rw [hN1]
    exact add_mul _ _ _
  have hprod2 : (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) * orbitSize (ε i₂) =
      movedOrbit hn (ε i₂) * (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) +
        (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) *
          (orbitSize (ε i₂) - movedOrbit hn (ε i₂)) := by
    conv_lhs => rw [hN2]
    rw [mul_add, mul_comm (orbitSize (ε i₁) - movedOrbit hn (ε i₁)) (movedOrbit hn (ε i₂))]
  omega

theorem mul_sub_three_le_movedOrbit {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n) (hn5 : 5 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hS : 3 ≤ S.card + 1)
    (hne : ¬ (S.card + 1 = 3 ∧ ∃ i, blocks S i = n - 2)) :
    (n - 2) * (3 * n - 7) ≤ movedOrbit hn S := by
  classical
  have hn0 : 0 < n := by omega
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hkey := mul_add_multinomial_le_of_ne (b := blocks S) hb hsum hS hn5 hne
  set N := Nat.multinomial univ (blocks S) with hNdef
  set T := ∑ i, blocks S i ^ 2 with hTdef
  have hkey' : n * (n - 1) * (n - 2) * (3 * n - 7) + N * T ≤ N * n ^ 2 := hkey
  have hmoved := card_moved_rearr_topWt S hn
  have hmoved' : movedOrbit hn S * (n * (n - 1)) = N * (n ^ 2 - T) := by
    simpa [movedOrbit, hNdef, hTdef] using hmoved
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Nat.multinomial_pos _ _
  have hA : n * (n - 1) * (n - 2) * (3 * n - 7) ≤ N * (n ^ 2 - T) := by
    have h1 : n * (n - 1) * (n - 2) * (3 * n - 7) ≤ N * n ^ 2 - N * T :=
      Nat.le_sub_of_add_le hkey'
    rwa [← Nat.mul_sub_left_distrib] at h1
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.le_of_mul_le_mul_right (c := n * (n - 1)) _ hpos
  rw [hmoved']
  calc (n - 2) * (3 * n - 7) * (n * (n - 1)) =
        n * (n - 1) * (n - 2) * (3 * n - 7) := by ring
    _ ≤ N * (n ^ 2 - T) := hA

theorem four_mul_mul_sub_le_sq {n c : ℕ} (hc : c ≤ n) : 4 * (c * (n - c)) ≤ n ^ 2 := by
  set d := n - c with hd
  have h : n = c + d := by omega
  rw [h, pow_two]
  nlinarith [sq_nonneg ((c : ℤ) - (d : ℤ))]

theorem false_of_three_le_factors {n f s e c : ℕ} {ε : Fin f → Finset (Fin n)}
    (hn : 5 ≤ n) (hf : 0 < f)
    (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i)
    (hT : 3 ≤ (univ.filter fun i => ε i ≠ ∅).card)
    (hs : f ≤ s * (univ.filter fun i => ε i ≠ ∅).card)
    (hcn : c ≤ n)
    (hineq : s * e ≤ 1 + f * (c * (n - c)))
    (htop : movedTop (by omega) ε ≤ 2 * e) : False := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hs' : f ≤ s * (univ.filter fun i => ε i ≠ ∅).card := hs
  have htop' : movedTop hn2 ε ≤ 2 * e := htop
  have hlow := two_mul_pow_le_movedTop_of_three hn2 ε h0 hT
  have he : n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1) ≤ e :=
    Nat.le_of_mul_le_mul_left (le_trans hlow htop') (by norm_num)
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.zero_mul] at hs'
      omega
    · exact h
  have hP : 1 ≤ s * (univ.filter fun i => ε i ≠ ∅).card := by omega
  have h4 := four_mul_mul_sub_le_sq hcn
  have hC4 : 4 * (f * (c * (n - c))) ≤ f * n ^ 2 := by
    calc 4 * (f * (c * (n - c))) = f * (4 * (c * (n - c))) := by ring
      _ ≤ f * n ^ 2 := Nat.mul_le_mul_left f h4
  have hse : 4 * (s * e) ≤ 4 + f * n ^ 2 := by
    have h1 : 4 * (s * e) ≤ 4 * (1 + f * (c * (n - c))) := Nat.mul_le_mul_left 4 hineq
    have h2 : 4 * (1 + f * (c * (n - c))) = 4 + 4 * (f * (c * (n - c))) := by ring
    omega
  have hsn : 4 * (s * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1)) ≤ 4 + f * n ^ 2 := by
    have h1 : 4 * (s * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1)) ≤ 4 * (s * e) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left s he)
    omega
  have hpow := mul_sq_add_four_lt_pow (m := n) (t := (univ.filter fun i => ε i ≠ ∅).card) hn hT
  have hlt : s * ((univ.filter fun i => ε i ≠ ∅).card * (n ^ 2 + 4)) <
      4 * (s * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1)) := by
    have h := Nat.mul_lt_mul_of_pos_left hpow hs_pos
    calc s * ((univ.filter fun i => ε i ≠ ∅).card * (n ^ 2 + 4))
        < s * (4 * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1)) := h
      _ = 4 * (s * n ^ ((univ.filter fun i => ε i ≠ ∅).card - 1)) := by ring
  have hfn : f * n ^ 2 ≤ s * (univ.filter fun i => ε i ≠ ∅).card * n ^ 2 :=
    Nat.mul_le_mul_right _ hs'
  have hkey : s * ((univ.filter fun i => ε i ≠ ∅).card * (n ^ 2 + 4)) =
      s * (univ.filter fun i => ε i ≠ ∅).card * n ^ 2 +
        4 * (s * (univ.filter fun i => ε i ≠ ∅).card) := by ring
  omega

theorem false_of_two_factor_rank {n f s e c : ℕ} (hn : 5 ≤ n) (hf : 0 < f)
    (hs : f ≤ s * 2) (hcn : c ≤ n)
    (hineq : s * e ≤ 1 + f * (c * (n - c)))
    (he : n.choose 2 + (n - 2) ^ 2 ≤ e) : False := by
  have hs_pos : 0 < s := by omega
  have h2e : n ^ 2 + 5 ≤ 2 * e := by
    have h := sq_add_four_lt_choose_add_sq hn
    have h2 : 2 * (n.choose 2 + (n - 2) ^ 2) ≤ 2 * e := Nat.mul_le_mul_left 2 he
    omega
  have h1 : 2 * (s * e) ≤ 2 + s * n ^ 2 := by
    have h1' : 2 * (s * e) ≤ 2 * (1 + f * (c * (n - c))) := Nat.mul_le_mul_left 2 hineq
    have h2' : 2 * (1 + f * (c * (n - c))) = 2 + 2 * (f * (c * (n - c))) := by ring
    have hf2 : 2 * f ≤ 4 * s := by omega
    have h3' : 2 * (f * (c * (n - c))) ≤ s * n ^ 2 := by
      have h4 := four_mul_mul_sub_le_sq hcn
      calc 2 * (f * (c * (n - c))) = (2 * f) * (c * (n - c)) := by ring
        _ ≤ (4 * s) * (c * (n - c)) := Nat.mul_le_mul_right _ hf2
        _ = s * (4 * (c * (n - c))) := by ring
        _ ≤ s * n ^ 2 := Nat.mul_le_mul_left s h4
    omega
  have h2 : s * n ^ 2 + 5 * s ≤ 2 * (s * e) := by
    have h := Nat.mul_le_mul_left s h2e
    calc s * n ^ 2 + 5 * s = s * (n ^ 2 + 5) := by ring
      _ ≤ s * (2 * e) := h
      _ = 2 * (s * e) := by ring
  omega

theorem false_of_two_natural {n f s e c : ℕ} (hn : 5 ≤ n) (hf : 0 < f) (hc : 1 ≤ c)
    (hs2 : 2 * f ≤ s) (hcn : c ≤ n)
    (hineq : s * e ≤ 1 + f * (c * (n - c)))
    (he : n * c ≤ e) : False := by
  have h1 : 2 * (s * e) ≤ 2 + s * (c * (n - c)) := by
    have h1' : 2 * (s * e) ≤ 2 * (1 + f * (c * (n - c))) := Nat.mul_le_mul_left 2 hineq
    have h2' : 2 * (1 + f * (c * (n - c))) = 2 + 2 * (f * (c * (n - c))) := by ring
    have h3 : 2 * (f * (c * (n - c))) ≤ s * (c * (n - c)) := by
      calc 2 * (f * (c * (n - c))) = (2 * f) * (c * (n - c)) := by ring
        _ ≤ s * (c * (n - c)) := Nat.mul_le_mul_right _ hs2
    omega
  have hkey : s * (c * (n + c)) + s * (c * (n - c)) = 2 * (s * (n * c)) := by
    have hnc : (n + c) + (n - c) = 2 * n := by omega
    calc s * (c * (n + c)) + s * (c * (n - c))
        = s * (c * ((n + c) + (n - c))) := by rw [← mul_add]; ring
      _ = s * (c * (2 * n)) := by rw [hnc]
      _ = 2 * (s * (n * c)) := by ring
  have h2 : s * (c * (n + c)) + s * (c * (n - c)) ≤ 2 * (s * e) := by
    rw [hkey]
    exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left s he)
  have h3 : s * (c * (n + c)) ≤ 2 := by
    have h2' : 2 * (s * (n * c)) ≤ 2 * (s * e) := by
      rw [← hkey]
      exact h2
    have hsum : s * (c * (n + c)) + s * (c * (n - c)) ≤ 2 + s * (c * (n - c)) := by
      calc s * (c * (n + c)) + s * (c * (n - c))
          = 2 * (s * (n * c)) := hkey
        _ ≤ 2 * (s * e) := h2'
        _ ≤ 2 + s * (c * (n - c)) := h1
    exact (Nat.add_le_add_iff_right).mp hsum
  have h4 : 2 * (f * (c * (n + c))) ≤ 2 := by
    calc 2 * (f * (c * (n + c))) = (2 * f) * (c * (n + c)) := by ring
      _ ≤ s * (c * (n + c)) := Nat.mul_le_mul_right _ hs2
      _ ≤ 2 := h3
  have h5 : f * (c * (n + c)) ≤ 1 := by omega
  have h6 : 6 ≤ c * (n + c) := by nlinarith
  have h7 : 6 ≤ f * (c * (n + c)) := by
    calc 6 = 1 * 6 := by norm_num
      _ ≤ f * (c * (n + c)) := Nat.mul_le_mul hf h6
  omega

theorem false_of_one_rank {n f s e c A : ℕ} (hf : 0 < f)
    (hcn : c ≤ n) (hs : f ≤ s)
    (hineq : s * e ≤ 1 + f * (c * (n - c)))
    (hA : A ≤ 2 * e) (hA2 : n ^ 2 + 4 < 2 * A) : False := by
  have hs_pos : 0 < s := by omega
  have he : n ^ 2 + 5 ≤ 4 * e := by
    have h1 : 2 * A ≤ 4 * e := by
      calc 2 * A ≤ 2 * (2 * e) := Nat.mul_le_mul_left 2 hA
        _ = 4 * e := by ring
    omega
  have h4 := four_mul_mul_sub_le_sq hcn
  have hse : 4 * (s * e) ≤ 4 + s * n ^ 2 := by
    have h1 : 4 * (s * e) ≤ 4 * (1 + f * (c * (n - c))) := Nat.mul_le_mul_left 4 hineq
    have h2 : 4 * (1 + f * (c * (n - c))) = 4 + 4 * (f * (c * (n - c))) := by ring
    have h3 : 4 * (f * (c * (n - c))) ≤ s * n ^ 2 := by
      calc 4 * (f * (c * (n - c))) = f * (4 * (c * (n - c))) := by ring
        _ ≤ s * (4 * (c * (n - c))) := Nat.mul_le_mul_right _ hs
        _ ≤ s * n ^ 2 := Nat.mul_le_mul_left s h4
    omega
  have h3 : s * n ^ 2 + 5 * s ≤ 4 * (s * e) := by
    have h := Nat.mul_le_mul_left s he
    calc s * n ^ 2 + 5 * s = s * (n ^ 2 + 5) := by ring
      _ ≤ s * (4 * e) := h
      _ = 4 * (s * e) := by ring
  omega

theorem false_of_one_adjoint {n f s e : ℕ} (hn : 5 ≤ n) (hf : 0 < f) (hs : f ≤ s)
    (hadj : s * e ≤ 1 + f) (he : 2 * n - 3 ≤ e) : False := by
  have h1 : s * (2 * n - 3) ≤ 1 + f := le_trans (Nat.mul_le_mul_left s he) hadj
  have harg : 2 * n - 3 = (2 * n - 4) + 1 := by omega
  rw [harg, Nat.mul_add, Nat.mul_one] at h1
  have h2 : s * (2 * n - 4) ≤ 1 := by omega
  have h3 : 6 ≤ 2 * n - 4 := by omega
  have h4 : s * 6 ≤ s * (2 * n - 4) := Nat.mul_le_mul_left s h3
  omega

theorem false_of_one_singleton_six {f s e : ℕ} (hf : 0 < f)
    (hs : f ≤ s) (hcube : s * e ≤ 1 + 2 * f) (he : 6 ≤ e) : False := by
  have h1 : s * 6 ≤ s * e := Nat.mul_le_mul_left s he
  have h2 : s * 6 ≤ 1 + 2 * f := le_trans h1 hcube
  omega

theorem false_of_one_singleton_nonsym {n f s e c j : ℕ} (hn : 6 ≤ n) (hf : 0 < f)
    (hcn : c ≤ n) (hs2 : 2 * f ≤ s)
    (hineq : s * e ≤ 1 + f * (c * (n - c)))
    (he : (n - 2).choose (j - 1) ≤ e) (hj3 : 3 ≤ j) (hjn : j + 3 ≤ n) : False := by
  have h1 : (n - 2) * (n - 3) ≤ 2 * e := by
    have h := mul_le_two_mul_choose hj3 hjn
    omega
  have hA : n ^ 2 + 5 ≤ 4 * ((n - 2) * (n - 3)) := by
    have h := sq_add_four_lt_four_mul (by omega : 6 ≤ n)
    omega
  have he8 : n ^ 2 + 5 ≤ 8 * e := by
    have h := Nat.mul_le_mul_left 4 h1
    omega
  have h4 := four_mul_mul_sub_le_sq hcn
  have hse : 8 * (s * e) ≤ 8 + s * n ^ 2 := by
    have h1' : 8 * (s * e) ≤ 8 * (1 + f * (c * (n - c))) := Nat.mul_le_mul_left 8 hineq
    have h2' : 8 * (1 + f * (c * (n - c))) = 8 + 8 * (f * (c * (n - c))) := by ring
    have hf : 8 * f ≤ 4 * s := by omega
    have h3' : 8 * (f * (c * (n - c))) ≤ s * n ^ 2 := by
      calc 8 * (f * (c * (n - c))) = (8 * f) * (c * (n - c)) := by ring
        _ ≤ (4 * s) * (c * (n - c)) := Nat.mul_le_mul_right _ hf
        _ = s * (4 * (c * (n - c))) := by ring
        _ ≤ s * n ^ 2 := Nat.mul_le_mul_left s h4
    omega
  have h3 : s * n ^ 2 + 5 * s ≤ 8 * (s * e) := by
    have h := Nat.mul_le_mul_left s he8
    calc s * n ^ 2 + 5 * s = s * (n ^ 2 + 5) := by ring
      _ ≤ s * (8 * e) := h
      _ = 8 * (s * e) := by ring
  omega

theorem two_factor_lower {a b c d N1 M1 N2 M2 : ℕ}
    (hba : b ≤ a) (haN : a ≤ N1) (hbM : b ≤ M1) (hM1N : M1 ≤ N1)
    (hcN : c ≤ N2) (hdM : d ≤ M2) (hM2N : M2 ≤ N2) :
    b * c + d * (a - b) ≤ M1 * N2 + M2 * (N1 - M1) := by
  have h1 : b * N2 + M2 * (N1 - b) ≤ M1 * N2 + M2 * (N1 - M1) := by
    have hb : N1 - b = (N1 - M1) + (M1 - b) := by omega
    have hMb : M2 * (M1 - b) ≤ (M1 - b) * N2 := by
      rw [mul_comm M2 (M1 - b)]
      exact Nat.mul_le_mul_left _ hM2N

    have hsplit : M1 * N2 = b * N2 + (M1 - b) * N2 := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hbM]
    rw [hb, Nat.mul_add, hsplit]
    omega
  have h2 : b * c + d * (a - b) ≤ b * N2 + M2 * (N1 - b) := by
    have hbc : b * c ≤ b * N2 := Nat.mul_le_mul_left b hcN
    have hd : d * (a - b) ≤ M2 * (N1 - b) := by
      apply Nat.mul_le_mul hdM
      omega
    exact Nat.add_le_add hbc hd
  exact le_trans h2 h1

theorem two_factor_lower_special {n N1 M1 N2 M2 : ℕ} (hn : 2 ≤ n)
    (hC : 2 * (n - 2) ≤ n.choose 2)
    (hN1 : n.choose 2 ≤ N1) (hM1 : 2 * (n - 2) ≤ M1) (hM1N : M1 ≤ N1)
    (hN2 : n ≤ N2) (hM2 : 2 ≤ M2) (hM2N : M2 ≤ N2) :
    2 * (n.choose 2 + (n - 2) ^ 2) ≤ M1 * N2 + M2 * (N1 - M1) := by
  have h := two_factor_lower (a := n.choose 2) (b := 2 * (n - 2)) (c := n) (d := 2)
    hC hN1 hM1 hM1N hN2 hM2 hM2N
  have hcalc : 2 * (n - 2) * n + 2 * (n.choose 2 - 2 * (n - 2)) =
      2 * (n.choose 2 + (n - 2) ^ 2) := by
    have h1 : 2 * (2 * (n - 2)) + 2 * (n.choose 2 - 2 * (n - 2)) = 2 * n.choose 2 := by
      rw [Nat.add_comm, ← Nat.mul_add, Nat.sub_add_cancel hC]
    have h2 : 2 * (n - 2) * n = 2 * (n - 2) * (n - 2) + 2 * (2 * (n - 2)) := by
      nth_rewrite 2 [show n = (n - 2) + 2 by omega]
      ring
    calc 2 * (n - 2) * n + 2 * (n.choose 2 - 2 * (n - 2))
        = 2 * (n - 2) * (n - 2) + 2 * (2 * (n - 2)) +
            2 * (n.choose 2 - 2 * (n - 2)) := by rw [h2]
      _ = 2 * (n - 2) * (n - 2) +
            (2 * (2 * (n - 2)) + 2 * (n.choose 2 - 2 * (n - 2))) := by ring
      _ = 2 * (n - 2) * (n - 2) + 2 * n.choose 2 := by rw [h1]
      _ = 2 * (n.choose 2 + (n - 2) ^ 2) := by ring
  rwa [hcalc] at h

theorem movedTop_of_one {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n)) (i₀ : Fin f)
    (h : ∀ i, i ≠ i₀ → ε i = ∅) :
    movedTop hn ε = movedOrbit hn (ε i₀) := by
  classical
  have hmain := movedTop_add_prod_fixed hn ε
  have hN := prod_eq_single_of_empty_other (g := orbitSize) orbitSize_empty ε i₀ h
  have hF := prod_eq_single_of_empty_other (g := fun S => fixedOrbit hn S)
    (fixedOrbit_empty hn) ε i₀ h
  rw [hN, hF] at hmain
  have := movedOrbit_add_fixedOrbit hn (ε i₀)
  omega

theorem prime_dvd_of_scalar_singleton {n f r : ℕ} {ε : Fin f → Finset (Fin n)}
    {i₀ : Fin f} {j : Fin n}
    (hr : r.Prime) (hr2 : r ≠ 2) (h : ∀ i, i ≠ i₀ → ε i = ∅)
    (hS : ε i₀ = {j})
    (hscal : r ∣ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ t ∈ ε i, (t : ℕ)) :
    r ∣ (j : ℕ) := by
  classical
  have hsum : ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ t ∈ ε i, (t : ℕ) = 2 ^ (i₀ : ℕ) * (j : ℕ) := by
    rw [Finset.sum_eq_single i₀]
    · rw [hS, Finset.sum_singleton]
    · intro i _ hi
      rw [h i hi]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i₀) hi
  rw [hsum] at hscal
  have hnot : ¬ r ∣ 2 ^ (i₀ : ℕ) := by
    intro hd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  exact (hr.dvd_mul.mp hscal).resolve_left hnot

theorem two_factor_nonnatural_lower {n f : ℕ} {ε : Fin f → Finset (Fin n)}
    (hn : 5 ≤ n) (hn2 : 2 ≤ n) (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i)
    {i₁ i₂ : Fin f} (hne : i₁ ≠ i₂) (hempty : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅)
    (hi1 : ε i₁ ≠ ∅) (hi2 : ε i₂ ≠ ∅)
    (hnon : ¬ (ε i₁ = {(⟨1, by omega⟩ : Fin n)} ∨
      ε i₁ = {(⟨n - 1, by omega⟩ : Fin n)})) :
    2 * (n.choose 2 + (n - 2) ^ 2) ≤ movedTop hn2 ε := by
  rw [movedTop_of_two hn2 ε hne hempty]
  have hN1 : n.choose 2 ≤ orbitSize (ε i₁) :=
    choose_two_le_orbitSize_of_nonnatural hn (h0 i₁) hi1 hnon
  have hM1 : 2 * (n - 2) ≤ movedOrbit hn2 (ε i₁) :=
    two_mul_pred_le_movedOrbit_of_nonnatural hn2 hn (h0 i₁) hi1 hnon
  have hN2 : n ≤ orbitSize (ε i₂) := n_le_orbitSize hn2 (h0 i₂) hi2
  have hM2 : 2 ≤ movedOrbit hn2 (ε i₂) := two_le_movedOrbit hn2 (h0 i₂) hi2
  have hM1N : movedOrbit hn2 (ε i₁) ≤ orbitSize (ε i₁) := by
    have := movedOrbit_add_fixedOrbit hn2 (ε i₁)
    omega
  have hM2N : movedOrbit hn2 (ε i₂) ≤ orbitSize (ε i₂) := by
    have := movedOrbit_add_fixedOrbit hn2 (ε i₂)
    omega
  have hC : 2 * (n - 2) ≤ n.choose 2 := by
    have h2 := two_mul_choose_two n
    have h4 : 2 * (2 * (n - 2)) ≤ 2 * n.choose 2 := by
      rw [h2]
      have h1 : n = (n - 1) + 1 := by omega
      have h3 : n = (n - 2) + 2 := by omega
      nlinarith
    omega
  exact two_factor_lower_special hn2 hC hN1 hM1 hM1N hN2 hM2 hM2N

theorem false_of_scalar_bounds {n f r : ℕ} (hn : 5 ≤ n) (hf : 0 < f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ n) (ε : Fin f → Finset (Fin n)) (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i)
    (ht : ∃ i, ε i ≠ ∅)
    (hscal : r ∣ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ))
    {s e c : ℕ}
    (hs : f ≤ s * (univ.filter fun i => ε i ≠ ∅).card)
    (hs2 : (univ.filter fun i => ε i ≠ ∅).card ≤ 2 →
      (∃ i, ∃ j ∈ ε i, ∃ hj : n - (j : ℕ) < n, (⟨n - j, hj⟩ : Fin n) ∉ ε i) → 2 * f ≤ s)
    (hc : 1 ≤ c) (hcn : c ≤ n) (hineq : s * e ≤ 1 + f * (c * (n - c)))
    (htop : movedTop (by omega) ε ≤ 2 * e)
    (hextra : ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) →
      (ε i₀ = {⟨1, by omega⟩, ⟨2, by omega⟩} ∨ ε i₀ = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) →
      n * (n - 1) ≤ 2 * e)
    (hadj : ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) → ε i₀ = {⟨1, by omega⟩, ⟨n - 1, by omega⟩} → s * e ≤ 1 + f)
    (hcube : ∀ (h6 : n = 6), ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) → ε i₀ = {⟨3, by omega⟩} → s * e ≤ 1 + 2 * f)
    (hnat : (univ.filter fun i => ε i ≠ ∅).card = 2 →
      (∀ i, ε i ≠ ∅ → ε i = {⟨1, by omega⟩} ∨ ε i = {⟨n - 1, by omega⟩}) → n * c ≤ e) :
    False := by
  classical
  have hn2 : 2 ≤ n := by omega
  let T : Finset (Fin f) := univ.filter fun i => ε i ≠ ∅
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, by simpa [T] using hi⟩
  have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
  have hs' : f ≤ s * T.card := by simpa [T] using hs
  rcases Nat.lt_or_ge T.card 3 with hlt | hge
  · have h1or2 : T.card = 1 ∨ T.card = 2 := by omega
    rcases h1or2 with h1 | h2
    ·
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
      have hempty : ∀ i, i ≠ i₀ → ε i = ∅ := by
        intro i hi
        by_contra hne
        have hmem : i ∈ T := by simpa [T] using hne
        rw [hi₀] at hmem
        exact hi (Finset.mem_singleton.mp hmem)
      have hSne : ε i₀ ≠ ∅ := by
        have hmem : i₀ ∈ T := by rw [hi₀]; exact Finset.mem_singleton_self i₀
        simpa [T] using hmem
      have hs1 : f ≤ s := by
        have h := hs'
        rw [h1, Nat.mul_one] at h
        exact h
      have hmoved : movedTop hn2 ε = movedOrbit hn2 (ε i₀) := movedTop_of_one hn2 ε i₀ hempty
      have htopM : movedOrbit hn2 (ε i₀) ≤ 2 * e := by
        rw [← hmoved]
        exact htop
      by_cases hc0 : (ε i₀).card = 0
      · exact absurd (Finset.card_eq_zero.mp hc0) hSne
      · have hcpos : 0 < (ε i₀).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
        rcases Nat.lt_or_ge (ε i₀).card 2 with hc1 | hc2
        ·
          have hcard1 : (ε i₀).card = 1 := by omega
          obtain ⟨j, hSj⟩ := Finset.card_eq_one.mp hcard1
          have hj0 : (j : ℕ) ≠ 0 := by
            intro h
            apply h0 i₀
            rw [hSj, Finset.mem_singleton]
            exact Fin.ext h.symm
          have hjpos : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
          have hrdvd : r ∣ (j : ℕ) := prime_dvd_of_scalar_singleton hr hr2 hempty hSj hscal
          have hr3 : 3 ≤ r := by
            have := hr.two_le
            omega
          have hj3 : 3 ≤ (j : ℕ) := le_trans hr3 (Nat.le_of_dvd (by omega) hrdvd)
          have hjn : (j : ℕ) + 3 ≤ n := by
            have hle : (j : ℕ) ≤ n - 3 := by
              by_contra h
              have hge' : n - 2 ≤ (j : ℕ) := by omega
              have hdvd : r ∣ n - (j : ℕ) := Nat.dvd_sub hrn hrdvd
              have hpos : 0 < n - (j : ℕ) := by omega
              have hrle : r ≤ n - (j : ℕ) := Nat.le_of_dvd hpos hdvd
              omega
            omega
          have he : (n - 2).choose ((j : ℕ) - 1) ≤ e := by
            have hmoved' : movedTop hn2 ε = 2 * (n - 2).choose ((j : ℕ) - 1) := by
              rw [hmoved, hSj, movedOrbit_singleton hn2 hjpos]
            have h := htop
            rw [hmoved'] at h
            omega
          by_cases hmid : n = 2 * (j : ℕ)
          ·
            have heven : Even n := ⟨(j : ℕ), by omega⟩
            by_cases h6 : n = 6
            · have hjval : (j : ℕ) = 3 := by omega
              have hset : ε i₀ = {(⟨3, by omega⟩ : Fin n)} := by
                rw [hSj]
                congr 1
                exact Fin.ext hjval
              have hcube' : s * e ≤ 1 + 2 * f := hcube h6 i₀ hempty hset
              have he6 : 6 ≤ e := by
                have h := he
                have hnsub : n - 2 = 4 := by omega
                rw [hnsub, hjval] at h
                norm_num at h
                exact h
              exact false_of_one_singleton_six hf hs1 hcube' he6
            · have hn8 : 8 ≤ n := by omega
              have he3 : (n - 2).choose 3 ≤ e := by
                have h := choose_three_le_choose_half (m := n) hn8 heven
                have h2' : (n - 2).choose ((j : ℕ) - 1) = (n - 2).choose (n / 2 - 1) := by
                  congr 1
                  omega
                rw [h2'] at he
                exact le_trans h he
              have hA : 2 * ((n - 2).choose 3) ≤ 2 * e := Nat.mul_le_mul_left 2 he3
              have hA2 : n ^ 2 + 4 < 2 * (2 * ((n - 2).choose 3)) := by
                have h := sq_add_four_lt_four_mul_choose_three hn8
                nlinarith
              exact false_of_one_rank hf hcn hs1 hineq hA hA2
          ·
            have hnsym : ∃ i, ∃ j' ∈ ε i, ∃ hj : n - (j' : ℕ) < n,
                (⟨n - j', hj⟩ : Fin n) ∉ ε i := by
              refine ⟨i₀, j, ?_, ?_, ?_⟩
              · rw [hSj]; exact Finset.mem_singleton_self j
              · omega
              · rw [hSj, Finset.mem_singleton]
                intro heq
                have hv : n - (j : ℕ) = (j : ℕ) := by simpa using congrArg Fin.val heq
                omega
            have h2f : 2 * f ≤ s := hs2 (by simpa [T] using (by omega : T.card ≤ 2)) hnsym
            exact false_of_one_singleton_nonsym (by omega : 6 ≤ n) hf hcn h2f hineq he hj3 hjn
        ·
          have hS2 : 3 ≤ (ε i₀).card + 1 := by omega
          have htopM' : movedOrbit hn2 (ε i₀) ≤ 2 * e := by
            rw [← hmoved]
            exact htop
          by_cases hex : (ε i₀).card = 2 ∧ ∃ k, blocks (ε i₀) k = n - 2
          · obtain ⟨hcard2, hex2⟩ := hex
            have hdisj := (exists_blocks_eq_sub_two_iff (n := n) (S := ε i₀)
              (by omega : 4 ≤ n) (h0 i₀) hcard2).mp hex2
            rcases hdisj with h12 | h1n | hn12
            · have hA : n * (n - 1) ≤ 2 * e := hextra i₀ hempty (Or.inl h12)
              have hA2 : n ^ 2 + 4 < 2 * (n * (n - 1)) := by
                have h := sq_add_four_lt_four_mul_choose_two (m := n) (by omega : 4 ≤ n)
                have hc2' := two_mul_choose_two n
                nlinarith
              exact false_of_one_rank hf hcn hs1 hineq hA hA2
            · have hadj' : s * e ≤ 1 + f := hadj i₀ hempty h1n
              have he : 2 * n - 3 ≤ e := by
                have hM := two_mul_two_mul_sub_three_le_movedOrbit hn2 (h0 i₀) hS2
                omega
              exact false_of_one_adjoint hn hf hs1 hadj' he
            · have hA : n * (n - 1) ≤ 2 * e := hextra i₀ hempty (Or.inr hn12)
              have hA2 : n ^ 2 + 4 < 2 * (n * (n - 1)) := by
                have h := sq_add_four_lt_four_mul_choose_two (m := n) (by omega : 4 ≤ n)
                have hc2' := two_mul_choose_two n
                nlinarith
              exact false_of_one_rank hf hcn hs1 hineq hA hA2
          · have hne' : ¬ ((ε i₀).card + 1 = 3 ∧ ∃ k, blocks (ε i₀) k = n - 2) := by
              rintro ⟨hc3, hk⟩
              exact hex ⟨by omega, hk⟩
            have hM := mul_sub_three_le_movedOrbit hn2 hn (h0 i₀) hS2 hne'
            have hA : (n - 2) * (3 * n - 7) ≤ 2 * e := le_trans hM htopM'
            have hA2 : n ^ 2 + 4 < 2 * ((n - 2) * (3 * n - 7)) := sq_add_four_lt_two_mul (m := n) hn
            exact false_of_one_rank hf hcn hs1 hineq hA hA2
    ·
      obtain ⟨i₁, i₂, hne, hTpair⟩ := Finset.card_eq_two.mp h2
      have hempty : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅ := by
        intro i hi1 hi2
        by_contra hne'
        have hmem : i ∈ T := by simpa [T] using hne'
        rw [hTpair] at hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hi1 h
        · exact hi2 (Finset.mem_singleton.mp h)
      have hi1 : ε i₁ ≠ ∅ := by
        have hmem : i₁ ∈ T := by
          rw [hTpair]; exact Finset.mem_insert_self i₁ {i₂}
        simpa [T] using hmem
      have hi2 : ε i₂ ≠ ∅ := by
        have hmem : i₂ ∈ T := by
          rw [hTpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i₂)
        simpa [T] using hmem
      have hmoved := movedTop_of_two hn2 ε hne hempty
      have hs2' : f ≤ s * 2 := by
        have h := hs'
        rw [h2] at h
        exact h
      by_cases hnat1 : ε i₁ = {(⟨1, by omega⟩ : Fin n)} ∨
          ε i₁ = {(⟨n - 1, by omega⟩ : Fin n)}
      · by_cases hnat2 : ε i₂ = {(⟨1, by omega⟩ : Fin n)} ∨
            ε i₂ = {(⟨n - 1, by omega⟩ : Fin n)}
        ·
          have hnatall : ∀ i, ε i ≠ ∅ →
              ε i = {⟨1, by omega⟩} ∨ ε i = {⟨n - 1, by omega⟩} := by
            intro i hi
            have hmem : i ∈ T := by simpa [T] using hi
            rw [hTpair] at hmem
            rcases Finset.mem_insert.mp hmem with h | h
            · rw [h]; exact hnat1
            · rw [Finset.mem_singleton.mp h]; exact hnat2
          have hnc : n * c ≤ e := hnat (by simpa [T] using h2) hnatall
          have hnsym : ∃ i, ∃ j ∈ ε i, ∃ hj : n - (j : ℕ) < n,
              (⟨n - j, hj⟩ : Fin n) ∉ ε i := by
            rcases hnat1 with h1 | h1
            · refine ⟨i₁, ⟨1, by omega⟩, ?_, ?_, ?_⟩
              · rw [h1]; exact Finset.mem_singleton_self _
              · show n - 1 < n
                omega
              · rw [h1, Finset.mem_singleton]
                intro heq
                have hv : n - 1 = 1 := by simpa using congrArg Fin.val heq
                omega
            · refine ⟨i₁, ⟨n - 1, by omega⟩, ?_, ?_, ?_⟩
              · rw [h1]; exact Finset.mem_singleton_self _
              · show n - (n - 1) < n
                omega
              · rw [h1, Finset.mem_singleton]
                intro heq
                have hv : n - (n - 1) = n - 1 := by simpa using congrArg Fin.val heq
                omega
          have h2f : 2 * f ≤ s := hs2 (by simpa [T] using (by omega : T.card ≤ 2)) hnsym
          exact false_of_two_natural hn hf hc h2f hcn hineq hnc
        ·
          have hlower : 2 * (n.choose 2 + (n - 2) ^ 2) ≤ movedTop hn2 ε :=
            two_factor_nonnatural_lower hn hn2 h0 hne.symm
              (fun i hi1' hi2' => hempty i hi2' hi1') hi2 hi1 hnat2
          have he : n.choose 2 + (n - 2) ^ 2 ≤ e := by
            have h := le_trans hlower htop
            omega
          exact false_of_two_factor_rank hn hf hs2' hcn hineq he
      ·
        have hlower : 2 * (n.choose 2 + (n - 2) ^ 2) ≤ movedTop hn2 ε :=
          two_factor_nonnatural_lower hn hn2 h0 hne hempty hi1 hi2 hnat1
        have he : n.choose 2 + (n - 2) ^ 2 ≤ e := by
          have h := le_trans hlower htop
          omega
        exact false_of_two_factor_rank hn hf hs2' hcn hineq he
  ·
    exact false_of_three_le_factors hn hf h0 (by simpa [T] using hge)
      (by simpa [T] using hs) hcn hineq htop

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

