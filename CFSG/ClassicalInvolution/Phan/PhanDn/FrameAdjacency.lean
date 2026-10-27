module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame
import CFSG.ClassicalInvolution.Phan.PhanDn.Perp
import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap

variable {K : Type} [Field K] {σ : K ≃+* K}

namespace FlipFrame

variable {n : ℕ} {c d : FlipFrame σ n}

private theorem filter_lt_succ {n j : ℕ} (hj : j < n) :
    (Finset.univ.filter fun l : Fin n => (l : ℕ) < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter fun l : Fin n => (l : ℕ) < j) := by
  ext l
  simp [Fin.ext_iff]
  omega

theorem sub_zero (c : FlipFrame σ n) : c.sub 0 = ⊥ := by
  unfold FlipFrame.sub
  simp

theorem sub_succ (c : FlipFrame σ n) {j : ℕ} (hj : j < n) :
    c.sub (j + 1) = c.sub j ⊔ c.line ⟨j, hj⟩ := by
  unfold FlipFrame.sub
  rw [filter_lt_succ hj, FlipFrame.spanAt_insert, sup_comm]

theorem sub_mono (c : FlipFrame σ n) {j k : ℕ} (h : j ≤ k) : c.sub j ≤ c.sub k := by
  unfold FlipFrame.sub
  refine Finset.sup_le fun l hl => ?_
  exact Finset.le_sup (Finset.mem_filter.mpr
    ⟨Finset.mem_univ l, by rw [Finset.mem_filter] at hl; omega⟩)

theorem line_le_sub (c : FlipFrame σ n) {l : Fin n} {j : ℕ} (h : (l : ℕ) < j) :
    c.line l ≤ c.sub j := by
  unfold FlipFrame.sub
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)

theorem sub_eq_sub_of_line_eq (c d : FlipFrame σ n) {j : ℕ}
    (h : ∀ l : Fin n, (l : ℕ) < j → c.line l = d.line l) :
    c.sub j = d.sub j := by
  unfold FlipFrame.sub
  exact Finset.sup_congr rfl fun l hl => h l (Finset.mem_filter.mp hl).2

theorem sub_of_le (c : FlipFrame σ n) {j : ℕ} (h : n ≤ j) :
    c.sub j = c.spanAt Finset.univ := by
  unfold FlipFrame.sub
  congr 1
  exact Finset.filter_true_of_mem fun l _ => by
    have := l.is_lt
    omega

theorem line_eq_flipOrth_sub_inf (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ n) {j : ℕ}
    (hj : j < n) :
    c.line ⟨j, hj⟩ = flipOrth σ (c.sub j) ⊓ c.sub (j + 1) := by
  unfold FlipFrame.sub
  rw [filter_lt_succ hj]
  exact c.line_eq_flipOrth_inf hσ (by simp)

theorem sub_le_flipOrth (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ n) {j : ℕ} {l : Fin n}
    (h : j ≤ (l : ℕ)) : c.line l ≤ flipOrth σ (c.sub j) := by
  intro y hy
  rw [mem_flipOrth]
  intro x hx
  have hsub : c.sub j ≤ flipOrth σ (c.line l) := by
    unfold FlipFrame.sub
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_filter] at hi
    intro z hz
    rw [mem_flipOrth]
    intro w hw
    have hil : i ≠ l := by
      rintro rfl
      omega
    exact c.flipHerm_eq_zero l i hil.symm w hw z hz
  exact (flipHerm_eq_zero_iff hσ).mp (hsub hx y hy)

variable {m : ℕ}

theorem elt_last (c : FlipFrame σ (m + 1)) : c.elt (Fin.last m) = c.sub (m + 1) := by
  unfold FlipFrame.elt
  rw [if_pos rfl]

theorem elt_of_add_one_eq (c : FlipFrame σ (m + 1)) (i : Fin (m + 1))
    (h : (i : ℕ) + 1 = m) : c.elt i = c.alt := by
  have hi : i ≠ Fin.last m := by
    intro hlast
    rw [hlast] at h
    simp only [Fin.val_last] at h
    omega
  unfold FlipFrame.elt
  rw [if_neg hi, if_pos h]

theorem elt_of_add_one_lt (c : FlipFrame σ (m + 1)) (i : Fin (m + 1))
    (h : (i : ℕ) + 1 < m) : c.elt i = c.sub ((i : ℕ) + 1) := by
  have hi : i ≠ Fin.last m := by
    intro hlast
    rw [hlast] at h
    simp only [Fin.val_last] at h
    omega
  unfold FlipFrame.elt
  rw [if_neg hi, if_neg (by omega)]

theorem alt_eq (c : FlipFrame σ (m + 1)) (hm : 1 ≤ m) :
    c.alt = c.sub (m - 1) ⊔
      (c.line ⟨m - 1, by omega⟩ ⊔ dFlipSub σ (c.line (Fin.last m))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [alt, c.sub_succ (j := k) (by omega), sup_assoc]
  congr 2

private theorem inf_flipOrth_sup_eq (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    {S P : Submodule K (Fin n ⊕ Fin n → K)} (hS : IsFlipflopSub σ S)
    (hP : P ≤ flipOrth σ S) : flipOrth σ S ⊓ (S ⊔ P) = P := by
  have hbot : flipOrth σ S ⊓ S = ⊥ := by
    rw [inf_comm]
    exact inf_flipOrth_eq_bot hσ hS
  have h := inf_sup_assoc_of_le (x := flipOrth σ S) (y := S) (z := P) hP
  rw [hbot, bot_sup_eq] at h
  exact h.symm

theorem line_sup_line_eq (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) (k : Fin m) :
    c.line k.castSucc ⊔ c.line k.succ =
      flipOrth σ (c.sub (k : ℕ)) ⊓ c.sub ((k : ℕ) + 2) := by
  have hk : (k : ℕ) < m + 1 := by omega
  have hcast : (⟨(k : ℕ), hk⟩ : Fin (m + 1)) = k.castSucc := Fin.ext rfl
  have hsucc : (⟨(k : ℕ) + 1, by omega⟩ : Fin (m + 1)) = k.succ := Fin.ext rfl
  have htwo : (k : ℕ) + 2 = (k : ℕ) + 1 + 1 := by omega
  have hB : c.sub ((k : ℕ) + 1) = c.sub (k : ℕ) ⊔ c.line k.castSucc := by
    have h := c.sub_succ (j := (k : ℕ)) hk
    rwa [hcast] at h
  have hC : c.sub ((k : ℕ) + 2) = c.sub ((k : ℕ) + 1) ⊔ c.line k.succ := by
    have h := c.sub_succ (j := (k : ℕ) + 1) (by omega)
    rw [hsucc] at h
    rw [htwo]
    exact h
  have hL : c.line k.castSucc = flipOrth σ (c.sub (k : ℕ)) ⊓ c.sub ((k : ℕ) + 1) := by
    have h := c.line_eq_flipOrth_sub_inf hσ hk
    rwa [hcast] at h
  have hM : c.line k.succ =
      flipOrth σ (c.sub ((k : ℕ) + 1)) ⊓ c.sub ((k : ℕ) + 2) := by
    have h := c.line_eq_flipOrth_sub_inf hσ (j := (k : ℕ) + 1) (by omega)
    rw [hsucc] at h
    rw [htwo]
    exact h
  have hP : c.line k.castSucc ⊔ c.line k.succ ≤ flipOrth σ (c.sub (k : ℕ)) := by
    refine sup_le ?_ ?_
    · exact sub_le_flipOrth hσ c (l := k.castSucc) (by simp)
    · exact sub_le_flipOrth hσ c (l := k.succ) (by
        simp only [Fin.val_succ]
        omega)
  have hC' : c.sub ((k : ℕ) + 2) =
      c.sub (k : ℕ) ⊔ (c.line k.castSucc ⊔ c.line k.succ) := by
    rw [hC, hB, sup_assoc]
  have hRHS : flipOrth σ (c.sub (k : ℕ)) ⊓ c.sub ((k : ℕ) + 2) =
      c.line k.castSucc ⊔ c.line k.succ := by
    rw [hC']
    exact inf_flipOrth_sup_eq hσ (c.isFlipflopSub_sub hσ (k : ℕ)) hP
  exact hRHS.symm

theorem line_sup_dFlipSub_eq (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1))
    (hm : 1 ≤ m) :
    c.line ⟨m - 1, by omega⟩ ⊔ dFlipSub σ (c.line (Fin.last m)) =
      flipOrth σ (c.sub (m - 1)) ⊓ c.alt := by
  have hm1 : m - 1 < m + 1 := by omega
  have hsub : c.sub m = c.sub (m - 1) ⊔ c.line ⟨m - 1, hm1⟩ := by
    simpa [Nat.sub_add_cancel hm] using c.sub_succ (j := m - 1) hm1
  have hW : c.sub (m - 1) ≤ flipOrth σ (dFlipSub σ (c.line (Fin.last m))) := by
    unfold FlipFrame.sub
    refine Finset.sup_le fun l hl => ?_
    rw [Finset.mem_filter] at hl
    intro y hy
    rw [mem_flipOrth]
    intro x hx
    have hdy : dFlip σ x ∈ c.line (Fin.last m) := (mem_dFlipSub hσ).1 hx
    have hne : l ≠ Fin.last m := by
      intro h
      rw [h] at hl
      simp only [Fin.val_last] at hl
      omega
    exact (flipHerm_eq_zero_iff hσ).mpr
      (c.polar_eq_zero l (Fin.last m) hne y hy (dFlip σ x) hdy)
  have hd : dFlipSub σ (c.line (Fin.last m)) ≤ flipOrth σ (c.sub (m - 1)) := by
    intro x hx
    rw [mem_flipOrth]
    intro y hy
    exact (flipHerm_eq_zero_iff hσ).mp (hW hy x hx)
  have hP : c.line ⟨m - 1, hm1⟩ ⊔ dFlipSub σ (c.line (Fin.last m)) ≤
      flipOrth σ (c.sub (m - 1)) :=
    sup_le (sub_le_flipOrth hσ c (l := ⟨m - 1, hm1⟩) (by simp)) hd
  rw [c.alt_eq hm]
  exact (inf_flipOrth_sup_eq hσ (c.isFlipflopSub_sub hσ (m - 1)) hP).symm

private theorem sub_eq_of_elt_eq (hσ : ∀ x, σ (σ x) = x) {m : ℕ}
    {c d : FlipFrame σ (m + 1)} (h : ∀ i : Fin (m + 1), c.elt i = d.elt i) :
    ∀ l : ℕ, l ≤ m + 1 → c.sub l = d.sub l := by
  have hlast : c.elt (Fin.last m) = d.elt (Fin.last m) := h _
  intro l hl
  by_cases hl0 : l = 0
  · rw [hl0, c.sub_zero, d.sub_zero]
  by_cases hlm : l = m
  · rw [hlm]
    have hm : 1 ≤ m := by omega
    have halt : c.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        d.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) := h _
    rw [← c.elt_last_inf_alt hσ, ← d.elt_last_inf_alt hσ]
    rw [show c.alt = c.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) from
          (c.elt_of_add_one_eq _ (by simp; omega)).symm,
      show d.alt = d.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) from
          (d.elt_of_add_one_eq _ (by simp; omega)).symm,
      halt, hlast]
  by_cases hlm1 : l = m + 1
  · rw [hlm1, ← c.elt_last, ← d.elt_last]
    exact hlast
  by_cases hlt : l < m
  · have hlpos : 1 ≤ l := by omega
    let i : Fin (m + 1) := ⟨l - 1, by omega⟩
    have hival : (i : ℕ) + 1 = l := by
      show l - 1 + 1 = l
      omega
    have hilt : (i : ℕ) + 1 < m := by omega
    have hi := h i
    rw [c.elt_of_add_one_lt i hilt, d.elt_of_add_one_lt i hilt] at hi
    rwa [hival] at hi
  · rw [c.sub_of_le (by omega), d.sub_of_le (by omega),
      ← c.sub_of_le (show m + 1 ≤ m + 1 by omega),
      ← d.sub_of_le (show m + 1 ≤ m + 1 by omega),
      ← c.elt_last, ← d.elt_last]
    exact hlast

private theorem sub_eq_of_elt_eq_of_ne (hσ : ∀ x, σ (σ x) = x) {m : ℕ}
    {c d : FlipFrame σ (m + 1)} (k : Fin m)
    (h : ∀ j : Fin (m + 1), j ≠ k.castSucc → c.elt j = d.elt j) :
    ∀ l : ℕ, l ≤ m + 1 → l ≠ (k : ℕ) + 1 → c.sub l = d.sub l := by
  have hlast : c.elt (Fin.last m) = d.elt (Fin.last m) := by
    refine h _ ?_
    intro heq
    have hval := congrArg Fin.val heq
    simp only [Fin.val_last, Fin.val_castSucc] at hval
    omega
  intro l hl hlne
  by_cases hl0 : l = 0
  · rw [hl0, c.sub_zero, d.sub_zero]
  by_cases hlm : l = m
  · rw [hlm]
    have hm : 1 ≤ m := by omega
    have hpos : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ k.castSucc := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hval
      omega
    have halt : c.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        d.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) := h _ hpos
    rw [← c.elt_last_inf_alt hσ, ← d.elt_last_inf_alt hσ]
    rw [show c.alt = c.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) from
          (c.elt_of_add_one_eq _ (by simp; omega)).symm,
      show d.alt = d.elt (⟨m - 1, by omega⟩ : Fin (m + 1)) from
          (d.elt_of_add_one_eq _ (by simp; omega)).symm,
      halt, hlast]
  by_cases hlm1 : l = m + 1
  · rw [hlm1, ← c.elt_last, ← d.elt_last]
    exact hlast
  by_cases hlt : l < m
  · have hlpos : 1 ≤ l := by omega
    let i : Fin (m + 1) := ⟨l - 1, by omega⟩
    have hival : (i : ℕ) + 1 = l := by
      show l - 1 + 1 = l
      omega
    have hilt : (i : ℕ) + 1 < m := by omega
    have hine : i ≠ k.castSucc := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hval
      change l - 1 = (k : ℕ) at hval
      omega
    have hi := h i hine
    rw [c.elt_of_add_one_lt i hilt, d.elt_of_add_one_lt i hilt] at hi
    rwa [hival] at hi
  · rw [c.sub_of_le (by omega), d.sub_of_le (by omega),
      ← c.sub_of_le (show m + 1 ≤ m + 1 by omega),
      ← d.sub_of_le (show m + 1 ≤ m + 1 by omega),
      ← c.elt_last, ← d.elt_last]
    exact hlast

private theorem sub_eq_of_line_eq_of_sup_eq {m : ℕ} {c d : FlipFrame σ (m + 1)} (k : Fin m)
    (hline : ∀ j : Fin (m + 1), j ≠ k.castSucc → j ≠ k.succ →
      c.line j = d.line j)
    (hsup : c.line k.castSucc ⊔ c.line k.succ =
      d.line k.castSucc ⊔ d.line k.succ) :
    (∀ l : ℕ, l ≤ (k : ℕ) → c.sub l = d.sub l) ∧
      (∀ l : ℕ, (k : ℕ) + 2 ≤ l → c.sub l = d.sub l) := by
  have hle : ∀ l : ℕ, l ≤ (k : ℕ) → c.sub l = d.sub l := by
    intro l hl
    refine c.sub_eq_sub_of_line_eq d fun j hj => ?_
    refine hline j ?_ ?_
    · intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hval
      omega
    · intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_succ] at hval
      omega
  have hge : ∀ l : ℕ, (k : ℕ) + 2 ≤ l → c.sub l = d.sub l := by
    have hcast : (⟨(k : ℕ), by omega⟩ : Fin (m + 1)) = k.castSucc := Fin.ext rfl
    have hsucc : (⟨(k : ℕ) + 1, by omega⟩ : Fin (m + 1)) = k.succ := Fin.ext rfl
    have htwo : (k : ℕ) + 2 = (k : ℕ) + 1 + 1 := by omega
    have hB : c.sub ((k : ℕ) + 1) = c.sub (k : ℕ) ⊔ c.line k.castSucc := by
      have h := c.sub_succ (j := (k : ℕ)) (by omega)
      rwa [hcast] at h
    have hBd : d.sub ((k : ℕ) + 1) = d.sub (k : ℕ) ⊔ d.line k.castSucc := by
      have h := d.sub_succ (j := (k : ℕ)) (by omega)
      rwa [hcast] at h
    have hC : c.sub ((k : ℕ) + 2) = c.sub ((k : ℕ) + 1) ⊔ c.line k.succ := by
      have h := c.sub_succ (j := (k : ℕ) + 1) (by omega)
      rw [hsucc] at h
      rw [htwo]
      exact h
    have hCd : d.sub ((k : ℕ) + 2) = d.sub ((k : ℕ) + 1) ⊔ d.line k.succ := by
      have h := d.sub_succ (j := (k : ℕ) + 1) (by omega)
      rw [hsucc] at h
      rw [htwo]
      exact h
    have hbase : c.sub ((k : ℕ) + 2) = d.sub ((k : ℕ) + 2) := by
      rw [hC, hB, hCd, hBd, hle (k : ℕ) le_rfl, sup_assoc, sup_assoc, hsup]
    have hstep : ∀ l : ℕ, (k : ℕ) + 2 ≤ l → c.sub l = d.sub l →
        c.sub (l + 1) = d.sub (l + 1) := by
      intro l hl ih
      by_cases hlm : l < m + 1
      · have hline_l : c.line (⟨l, hlm⟩ : Fin (m + 1)) =
            d.line (⟨l, hlm⟩ : Fin (m + 1)) := by
          refine hline ⟨l, hlm⟩ ?_ ?_
          · intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_castSucc] at hval
            omega
          · intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_succ] at hval
            omega
        rw [c.sub_succ hlm, d.sub_succ hlm, ih, hline_l]
      · have h1 : c.sub (l + 1) = c.spanAt Finset.univ := c.sub_of_le (by omega)
        have h2 : d.sub (l + 1) = d.spanAt Finset.univ := d.sub_of_le (by omega)
        have h3 : c.sub l = c.spanAt Finset.univ := c.sub_of_le (by omega)
        have h4 : d.sub l = d.spanAt Finset.univ := d.sub_of_le (by omega)
        rw [h1, h2, ← h3, ← h4]
        exact ih
    intro l hl
    exact Nat.le_induction hbase hstep l hl
  exact ⟨hle, hge⟩

theorem eq_of_elt_eq (hσ : ∀ x, σ (σ x) = x) {m : ℕ} {c d : FlipFrame σ (m + 1)}
    (h : ∀ i : Fin (m + 1), c.elt i = d.elt i) : c = d := by
  have hsub := sub_eq_of_elt_eq hσ h
  apply FlipFrame.ext
  funext j
  change c.line (⟨j.val, j.is_lt⟩ : Fin (m + 1)) =
    d.line (⟨j.val, j.is_lt⟩ : Fin (m + 1))
  rw [line_eq_flipOrth_sub_inf hσ c j.is_lt,
    line_eq_flipOrth_sub_inf hσ d j.is_lt,
    hsub (j : ℕ) (by omega), hsub ((j : ℕ) + 1) (by omega)]

theorem elt_eq_elt_iff_castSucc (hσ : ∀ x, σ (σ x) = x) {m : ℕ}
    {c d : FlipFrame σ (m + 1)} (k : Fin m) :
    (∀ j : Fin (m + 1), j ≠ k.castSucc → c.elt j = d.elt j) ↔
      (∀ j : Fin (m + 1), j ≠ k.castSucc → j ≠ k.succ → c.line j = d.line j) ∧
        c.line k.castSucc ⊔ c.line k.succ = d.line k.castSucc ⊔ d.line k.succ := by
  constructor
  · intro h
    have hsub := sub_eq_of_elt_eq_of_ne hσ k h
    refine ⟨?_, ?_⟩
    · intro j hj1 hj2
      have hjeta : j = (⟨j.val, j.is_lt⟩ : Fin (m + 1)) := Fin.ext rfl
      have h1 : (j : ℕ) ≠ (k : ℕ) + 1 := by
        intro heq
        exact hj2 (Fin.ext (by simpa using heq))
      have h2 : (j : ℕ) + 1 ≠ (k : ℕ) + 1 := by
        intro heq
        apply hj1
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      rw [hjeta, line_eq_flipOrth_sub_inf hσ c j.is_lt,
        line_eq_flipOrth_sub_inf hσ d j.is_lt,
        hsub (j : ℕ) (by omega) h1, hsub ((j : ℕ) + 1) (by omega) h2]
    · rw [line_sup_line_eq hσ c k, line_sup_line_eq hσ d k,
        hsub (k : ℕ) (by omega) (by omega),
        hsub ((k : ℕ) + 2) (by omega) (by omega)]
  · rintro ⟨hline, hsup⟩ j hj
    have hsub := sub_eq_of_line_eq_of_sup_eq (σ := σ) k hline hsup
    have hle := hsub.1
    have hge := hsub.2
    by_cases hlt : (j : ℕ) < (k : ℕ)
    · have h1 : (j : ℕ) + 1 < m := by omega
      rw [c.elt_of_add_one_lt j h1, d.elt_of_add_one_lt j h1]
      exact hle ((j : ℕ) + 1) (by omega)
    by_cases heq : (j : ℕ) = (k : ℕ) + 1
    · have hj_eq : j = k.succ := Fin.ext (by simpa using heq)
      subst hj_eq
      by_cases hlastj : (k : ℕ) + 1 = m
      · have hls : k.succ = Fin.last m := Fin.ext (by simpa using hlastj)
        rw [hls, c.elt_last, d.elt_last]
        exact hge (m + 1) (by omega)
      by_cases hlt2 : (k : ℕ) + 2 < m
      · have h1 : ((k.succ : Fin (m + 1)) : ℕ) + 1 < m := by
          simp only [Fin.val_succ]
          omega
        rw [c.elt_of_add_one_lt k.succ h1, d.elt_of_add_one_lt k.succ h1]
        exact hge ((k : ℕ) + 2) le_rfl
      · have h2 : ((k.succ : Fin (m + 1)) : ℕ) + 1 = m := by
          simp only [Fin.val_succ]
          omega
        rw [c.elt_of_add_one_eq k.succ h2, d.elt_of_add_one_eq k.succ h2]
        have hm : 1 ≤ m := by omega
        have hp : (⟨m - 1, by omega⟩ : Fin (m + 1)) = k.succ := Fin.ext (by
          simp only [Fin.val_succ]
          omega)
        have hBc : c.sub (m - 1) = c.sub (k : ℕ) ⊔ c.line k.castSucc := by
          have h := c.sub_succ (j := (k : ℕ)) (by omega)
          have hcast : (⟨(k : ℕ), by omega⟩ : Fin (m + 1)) = k.castSucc := Fin.ext rfl
          rw [hcast] at h
          rw [show m - 1 = (k : ℕ) + 1 by omega]
          exact h
        have hBd : d.sub (m - 1) = d.sub (k : ℕ) ⊔ d.line k.castSucc := by
          have h := d.sub_succ (j := (k : ℕ)) (by omega)
          have hcast : (⟨(k : ℕ), by omega⟩ : Fin (m + 1)) = k.castSucc := Fin.ext rfl
          rw [hcast] at h
          rw [show m - 1 = (k : ℕ) + 1 by omega]
          exact h
        have hlast : c.line (Fin.last m) = d.line (Fin.last m) := by
          refine hline _ ?_ ?_
          · intro hh
            have hval := congrArg Fin.val hh
            simp only [Fin.val_last, Fin.val_castSucc] at hval
            omega
          · intro hh
            have hval := congrArg Fin.val hh
            simp only [Fin.val_last, Fin.val_succ] at hval
            omega
        have hL : c.alt = c.sub (k : ℕ) ⊔ (c.line k.castSucc ⊔ c.line k.succ) ⊔
            dFlipSub σ (c.line (Fin.last m)) := by
          rw [c.alt_eq hm, hBc, hp]
          ac_rfl
        have hR : d.alt = d.sub (k : ℕ) ⊔ (d.line k.castSucc ⊔ d.line k.succ) ⊔
            dFlipSub σ (d.line (Fin.last m)) := by
          rw [d.alt_eq hm, hBd, hp]
          ac_rfl
        rw [hL, hR, hle (k : ℕ) le_rfl, hsup, hlast]
    · have hgt : (k : ℕ) + 1 < (j : ℕ) := by
        have hjne : (j : ℕ) ≠ (k : ℕ) := by
          intro hh
          exact hj (Fin.ext (by simpa using hh))
        omega
      by_cases hlastj : j = Fin.last m
      · rw [hlastj, c.elt_last, d.elt_last]
        exact hge (m + 1) (by omega)
      by_cases hltj : (j : ℕ) + 1 < m
      · rw [c.elt_of_add_one_lt j hltj, d.elt_of_add_one_lt j hltj]
        exact hge ((j : ℕ) + 1) (by omega)
      · have hjeq : (j : ℕ) + 1 = m := by
          have hjlt : (j : ℕ) < m := by
            have hne : (j : ℕ) ≠ m := by
              intro hh
              exact hlastj (Fin.ext (by simpa using hh))
            omega
          omega
        rw [c.elt_of_add_one_eq j hjeq, d.elt_of_add_one_eq j hjeq]
        have hm : 1 ≤ m := by omega
        have hline_j : c.line (⟨m - 1, by omega⟩ : Fin (m + 1)) =
            d.line (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
          refine hline _ ?_ ?_
          · intro hh
            have hval := congrArg Fin.val hh
            simp only [Fin.val_castSucc] at hval
            omega
          · intro hh
            have hval := congrArg Fin.val hh
            simp only [Fin.val_succ] at hval
            omega
        have hline_last : c.line (Fin.last m) = d.line (Fin.last m) := by
          refine hline _ ?_ ?_
          · intro hh
            have hval := congrArg Fin.val hh
            simp only [Fin.val_last, Fin.val_castSucc] at hval
            omega
          · intro hh
            have hval := congrArg Fin.val hh
            simp only [Fin.val_last, Fin.val_succ] at hval
            omega
        rw [c.alt_eq hm, d.alt_eq hm, hge (m - 1) (by omega), hline_j, hline_last]

theorem elt_eq_elt_iff_last (hσ : ∀ x, σ (σ x) = x) {m : ℕ} (hm : 1 ≤ m)
    {c d : FlipFrame σ (m + 1)} :
    (∀ j : Fin (m + 1), j ≠ Fin.last m → c.elt j = d.elt j) ↔
      (∀ j : Fin (m + 1), (j : ℕ) + 1 < m → c.line j = d.line j) ∧
        c.line ⟨m - 1, by omega⟩ ⊔ dFlipSub σ (c.line (Fin.last m)) =
          d.line ⟨m - 1, by omega⟩ ⊔ dFlipSub σ (d.line (Fin.last m)) := by
  constructor
  · intro h
    have hsub : ∀ l : ℕ, l ≤ m - 1 → c.sub l = d.sub l := by
      intro l hl
      by_cases hl0 : l = 0
      · rw [hl0, c.sub_zero, d.sub_zero]
      · have hlpos : 1 ≤ l := by omega
        have hlt : l < m := by omega
        let i : Fin (m + 1) := ⟨l - 1, by omega⟩
        have hival : (i : ℕ) + 1 = l := by
          show l - 1 + 1 = l
          omega
        have hilt : (i : ℕ) + 1 < m := by omega
        have hine : i ≠ Fin.last m := by
          intro heq
          have hval := congrArg Fin.val heq
          simp only [Fin.val_last] at hval
          change l - 1 = m at hval
          omega
        have hi := h i hine
        rw [c.elt_of_add_one_lt i hilt, d.elt_of_add_one_lt i hilt] at hi
        rwa [hival] at hi
    have halt : c.alt = d.alt := by
      have hpos : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [Fin.val_last] at hval
        omega
      have hi := h _ hpos
      rw [c.elt_of_add_one_eq _ (by simp; omega),
        d.elt_of_add_one_eq _ (by simp; omega)] at hi
      exact hi
    refine ⟨?_, ?_⟩
    · intro j hj
      have hjeta : j = (⟨j.val, j.is_lt⟩ : Fin (m + 1)) := Fin.ext rfl
      rw [hjeta, line_eq_flipOrth_sub_inf hσ c j.is_lt,
        line_eq_flipOrth_sub_inf hσ d j.is_lt,
        hsub (j : ℕ) (by omega), hsub ((j : ℕ) + 1) (by omega)]
    · rw [line_sup_dFlipSub_eq hσ c hm, line_sup_dFlipSub_eq hσ d hm,
        hsub (m - 1) le_rfl, halt]
  · rintro ⟨hline, hplane⟩ j hj
    have hsub : ∀ l : ℕ, l ≤ m - 1 → c.sub l = d.sub l := by
      intro l hl
      refine c.sub_eq_sub_of_line_eq d fun i hi => hline i ?_
      omega
    by_cases hlt : (j : ℕ) < m - 1
    · have h1 : (j : ℕ) + 1 < m := by omega
      rw [c.elt_of_add_one_lt j h1, d.elt_of_add_one_lt j h1]
      exact hsub ((j : ℕ) + 1) (by omega)
    by_cases heq : (j : ℕ) = m - 1
    · have h2 : (j : ℕ) + 1 = m := by omega
      rw [c.elt_of_add_one_eq j h2, d.elt_of_add_one_eq j h2,
        c.alt_eq hm, d.alt_eq hm, hsub (m - 1) le_rfl, hplane]
    · exfalso
      have hval : (j : ℕ) = m := by omega
      exact hj (Fin.ext (by simpa using hval))

end FlipFrame

end CFSG.ClassicalInvolution.PhanDn

end
