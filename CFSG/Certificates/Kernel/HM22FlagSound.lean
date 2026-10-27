module

public import Certificates.Data.Kernel.HM22Flag

public section

namespace CFSG.KC.HM22Flag

open CFSG.Quasithin.HM22

theorem all_of_chunks {f : ℕ → Bool} {w m : ℕ} (h : ∀ k < m, chunk f w k = true) :
    ∀ j < w * m, f j = true := by
  intro j hj
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  have hk : j / w < m := (Nat.div_lt_iff_lt_mul hw).2 (by rwa [Nat.mul_comm])
  have := h _ hk
  simp only [chunk, List.all_eq_true, List.mem_range] at this
  have e := this (j % w) (Nat.mod_lt _ hw)
  rwa [Nat.div_add_mod] at e

theorem eqm_of_cols {N : ℕ} {P Pi : PM} (hPi : Pi.length = N)
    (h : ∀ j < N, PV.eqv N (PM.mulVec P (PM.col Pi j)) (PV.single j 1) = true) :
    PM.eqm N (PM.mul P Pi) (PM.idm N) = true := by
  simp only [PM.eqm, PM.mul, PM.idm, Bool.and_eq_true, beq_iff_eq, List.length_map,
    List.length_range, hPi, List.all_eq_true, true_and]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < N := by simp [hPi] at hi; omega
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
  have e := h i hi'
  rwa [PM.col, List.getD_eq_getElem _ _ (by omega)] at e

theorem blockOK_of_cols {N : ℕ} {K P Pi : PM} {ns : List ℕ} {stds : List PM}
    (hP : P.length = N) (hns : ∀ i < ns.length - 1, nsF ns (i + 1) ≤ N)
    (h : ∀ j < N, winOK ns stds j (colT K P Pi j) = true) :
    blockOK (PM.mul Pi (PM.mul K P)) ns stds = true := by
  simp only [blockOK, List.all_eq_true, List.mem_range]
  intro i hi c hc
  have hN := hns i hi
  have hj : nsF ns i + c < N := by omega
  have hcol : PM.col (PM.mul Pi (PM.mul K P)) (nsF ns i + c) = colT K P Pi (nsF ns i + c) := by
    rw [PM.col_mul _ _ _ (by rw [PM.length_mul]; omega), PM.col_mul _ _ _ (by omega)]
    rfl
  have hw := h _ hj
  simp only [winOK, List.all_eq_true, List.mem_range] at hw
  have e := hw i hi
  rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left] at e
  rw [hcol]
  exact e

theorem flagOK_of_cols {N : ℕ} {K₁ K₂ P Pi : PM} {ns : List ℕ} {s₁ s₂ : List PM}
    (hP : P.length = N) (hPi : Pi.length = N) (hns : ∀ i < ns.length - 1, nsF ns (i + 1) ≤ N)
    (hid : ∀ j < N, PV.eqv N (PM.mulVec P (PM.col Pi j)) (PV.single j 1) = true)
    (h₁ : ∀ j < N, winOK ns s₁ j (colT K₁ P Pi j) = true)
    (h₂ : ∀ j < N, winOK ns s₂ j (colT K₂ P Pi j) = true) :
    flagOK N K₁ K₂ P Pi ns s₁ s₂ = true := by
  rw [flagOK, eqm_of_cols hPi hid, blockOK_of_cols hP hns h₁, blockOK_of_cols hP hns h₂]
  simp [hP, hPi]

end CFSG.KC.HM22Flag
