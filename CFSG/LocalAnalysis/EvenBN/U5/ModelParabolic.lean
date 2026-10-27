module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4End

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

theorem U_col_e₁ {u : hypSU h 2 1} (hu : u ∈ hypUnitriangular h 2 1) (x : HypIndex 2 1) :
    mat u x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁ := by
  obtain ⟨⟨d1, -, -, -, -⟩, ⟨l1, l2, l3, l4, -, -, -, -, -, -⟩⟩ := U_entries hu
  rcases x with i | k | i <;> (try fin_cases i) <;> (try fin_cases k) <;> simp_all [one_apply]

theorem mul_col_e₁ {g : hypSU h 2 1}
    (hg : ∀ x, mat g x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁)
    (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (x : HypIndex 2 1) :
    (M * mat g) x ιe₁ = M x ιe₁ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun y _ hy => by
      rw [hg y, one_apply_ne hy, mul_zero]) (by simp), hg, one_apply_eq, mul_one]

theorem inv_col_e₁ {g : hypSU h 2 1}
    (hg : ∀ x, mat g x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁)
    (x : HypIndex 2 1) :
    mat g⁻¹ x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁ := by
  have e := mul_col_e₁ hg (mat g⁻¹) x
  rw [← mat_mul, inv_mul_cancel, mat_one] at e
  exact e.symm

theorem row_f₁_of_col_e₁ {g : hypSU h 2 1}
    (hg : ∀ x, mat g x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁)
    (b : HypIndex 2 1) :
    mat g ιf₁ b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) ιf₁ b := by
  have e := mat_inv_apply g⁻¹ ιf₁ b
  rw [inv_inv] at e
  have k2 : (hypPartner b = ιe₁) ↔ (ιf₁ = b) := by
    rw [hypPartner_eq_iff, eq_comm]; rfl
  rw [e, hypPartner_inr_inr, inv_col_e₁ hg, one_apply, one_apply]
  by_cases hb : ιf₁ = b
  · rw [ite_eq_left (k2.2 hb), ite_eq_left hb, map_one]
  · rw [ite_eq_right (fun e => hb (k2.1 e)), ite_eq_right hb, map_zero]

theorem exists_A₂sub_mul_N₂sub {g : hypSU h 2 1}
    (hg : ∀ x, mat g x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁) :
    ∃ a ∈ A₂sub h, ∃ n ∈ N₂sub h, g = a * n := by
  have := h.charP
  have hbb := h.bar_bar
  have hgf := row_f₁_of_col_e₁ hg
  obtain ⟨a, ha, a1, a2, a3⟩ := exists_A₂sub_coord h (h.bar (mat g ιf₂ ιf₁))
    (h.bar (mat g ιz ιf₁)) (h.bar (mat g ιe₂ ιf₁))
  have haU := A₂sub_le_U ha
  obtain ⟨c1, c2, c3⟩ := A₂_rel ha
  have f2 : mat a ιe₂ ιf₁ = mat g ιe₂ ιf₁ := by rw [c3, a3, hbb]
  have fz : mat a ιz ιf₁ = mat g ιz ιf₁ := by rw [c2, a2, hbb]
  have ff2 : mat a ιf₂ ιf₁ = mat g ιf₂ ιf₁ := by rw [c1, a1, hbb]
  have ff1 : mat a ιf₁ ιf₁ = mat g ιf₁ ιf₁ := by rw [U_diag haU, hgf, one_apply_eq]
  set c := mat g ιe₁ ιf₁ - mat a ιe₁ ιf₁ with hc
  set n' := a⁻¹ * g with hn'
  have hn'e : ∀ x, mat n' x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁ := by
    intro x
    rw [hn', mat_mul, mul_col_e₁ hg, U_col_e₁ (inv_mem haU)]
  have hn'f : ∀ x, mat n' x ιf₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιf₁ +
      (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁ * c := by
    intro x
    have e1 : (mat a⁻¹ * mat a) x ιf₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιf₁ := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    rw [Matrix.mul_apply, sum_hypIndex_two] at e1
    rw [hn', mat_mul, Matrix.mul_apply, sum_hypIndex_two, ← U_col_e₁ (inv_mem haU) x, ← f2, ← fz,
      ← ff2, ← ff1, hc]
    linear_combination e1
  have m1 : mat n' ιe₁ ιf₁ = c := by
    rw [hn'f, one_apply_ne (by decide), one_apply_eq, zero_add, one_mul]
  have m2 : mat n' ιe₂ ιf₁ = 0 := by
    rw [hn'f, one_apply_ne (by decide), one_apply_ne (by decide), zero_mul, add_zero]
  have m3 : mat n' ιz ιf₁ = 0 := by
    rw [hn'f, one_apply_ne (by decide), one_apply_ne (by decide), zero_mul, add_zero]
  have m4 : mat n' ιf₁ ιf₁ = 1 := by
    rw [hn'f, one_apply_eq, one_apply_ne (by decide), zero_mul, add_zero]
  have m5 : mat n' ιf₂ ιf₁ = 0 := by
    rw [hn'f, one_apply_ne (by decide), one_apply_ne (by decide), zero_mul, add_zero]
  have hcb : h.bar c = c := by
    have e := congrFun (congrFun (show mat n'⁻¹ * mat n' = 1 by
      rw [← mat_mul, inv_mul_cancel, mat_one]) ιe₁) ιf₁
    rw [Matrix.mul_apply, sum_hypIndex_two, m1, m2, m3, m4, m5, one_apply_ne (by decide)] at e
    simp only [mul_zero, add_zero, mul_one] at e
    rw [mat_inv_apply, mat_inv_apply] at e
    simp only [hypPartner_inl, hypPartner_inr_inr, m1, m4, map_one, one_mul] at e
    exact bar_eq_of_add_eq_zero h e
  set z := zRoot h ⟨c, h.mem_fixedField.2 hcb⟩ with hz
  have hzZ : z ∈ ZPsub h := zRoot_mem _
  have hzz : z * z = 1 := Vsub_sq (ZPsub_le_Vsub hzZ)
  have hzm : mat z = 1 + Matrix.single ιe₁ ιf₁ c := by
    rw [mat_eq_of_mem_ZPsub hzZ, hz, mat_zRoot]
  have hnN : z * n' ∈ N₂sub h := by
    refine mem_N₂sub.2 ⟨fun x => ?_, fun x => ?_⟩
    · rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun y _ hy => by
        rw [hn'e y, one_apply_ne hy, mul_zero]) (by simp), hn'e, one_apply_eq, mul_one,
        U_col_e₁ (Z₂Psub_le_A₂sub (ZPsub_le_Z₂Psub hzZ) |> A₂sub_le_U)]
    · rw [mat_mul, hzm, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
      by_cases hx : x = ιe₁
      · subst hx
        rw [single_mul_apply_same, m1, m4, one_apply_ne (by decide), mul_one,
          CharTwo.add_self_eq_zero]
      · rw [single_mul_apply_of_ne _ _ _ _ _ hx, add_zero, hn'f, one_apply_ne hx, zero_mul,
          add_zero]
  refine ⟨a * z, mul_mem ha (Z₂Psub_le_A₂sub (ZPsub_le_Z₂Psub hzZ)), z * n', hnN, ?_⟩
  calc g = a * (z * z) * (a⁻¹ * g) := by rw [hzz, mul_one, mul_inv_cancel_left]
    _ = a * z * (z * n') := by rw [hn']; group

theorem exists_A₂sub_mul_N₂sub_mul_Isub {g : hypSU h 2 1}
    (hg : ∀ x, x ≠ ιe₁ → mat g x ιe₁ = 0) :
    ∃ a ∈ A₂sub h, ∃ n ∈ N₂sub h, ∃ i ∈ Isub h, g = a * n * i := by
  set l := mat g ιe₁ ιe₁ with hl
  have hl0 : l ≠ 0 := by
    have e := congrFun (congrFun (show mat g⁻¹ * mat g = 1 by
      rw [← mat_mul, inv_mul_cancel, mat_one]) ιe₁) ιe₁
    rw [Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun y _ hy => by rw [hg y hy, mul_zero])
      (by simp), one_apply_eq] at e
    exact right_ne_zero_of_mul_eq_one e
  obtain ⟨i, hi, i1, -⟩ := exists_torus h hl0 one_ne_zero
  have hgi : ∀ x, mat (g * i⁻¹) x ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) x ιe₁ := by
    intro x
    rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun y _ hy => by
      rw [torus_offdiag (inv_mem hi) hy, mul_zero]) (by simp), torus_inv_apply hi, i1]
    by_cases hx : x = ιe₁
    · rw [hx, ← hl, mul_inv_cancel₀ hl0, one_apply_eq]
    · rw [hg x hx, zero_mul, one_apply_ne hx]
  obtain ⟨a, ha, n, hn, he⟩ := exists_A₂sub_mul_N₂sub hgi
  exact ⟨a, ha, n, hn, i, hi, by rw [← he, inv_mul_cancel_right]⟩

theorem act_col_e₁_of_mem_N₂sub {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0)
    {n : hypSU h 2 1} (hn : n ∈ N₂sub h) (b : HypIndex 2 1) :
    mat (actΓ h x n) b ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) b ιe₁ := by
  have hl := lmat_e₁e₁_ne_zero hcol
  have e := congrFun (congrFun (lmat_mul_map x n) b) ιe₁
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun w _ hw => by
      rw [Matrix.map_apply, (mem_N₂sub.1 hn).1 w, one_apply_ne hw, map_zero, mul_zero])
      (by simp),
    Finset.sum_eq_single ιe₁ (fun w _ hw => by rw [hcol w hw, mul_zero]) (by simp),
    Matrix.map_apply, (mem_N₂sub.1 hn).1 ιe₁, one_apply_eq, map_one, mul_one] at e
  by_cases hb : b = ιe₁
  · subst hb
    rw [one_apply_eq]
    exact mul_right_cancel₀ hl (e.symm.trans (one_mul _).symm)
  · rw [hcol b hb] at e
    rw [one_apply_ne hb]
    exact (mul_eq_zero.1 e.symm).resolve_right hl

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.conj_N₂_mem_A₂_sup_N₂ (hd : d.Hyp) {c : G} (hcZ : c ∈ normalizer (d.ZtP : Set G))
    (hcL : c ∈ normalizer (d.L : Set G)) {n : G} (hn : n ∈ d.N₂) :
    c * n * c⁻¹ ∈ d.A₂ ⊔ d.N₂ := by
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  obtain ⟨hcol, -⟩ := hd.lift_flag hcZ hcL hy
  obtain ⟨m, hm, rfl⟩ := hn
  rw [d.conj_η_eq hcL hy]
  obtain ⟨a, ha, n', hn', he⟩ := exists_A₂sub_mul_N₂sub (act_col_e₁_of_mem_N₂sub hcol hm)
  rw [he, map_mul]
  exact mul_mem (mem_sup_left ⟨a, ha, rfl⟩) (mem_sup_right ⟨n', hn', rfl⟩)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
