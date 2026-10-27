module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812MatDefs
public import CFSG.RankThree.PartTwo.KFacts.K74Bloom

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.P812

open CFSG.RankThree.PartTwo.KFacts (glEquiv glEquiv_apply)
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem caseB_mem_cline_iff (i : Fin 3) (v : Fin 3 → ZMod 3) :
    v ∈ cline i ↔ ∀ j, j ≠ i → v j = 0 := by
  unfold cline
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩ j hj
    simp [ev, Pi.single_apply, hj]
  · intro h
    refine ⟨v i, ?_⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [ev]
    · simp [ev, Pi.single_apply, hj, h j hj]

theorem caseB_mem_cplane_iff (i : Fin 3) (v : Fin 3 → ZMod 3) : v ∈ cplane i ↔ v i = 0 := by
  unfold cplane
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      simp [ev, Pi.single_apply, Ne.symm hj]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  · intro h
    have hv : v = ∑ j, v j • ev j := by
      ext l
      simp [ev, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp [h]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

theorem caseB_mulVec_apply_fin_three (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (v : Fin 3 → ZMod 3)
    (i : Fin 3) : (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem caseB_mulVec_ev_apply (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (i j : Fin 3) :
    (M *ᵥ ev j) i = M i j := by
  simp [ev, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem caseB_two_mul_add_self (x : ZMod 3) : 2 * (x + x) = x := by
  revert x
  decide

theorem caseB_smul_ev_mem {W : Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hA : ∀ x ∈ W, (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    (hB : ∀ x ∈ W, (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    {v : Fin 3 → ZMod 3} (hv : v ∈ W) (i : Fin 3) : v i • ev i ∈ W := by
  have h1 : v 1 • ev 1 ∈ W := by
    have h := W.smul_mem (2 : ZMod 3) (W.sub_mem hv (hA v hv))
    convert h using 1
    ext j
    fin_cases j <;> simp [dA_mulVec, ev, Matrix.vecHead, Matrix.vecTail, caseB_two_mul_add_self]
  have h2 : v 2 • ev 2 ∈ W := by
    have h := W.smul_mem (2 : ZMod 3) (W.sub_mem hv (hB v hv))
    convert h using 1
    ext j
    fin_cases j <;> simp [dB_mulVec, ev, Matrix.vecHead, Matrix.vecTail, caseB_two_mul_add_self]
  have h0 : v 0 • ev 0 ∈ W := by
    have h := W.sub_mem (W.sub_mem hv h1) h2
    convert h using 1
    ext j
    fin_cases j <;> simp [ev]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem caseB_ev_mem_of_apply_ne {W : Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hA : ∀ x ∈ W, (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    (hB : ∀ x ∈ W, (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    {v : Fin 3 → ZMod 3} (hv : v ∈ W) {i : Fin 3} (hi : v i ≠ 0) : ev i ∈ W := by
  have h := W.smul_mem (v i)⁻¹ (caseB_smul_ev_mem hA hB hv i)
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at h

theorem caseB_apply_eq_zero_of_ev_not_mem {W : Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hA : ∀ x ∈ W, (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    (hB : ∀ x ∈ W, (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    {v : Fin 3 → ZMod 3} (hv : v ∈ W) {i : Fin 3} (hi : ev i ∉ W) : v i = 0 := by
  by_contra h
  exact hi (caseB_ev_mem_of_apply_ne hA hB hv h)

theorem caseB_stab_of_invariant {W : Submodule (ZMod 3) (Fin 3 → ZMod 3)} (hbot : W ≠ ⊥)
    (htop : W ≠ ⊤)
    (hA : ∀ x ∈ W, (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    (hB : ∀ x ∈ W, (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    (hξ : ∀ x ∈ W,
      ((xiK 1 (by decide) : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x ∈ W)
    {g : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hg : ∀ x ∈ W, g *ᵥ x ∈ W)
    (hn1 : g 0 1 ≠ 0 ∨ g 2 1 ≠ 0) (hn2 : g 0 2 ≠ 0 ∨ g 1 2 ≠ 0) (hn3 : g 0 1 ≠ 0 ∨ g 0 2 ≠ 0) :
    g 2 0 = 0 ∧ g 2 1 = 0 := by
  have hent : ∀ i j : Fin 3, ev j ∈ W → ev i ∉ W → g i j = 0 := by
    intro i j hj hi
    have := caseB_apply_eq_zero_of_ev_not_mem hA hB (hg _ hj) hi
    rwa [caseB_mulVec_ev_apply] at this
  have hall : (∀ i, ev i ∈ W) → False := by
    intro h
    apply htop
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ j, v j • ev j := by
      ext l
      simp [ev, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => W.smul_mem _ (h j)
  have hnone : (∀ i, ev i ∉ W) → False := by
    intro h
    apply hbot
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    funext i
    exact caseB_apply_eq_zero_of_ev_not_mem hA hB hv (h i)
  by_cases h0 : ev 0 ∈ W
  · have h1 : ev 1 ∈ W := by
      have h := W.sub_mem (hξ _ h0) h0
      rw [xiK_mulVec] at h
      have e : ev 0 + (ev 0) 0 • ev 1 - ev 0 = ev 1 := by simp [ev]
      rwa [e] at h
    by_cases h2 : ev 2 ∈ W
    · exact (hall fun i => by fin_cases i <;> assumption).elim
    · exact ⟨hent 2 0 h0 h2, hent 2 1 h1 h2⟩
  · by_cases h1 : ev 1 ∈ W <;> by_cases h2 : ev 2 ∈ W
    · exfalso
      rcases hn3 with h | h
      · exact h (hent 0 1 h1 h0)
      · exact h (hent 0 2 h2 h0)
    · exfalso
      rcases hn1 with h | h
      · exact h (hent 0 1 h1 h0)
      · exact h (hent 2 1 h1 h2)
    · exfalso
      rcases hn2 with h | h
      · exact h (hent 0 2 h2 h0)
      · exact h (hent 1 2 h2 h1)
    · exact (hnone fun i => by fin_cases i <;> assumption).elim

@[expose] def caseB_rU (u : ZMod 3 × ZMod 3) : GL (Fin 3) (ZMod 3) where
  val := !![1, 0, u.1; 0, 1, u.2; 0, 0, 1]
  inv := !![1, 0, -u.1; 0, 1, -u.2; 0, 0, 1]
  val_inv := by
    rw [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem caseB_rU_val (u : ZMod 3 × ZMod 3) :
    ((caseB_rU u : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      !![1, 0, u.1; 0, 1, u.2; 0, 0, 1] := rfl

theorem caseB_rU_add (u v : ZMod 3 × ZMod 3) : caseB_rU (u + v) = caseB_rU u * caseB_rU v := by
  ext1
  rw [Units.val_mul, caseB_rU_val, caseB_rU_val, caseB_rU_val, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem caseB_rU_zero : caseB_rU 0 = 1 := by
  ext1
  rw [caseB_rU_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem caseB_dA_val : ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
    !![1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dA, Matrix.diagonal_apply]

theorem caseB_dB_val : ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
    !![1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dB, Matrix.diagonal_apply]

theorem caseB_xiK_one_val :
    ((xiK 1 (by decide) : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      !![1, 0, 0; 1, 1, 0; 0, 0, 1] := by
  rw [xiK_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem caseB_xiK_two_val :
    ((xiK 2 (by decide) : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      !![1, 0, 0; 0, 1, 0; 1, 0, 1] := by
  rw [xiK_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem caseB_mat_conj_rU (a b c d p₀ p₁ s u₀ u₁ : ZMod 3) (hs : s * s = 1) :
    (!![a, b, p₀; c, d, p₁; 0, 0, s] : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        !![1, 0, u₀; 0, 1, u₁; 0, 0, 1] =
      !![1, 0, s * (a * u₀ + b * u₁); 0, 1, s * (c * u₀ + d * u₁); 0, 0, 1] *
        !![a, b, p₀; c, d, p₁; 0, 0, s] := by
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-(a * u₀ + b * u₁)) * hs
  · linear_combination (-(c * u₀ + d * u₁)) * hs

theorem caseB_mat_comm_dB (a b c d p₀ p₁ s : ZMod 3) (hs : s * s = 1) :
    (!![a, b, p₀; c, d, p₁; 0, 0, s] : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        !![1, 0, 0; 0, 1, 0; 0, 0, -1] =
      !![1, 0, -(s * p₀); 0, 1, -(s * p₁); 0, 0, 1] * !![1, 0, 0; 0, 1, 0; 0, 0, -1] *
        !![a, b, p₀; c, d, p₁; 0, 0, s] := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-p₀) * hs + (-p₀) * h3
  · linear_combination (-p₁) * hs + (-p₁) * h3

theorem caseB_val_eq_of_stab (h : GL (Fin 3) (ZMod 3)) (h20 : h.val 2 0 = 0) (h21 : h.val 2 1 = 0) :
    (h.val : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      !![h.val 0 0, h.val 0 1, h.val 0 2; h.val 1 0, h.val 1 1, h.val 1 2; 0, 0, h.val 2 2] := by
  have e := Matrix.eta_fin_three (h.val : Matrix (Fin 3) (Fin 3) (ZMod 3))
  rw [h20, h21] at e
  exact e

theorem caseB_entry22_mul_self (h : GL (Fin 3) (ZMod 3)) (h20 : h.val 2 0 = 0)
    (h21 : h.val 2 1 = 0) : h.val 2 2 * h.val 2 2 = 1 := by
  have h22 : h.val 2 2 ≠ 0 := by
    intro h0
    have e := congrFun (congrFun h.val_inv 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, h0] at e
  generalize h.val 2 2 = s at h22 ⊢
  revert s
  decide

@[expose] def caseB_actR (h : GL (Fin 3) (ZMod 3)) (u : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (h.val 2 2 * (h.val 0 0 * u.1 + h.val 0 1 * u.2),
    h.val 2 2 * (h.val 1 0 * u.1 + h.val 1 1 * u.2))

theorem caseB_conj_rU (h : GL (Fin 3) (ZMod 3)) (h20 : h.val 2 0 = 0) (h21 : h.val 2 1 = 0)
    (u : ZMod 3 × ZMod 3) : h * caseB_rU u * h⁻¹ = caseB_rU (caseB_actR h u) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext1
  rw [Units.val_mul, Units.val_mul, caseB_rU_val, caseB_rU_val, caseB_val_eq_of_stab h h20 h21]
  exact caseB_mat_conj_rU _ _ _ _ _ _ _ _ _ (caseB_entry22_mul_self h h20 h21)

theorem caseB_comm_dB (g : GL (Fin 3) (ZMod 3)) (h20 : g.val 2 0 = 0) (h21 : g.val 2 1 = 0) :
    g * dB * g⁻¹ * dB⁻¹ = caseB_rU (-(g.val 2 2 * g.val 0 2), -(g.val 2 2 * g.val 1 2)) := by
  rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  ext1
  rw [Units.val_mul, Units.val_mul, Units.val_mul, caseB_rU_val, caseB_dB_val,
    caseB_val_eq_of_stab g h20 h21]
  exact caseB_mat_comm_dB _ _ _ _ _ _ _ (caseB_entry22_mul_self g h20 h21)

def caseB_rSub (H : Subgroup (GL (Fin 3) (ZMod 3))) : Submodule (ZMod 3) (ZMod 3 × ZMod 3) where
  carrier := {u | caseB_rU u ∈ H}
  add_mem' {u v} hu hv := by
    show caseB_rU (u + v) ∈ H
    rw [caseB_rU_add]
    exact H.mul_mem hu hv
  zero_mem' := by
    show caseB_rU 0 ∈ H
    rw [caseB_rU_zero]
    exact H.one_mem
  smul_mem' c u hu := by
    show caseB_rU (c • u) ∈ H
    have hc : c = 0 ∨ c = 1 ∨ c = 2 := by
      revert c
      decide
    rcases hc with rfl | rfl | rfl
    · rw [zero_smul, caseB_rU_zero]
      exact H.one_mem
    · rw [one_smul]
      exact hu
    · rw [two_smul, caseB_rU_add]
      exact H.mul_mem hu hu

theorem caseB_mem_rSub {H : Subgroup (GL (Fin 3) (ZMod 3))} {u : ZMod 3 × ZMod 3} :
    u ∈ caseB_rSub H ↔ caseB_rU u ∈ H := Iff.rfl

theorem caseB_actR_mem {H : Subgroup (GL (Fin 3) (ZMod 3))} {h : GL (Fin 3) (ZMod 3)} (hh : h ∈ H)
    (h20 : h.val 2 0 = 0) (h21 : h.val 2 1 = 0) {u : ZMod 3 × ZMod 3} (hu : u ∈ caseB_rSub H) :
    caseB_actR h u ∈ caseB_rSub H := by
  rw [caseB_mem_rSub, ← caseB_conj_rU h h20 h21]
  exact H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)

theorem caseB_rU_one_zero_mem_of_stab (H : Subgroup (GL (Fin 3) (ZMod 3))) (hB : dB ∈ H)
    (hξ : (xiK 1 (by decide) : GL (Fin 3) (ZMod 3)) ∈ H) {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ H)
    (h20 : g.val 2 0 = 0) (h21 : g.val 2 1 = 0) (hb : g.val 0 1 ≠ 0)
    (hp : g.val 0 2 ≠ 0 ∨ g.val 1 2 ≠ 0) : caseB_rU (1, 0) ∈ H := by
  have hs : g.val 2 2 * g.val 2 2 = 1 := caseB_entry22_mul_self g h20 h21
  have hs0 : g.val 2 2 ≠ 0 := left_ne_zero_of_mul_eq_one hs
  have hu : (-(g.val 2 2 * g.val 0 2), -(g.val 2 2 * g.val 1 2)) ∈ caseB_rSub H := by
    rw [caseB_mem_rSub, ← caseB_comm_dB g h20 h21]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hB) (H.inv_mem hg)) (H.inv_mem hB)
  set u : ZMod 3 × ZMod 3 := (-(g.val 2 2 * g.val 0 2), -(g.val 2 2 * g.val 1 2)) with hu_def
  have hu0 : u ≠ 0 := by
    intro h0
    have e1 : g.val 2 2 * g.val 0 2 = 0 := by simpa [hu_def] using congrArg Prod.fst h0
    have e2 : g.val 2 2 * g.val 1 2 = 0 := by simpa [hu_def] using congrArg Prod.snd h0
    rcases hp with hp | hp
    · exact hp ((mul_eq_zero.mp e1).resolve_left hs0)
    · exact hp ((mul_eq_zero.mp e2).resolve_left hs0)
  have hξ20 : ((xiK 1 (by decide) : GL (Fin 3) (ZMod 3)).val :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 = 0 := by
    rw [caseB_xiK_one_val]
    rfl
  have hξ21 : ((xiK 1 (by decide) : GL (Fin 3) (ZMod 3)).val :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1 = 0 := by
    rw [caseB_xiK_one_val]
    rfl
  have hξu := caseB_actR_mem hξ hξ20 hξ21 hu
  have h01 : ((0 : ZMod 3), u.1) ∈ caseB_rSub H := by
    have h := (caseB_rSub H).sub_mem hξu hu
    convert h using 1
    ext <;> simp [caseB_actR, caseB_xiK_one_val]
  have h1 : ((0 : ZMod 3), (1 : ZMod 3)) ∈ caseB_rSub H := by
    by_cases hu1 : u.1 = 0
    · have hu2 : u.2 ≠ 0 := fun h2 => hu0 (Prod.ext hu1 h2)
      have h := (caseB_rSub H).smul_mem (u.2)⁻¹ hu
      convert h using 1
      ext <;> simp [hu1, inv_mul_cancel₀ hu2]
    · have h := (caseB_rSub H).smul_mem (u.1)⁻¹ h01
      convert h using 1
      ext <;> simp [inv_mul_cancel₀ hu1]
  have hg1 : (g.val 2 2 * g.val 0 1, g.val 2 2 * g.val 1 1) ∈ caseB_rSub H := by
    have h := caseB_actR_mem hg h20 h21 h1
    convert h using 1
    simp [caseB_actR]
  have hg2 : (g.val 2 2 * g.val 0 1, (0 : ZMod 3)) ∈ caseB_rSub H := by
    have h := (caseB_rSub H).sub_mem hg1 ((caseB_rSub H).smul_mem (g.val 2 2 * g.val 1 1) h1)
    convert h using 1
    ext <;> simp
  have hc : g.val 2 2 * g.val 0 1 ≠ 0 := mul_ne_zero hs0 hb
  have h := (caseB_rSub H).smul_mem (g.val 2 2 * g.val 0 1)⁻¹ hg2
  have e : (g.val 2 2 * g.val 0 1)⁻¹ • (g.val 2 2 * g.val 0 1, (0 : ZMod 3)) = (1, 0) := by
    refine Prod.ext ?_ ?_
    · show (g.val 2 2 * g.val 0 1)⁻¹ * (g.val 2 2 * g.val 0 1) = 1
      exact inv_mul_cancel₀ hc
    · show (g.val 2 2 * g.val 0 1)⁻¹ * 0 = 0
      exact mul_zero _
  rw [e] at h
  exact h

theorem caseB_rU_one_zero_mem_of_irreducible (H : Subgroup (GL (Fin 3) (ZMod 3)))
    (hξ : (xiK 1 (by decide) : GL (Fin 3) (ZMod 3)) ∈ H)
    (hirr : ∀ W : Submodule (ZMod 3) (Fin 3 → ZMod 3),
      (∀ g ∈ H, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    caseB_rU (1, 0) ∈ H := by
  set G : Subgroup ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :=
    H.comap (glEquiv.symm : _ ≃* _).toMonoidHom with hG
  have hmem : ∀ x : GL (Fin 3) (ZMod 3), glEquiv x ∈ G ↔ x ∈ H := by
    intro x
    simp [hG, Subgroup.mem_comap]
  have hirrG : ∀ W : Submodule (ZMod 3) (Fin 3 → ZMod 3),
      (∀ g ∈ G, ∀ x ∈ W, g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hirr W
    intro g hg w hw
    have := hW (glEquiv g) ((hmem g).mpr hg) w hw
    rwa [glEquiv_apply] at this
  have hr : CFSG.RankThree.Classical.IsTransvectionWith (glEquiv (xiK 1 (by decide))) (ev 1)
      (LinearMap.proj 0 : Module.Dual (ZMod 3) (Fin 3 → ZMod 3)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 1
      simp [ev] at this
    · intro h
      have := LinearMap.congr_fun h (ev 0)
      simp [ev] at this
    · simp [ev]
    · intro x
      rw [glEquiv_apply, xiK_mulVec]
      rfl
  have hdet : LinearMap.det (((glEquiv (caseB_rU (1, 0)) :
      (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :
      (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3))) = 1 := by
    have hlin : ((glEquiv (caseB_rU (1, 0)) : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :
        (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3)) = Matrix.toLin' (caseB_rU (1, 0)).val := by
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, ← glEquiv_apply]
      rfl
    rw [hlin, LinearMap.det_toLin', caseB_rU_val]
    simp [Matrix.det_fin_three]
  have h := CFSG.RankThree.PartTwo.Sec3.det_eq_one_mem_of_irreducible
    (Module.finrank_fin_fun (ZMod 3)) G hirrG ((hmem _).mpr hξ) hr _ hdet
  exact (hmem _).mp h

theorem caseB_core_one (H : Subgroup (GL (Fin 3) (ZMod 3))) (hA : dA ∈ H) (hB : dB ∈ H)
    (hξ : (xiK 1 (by decide) : GL (Fin 3) (ZMod 3)) ∈ H) {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ H)
    (hn1 : g.val 0 1 ≠ 0 ∨ g.val 2 1 ≠ 0) (hn2 : g.val 0 2 ≠ 0 ∨ g.val 1 2 ≠ 0)
    (hn3 : g.val 0 1 ≠ 0 ∨ g.val 0 2 ≠ 0) : caseB_rU (1, 0) ∈ H := by
  by_cases hirr : ∀ W : Submodule (ZMod 3) (Fin 3 → ZMod 3),
      (∀ g ∈ H, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤
  · exact caseB_rU_one_zero_mem_of_irreducible H hξ hirr
  · push Not at hirr
    obtain ⟨W, hW, hbot, htop⟩ := hirr
    obtain ⟨h20, h21⟩ := caseB_stab_of_invariant hbot htop (hW dA hA) (hW dB hB) (hW _ hξ)
      (hW g hg) hn1 hn2 hn3
    have hb : g.val 0 1 ≠ 0 := by
      rcases hn1 with h | h
      · exact h
      · exact absurd h21 h
    exact caseB_rU_one_zero_mem_of_stab H hB hξ hg h20 h21 hb hn2

@[expose] def caseB_swp : GL (Fin 3) (ZMod 3) where
  val := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  inv := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  val_inv := by
    rw [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem caseB_swp_val :
    (caseB_swp : GL (Fin 3) (ZMod 3)).val = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl

theorem caseB_swp_inv_val :
    ((caseB_swp : GL (Fin 3) (ZMod 3))⁻¹).val = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl

theorem caseB_swp_dA : caseB_swp * dA * caseB_swp⁻¹ = dB := by
  ext1
  rw [Units.val_mul, Units.val_mul, caseB_swp_val, caseB_swp_inv_val, caseB_dA_val,
    caseB_dB_val, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem caseB_swp_dB : caseB_swp * dB * caseB_swp⁻¹ = dA := by
  ext1
  rw [Units.val_mul, Units.val_mul, caseB_swp_val, caseB_swp_inv_val, caseB_dA_val,
    caseB_dB_val, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem caseB_swp_xiK : caseB_swp * xiK 1 (by decide) * caseB_swp⁻¹ = xiK 2 (by decide) := by
  ext1
  rw [Units.val_mul, Units.val_mul, caseB_swp_val, caseB_swp_inv_val, caseB_xiK_one_val,
    caseB_xiK_two_val, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem caseB_swp_rU :
    (caseB_swp * caseB_rU (1, 0) * caseB_swp⁻¹).val = !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  rw [Units.val_mul, Units.val_mul, caseB_swp_val, caseB_swp_inv_val, caseB_rU_val,
    Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def caseB_conjSwp (H : Subgroup (GL (Fin 3) (ZMod 3))) : Subgroup (GL (Fin 3) (ZMod 3)) :=
  H.comap (MulAut.conj (caseB_swp : GL (Fin 3) (ZMod 3))).toMonoidHom

theorem caseB_mem_conjSwp {H : Subgroup (GL (Fin 3) (ZMod 3))} {x : GL (Fin 3) (ZMod 3)} :
    x ∈ caseB_conjSwp H ↔ caseB_swp * x * caseB_swp⁻¹ ∈ H := Iff.rfl

theorem caseB_swp_conj_val (g : GL (Fin 3) (ZMod 3)) :
    (caseB_swp⁻¹ * g * caseB_swp).val =
      !![g.val 0 0, g.val 0 2, g.val 0 1; g.val 2 0, g.val 2 2, g.val 2 1;
        g.val 1 0, g.val 1 2, g.val 1 1] := by
  rw [Units.val_mul, Units.val_mul, caseB_swp_val, caseB_swp_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp

theorem caseB_core_two (H : Subgroup (GL (Fin 3) (ZMod 3))) (hA : dA ∈ H) (hB : dB ∈ H)
    (hξ : (xiK 2 (by decide) : GL (Fin 3) (ZMod 3)) ∈ H) {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ H)
    (hn1 : g.val 0 1 ≠ 0 ∨ g.val 2 1 ≠ 0) (hn2 : g.val 0 2 ≠ 0 ∨ g.val 1 2 ≠ 0)
    (hn3 : g.val 0 1 ≠ 0 ∨ g.val 0 2 ≠ 0) : caseB_swp * caseB_rU (1, 0) * caseB_swp⁻¹ ∈ H := by
  have hg' : caseB_swp⁻¹ * g * caseB_swp ∈ caseB_conjSwp H := by
    rw [caseB_mem_conjSwp]
    have e : caseB_swp * (caseB_swp⁻¹ * g * caseB_swp) * caseB_swp⁻¹ = g := by group
    rw [e]
    exact hg
  have e01 : (caseB_swp⁻¹ * g * caseB_swp).val 0 1 = g.val 0 2 := by
    rw [caseB_swp_conj_val]
    rfl
  have e21 : (caseB_swp⁻¹ * g * caseB_swp).val 2 1 = g.val 1 2 := by
    rw [caseB_swp_conj_val]
    rfl
  have e02 : (caseB_swp⁻¹ * g * caseB_swp).val 0 2 = g.val 0 1 := by
    rw [caseB_swp_conj_val]
    rfl
  have e12 : (caseB_swp⁻¹ * g * caseB_swp).val 1 2 = g.val 2 1 := by
    rw [caseB_swp_conj_val]
    rfl
  have h := caseB_core_one (caseB_conjSwp H) (by rw [caseB_mem_conjSwp, caseB_swp_dA]; exact hB)
    (by rw [caseB_mem_conjSwp, caseB_swp_dB]; exact hA)
    (by rw [caseB_mem_conjSwp, caseB_swp_xiK]; exact hξ) hg'
    (by rw [e01, e21]; exact hn2) (by rw [e02, e12]; exact hn1)
    (by rw [e01, e02]; exact hn3.symm)
  exact caseB_mem_conjSwp.mp h

theorem caseB_entries_of_hw {g : GL (Fin 3) (ZMod 3)}
    (h1 : ¬ ∀ w ∈ cline 1, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline 1)
    (h2 : ¬ ∀ w ∈ cline 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline 2)
    (h3 : ¬ ∀ w ∈ cplane 0, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cplane 0) :
    (g.val 0 1 ≠ 0 ∨ g.val 2 1 ≠ 0) ∧ (g.val 0 2 ≠ 0 ∨ g.val 1 2 ≠ 0) ∧
      (g.val 0 1 ≠ 0 ∨ g.val 0 2 ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply h1
    intro w hw
    rw [caseB_mem_cline_iff] at hw ⊢
    intro j hj
    rw [caseB_mulVec_apply_fin_three]
    have hw0 := hw 0 (by decide)
    have hw2 := hw 2 (by decide)
    fin_cases j
    · simp [hw0, hw2, h.1]
    · exact (hj rfl).elim
    · simp [hw0, hw2, h.2]
  · by_contra h
    push Not at h
    apply h2
    intro w hw
    rw [caseB_mem_cline_iff] at hw ⊢
    intro j hj
    rw [caseB_mulVec_apply_fin_three]
    have hw0 := hw 0 (by decide)
    have hw1 := hw 1 (by decide)
    fin_cases j
    · simp [hw0, hw1, h.1]
    · simp [hw0, hw1, h.2]
    · exact (hj rfl).elim
  · by_contra h
    push Not at h
    apply h3
    intro w hw
    rw [caseB_mem_cplane_iff] at hw ⊢
    rw [caseB_mulVec_apply_fin_three]
    simp [hw, h.1, h.2]

theorem caseB_matrix
    (H : Subgroup (GL (Fin 3) (ZMod 3))) (k : Fin 3) (hk : k ≠ 0) (hk12 : k = 1 ∨ k = 2)
    (hA : dA ∈ H) (hB : dB ∈ H) (hξ : xiK k hk ∈ H)
    (hw : ∃ g ∈ H,
        ¬ (∀ w ∈ cline 1, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline 1) ∧
        ¬ (∀ w ∈ cline 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline 2) ∧
        ¬ (∀ w ∈ cplane 0, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cplane 0))
    (hstar : ∀ g ∈ H, ∀ j : Fin 3, (j = 1 ∨ j = 2) →
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev j = ev j →
        (∀ w ∈ cline 1, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline 1) ∧
        (∀ w ∈ cline 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline 2)) :
    False := by
  obtain ⟨g, hg, hw1, hw2, hw3⟩ := hw
  obtain ⟨hn1, hn2, hn3⟩ := caseB_entries_of_hw hw1 hw2 hw3
  rcases hk12 with rfl | rfl
  · have hr := caseB_core_one H hA hB hξ hg hn1 hn2 hn3
    have hfix : ((caseB_rU (1, 0) : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ
        ev 1 = ev 1 := by
      rw [caseB_rU_val]
      decide
    have h := (hstar _ hr 1 (Or.inl rfl) hfix).2 (ev 2) (Submodule.mem_span_singleton_self _)
    rw [caseB_mem_cline_iff] at h
    have h0 := h 0 (by decide)
    rw [caseB_mulVec_ev_apply, caseB_rU_val] at h0
    simp at h0
  · have hr := caseB_core_two H hA hB hξ hg hn1 hn2 hn3
    have hfix : ((caseB_swp * caseB_rU (1, 0) * caseB_swp⁻¹ : GL (Fin 3) (ZMod 3)) :
        Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 = ev 2 := by
      rw [caseB_swp_rU]
      decide
    have h := (hstar _ hr 2 (Or.inr rfl) hfix).1 (ev 1) (Submodule.mem_span_singleton_self _)
    rw [caseB_mem_cline_iff] at h
    have h0 := h 0 (by decide)
    rw [caseB_mulVec_ev_apply, caseB_swp_rU] at h0
    simp at h0

end CFSG.LocalAnalysis.RankThreeUC.S15.P812
