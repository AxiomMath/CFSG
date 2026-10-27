module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Centralizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LieType.PSp43Local

open Matrix CFSG.GH74.Exceptional CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

@[expose] def xMat : SpMat3 :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 0, -1] !![0, 0; 0, 1] !![1, 0; 0, 0]

theorem xMat_mul_transpose : xMat * xMatᵀ = 1 := by
  decide +kernel

theorem transpose_mul_xMat : xMatᵀ * xMat = 1 := by
  decide +kernel

@[expose] def xGL : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨xMat, xMatᵀ, xMat_mul_transpose, transpose_mul_xMat⟩

private theorem xMat_symplectic : xMatᵀ * J4 * xMat = J4 := by
  decide +kernel

theorem xGL_mem : xGL ∈ StatedSp 2 (ZMod 3) := by
  rw [StatedAPI.mem_statedSp_iff]
  exact xMat_symplectic

@[expose] noncomputable def xPSp : PSp43 :=
  QuotientGroup.mk ⟨xGL, xGL_mem⟩

theorem xPSp_conj_a :
    xPSp * uPSp (Multiplicative.ofAdd (1, 0, 0)) * xPSp⁻¹ =
      uPSp (Multiplicative.ofAdd (1, 0, 0)) := by
  rw [xPSp, uPSp_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  show xMat * uMat (1, 0, 0) * xMatᵀ = uMat (1, 0, 0)
  decide +kernel

theorem xPSp_conj_b :
    xPSp * uPSp (Multiplicative.ofAdd (0, 1, 0)) * xPSp⁻¹ = (levPSp 1)⁻¹ := by
  rw [xPSp, uPSp_apply, levPSp, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  rw [eq_inv_iff_mul_eq_one]
  apply Subtype.ext
  apply Units.ext
  show xMat * uMat (0, 1, 0) * xMatᵀ * (levGL 1 : SpMat3) = 1
  decide +kernel

theorem xPSp_conj_t : xPSp * levPSp 1 * xPSp⁻¹ = uPSp (Multiplicative.ofAdd (0, 1, 0)) := by
  rw [xPSp, uPSp_apply, levPSp, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  show xMat * (levGL 1 : SpMat3) * xMatᵀ = uMat (0, 1, 0)
  decide +kernel

theorem uPSp_b_mul_levPSp_one_pow_three :
    (uPSp (Multiplicative.ofAdd (0, 1, 0)) * levPSp 1) ^ 3 = 1 := by
  rw [uPSp_apply, levPSp, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  have h : (uSpHom (Multiplicative.ofAdd (0, 1, 0)) *
      ⟨levGL 1, levGL_mem 1⟩ : StatedSp 2 (ZMod 3)) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (uMat (0, 1, 0) * (levGL 1 : SpMat3)) ^ 3 = 1
    decide +kernel
  rw [h, QuotientGroup.mk_one]

theorem uPSp_a_mul_levPSp_one_pow_three :
    (uPSp (Multiplicative.ofAdd (1, 0, 0)) * levPSp 1) ^ 3 = 1 := by
  rw [uPSp_apply, levPSp, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  have h : (uSpHom (Multiplicative.ofAdd (1, 0, 0)) *
      ⟨levGL 1, levGL_mem 1⟩ : StatedSp 2 (ZMod 3)) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (uMat (1, 0, 0) * (levGL 1 : SpMat3)) ^ 3 = 1
    decide +kernel
  rw [h, QuotientGroup.mk_one]

theorem levPSp_one_mul_b_ne :
    levPSp 1 * uPSp (Multiplicative.ofAdd (0, 1, 0)) ≠
      uPSp (Multiplicative.ofAdd (0, 1, 0)) * levPSp 1 := by
  intro h
  have hconj : levPSp 1 * uPSp (Multiplicative.ofAdd (0, 1, 0)) * (levPSp 1)⁻¹ =
      uPSp (Multiplicative.ofAdd (0, 1, 0)) := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [levPSp_conj] at hconj
  have hlev : levAct (levA 1) (0, 1, 0) = (2, 1, 0) := by
    decide +kernel
  change uPSp (Multiplicative.ofAdd (levAct (levA 1) (0, 1, 0))) =
    uPSp (Multiplicative.ofAdd (0, 1, 0)) at hconj
  rw [hlev] at hconj
  exact absurd (congrArg Multiplicative.toAdd (uPSp_injective hconj)) (by decide)

theorem levPSp_one_not_mem_E0 : levPSp 1 ∉ E0 := by
  intro h
  have hb : uPSp (Multiplicative.ofAdd (0, 1, 0)) ∈ E0 := ⟨_, rfl⟩
  exact levPSp_one_mul_b_ne (E0_comm h hb)

theorem xPSp_not_mem_normalizer_E0 : xPSp ∉ Subgroup.normalizer (E0 : Set PSp43) := by
  intro hx
  have hb : uPSp (Multiplicative.ofAdd (0, 1, 0)) ∈ E0 := ⟨_, rfl⟩
  have htinv : (levPSp 1)⁻¹ ∈ E0 := by
    have h := (Subgroup.mem_set_normalizer_iff.mp hx)
      (uPSp (Multiplicative.ofAdd (0, 1, 0)))
    rw [xPSp_conj_b] at h
    exact h.mp hb
  exact levPSp_one_not_mem_E0 (by simpa using E0.inv_mem htinv)

private theorem eq_zero_of_swap_mul_eq_zero (C : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (h : !![0, 1; 1, 0] * C = 0) : C = 0 := by
  ext i j
  fin_cases i
  · have := congrFun (congrFun h (1 : Fin 2)) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  · have := congrFun (congrFun h (0 : Fin 2)) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

private theorem exists_blocks_eq_of_commute (A D : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (h1 : A * !![1, 0; 0, 0] = !![1, 0; 0, 0] * D)
    (h2 : A * !![0, 1; 1, 0] = !![0, 1; 1, 0] * D) :
    ∃ l m : ZMod 3, A = !![l, m; 0, l] ∧ D = !![l, 0; m, l] := by
  rw [Matrix.eta_fin_two A, Matrix.eta_fin_two D] at h1 h2
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1 h2
  obtain ⟨⟨h00, h01⟩, h10⟩ := h1
  obtain ⟨⟨h20, h21⟩, h22, h23⟩ := h2
  refine ⟨A 0 0, A 0 1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h22, h00]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h20, h21, ← h00]

private theorem eq_zero_of_two_mul_mul_eq_zero (l m : ZMod 3) (hl : l * l = 1)
    (h : 2 * l * m = 0) : m = 0 := by
  revert l m hl h
  decide

private theorem eq_one_or_eq_neg_one_of_sq_eq_one (l : ZMod 3) (hl : l * l = 1) :
    l = 1 ∨ l = -1 := by
  revert l hl
  decide

private theorem neg_one_fin_two :
    (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := by
  rw [show (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 0; 0, 1] from Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem symM_triple_eq_of_transpose_eq (B : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hB : Bᵀ = B) : symM (B 0 0, B 0 1, B 1 1) = B := by
  have h10 : B 1 0 = B 0 1 := by
    have := congrFun (congrFun hB 0) 1
    simpa [Matrix.transpose_apply] using this
  rw [Matrix.eta_fin_two B]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symM, h10]

private theorem symM_neg_triple_eq_of_transpose_eq (B : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hB : Bᵀ = B) : symM (-(B 0 0), -(B 0 1), -(B 1 1)) = -B := by
  have hB' : (-B)ᵀ = -B := by simpa using congrArg Neg.neg hB
  have := symM_triple_eq_of_transpose_eq (-B) hB'
  simpa using this

private theorem square_eq_one_and_eq_zero_of_symplectic
    (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (l m : ZMod 3)
    (h : (fromBlocks !![l, m; 0, l] B 0 !![l, 0; m, l])ᵀ * J4 *
      fromBlocks !![l, m; 0, l] B 0 !![l, 0; m, l] = J4) :
    l * l = 1 ∧ m = 0 := by
  simp only [J4, fromBlocks_transpose, fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_zero] at h
  obtain ⟨-, hAD, -, -⟩ := fromBlocks_inj.mp h
  have hl : l * l = 1 := by
    have h00 := congrFun (congrFun hAD 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
  have hlm : 2 * l * m = 0 := by
    have h10 := congrFun (congrFun hAD 1) 0
    have h10' : l * m + l * m = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using h10
    calc
      2 * l * m = l * m + l * m := by ring
      _ = 0 := h10'
  exact ⟨hl, eq_zero_of_two_mul_mul_eq_zero l m hl hlm⟩

private theorem transpose_eq_of_symplectic
    (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (l m : ZMod 3) (hl : l * l = 1) (hm : m = 0)
    (h : (fromBlocks !![l, m; 0, l] B 0 !![l, 0; m, l])ᵀ * J4 *
      fromBlocks !![l, m; 0, l] B 0 !![l, 0; m, l] = J4) :
    Bᵀ = B := by
  simp only [J4, fromBlocks_transpose, fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_zero] at h
  obtain ⟨-, -, -, hB⟩ := fromBlocks_inj.mp h
  rw [hm, Matrix.eta_fin_two B] at hB
  have hb01 := congrFun (congrFun hB 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] at hb01
  have hb : B 1 0 = B 0 1 := by
    linear_combination l * hb01 + (B 0 1 - B 1 0) * hl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hb]

private theorem eq_or_eq_neg_uMat_of_commute_of_symplectic
    (M : SpMat3) (hsymp : Mᵀ * J4 * M = J4)
    (h1 : M * uMat (1, 0, 0) = uMat (1, 0, 0) * M)
    (h2 : M * uMat (0, 1, 0) = uMat (0, 1, 0) * M) :
    ∃ s : T3, M = uMat s ∨ M = -uMat s := by
  rw [← fromBlocks_toBlocks M] at hsymp h1 h2 ⊢
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  rw [uMat] at h1 h2
  simp only [symM] at h1 h2
  rw [fromBlocks_multiply, fromBlocks_multiply] at h1 h2
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add] at h1 h2
  obtain ⟨e11, e12, e21, e22⟩ := fromBlocks_inj.mp h1
  obtain ⟨f11, f12, f21, f22⟩ := fromBlocks_inj.mp h2
  have hC : C = 0 := by
    have hSC : !![0, 1; 1, 0] * C = 0 := by
      have := f11
      rwa [left_eq_add] at this
    exact eq_zero_of_swap_mul_eq_zero C hSC
  have hA1 : A * !![1, 0; 0, 0] = !![1, 0; 0, 0] * D := by
    have := e12
    rwa [add_comm B (!![1, 0; 0, 0] * D), add_right_cancel_iff] at this
  have hA2 : A * !![0, 1; 1, 0] = !![0, 1; 1, 0] * D := by
    have := f12
    rwa [add_comm B (!![0, 1; 1, 0] * D), add_right_cancel_iff] at this
  obtain ⟨l, m, hAl, hDl⟩ := exists_blocks_eq_of_commute A D hA1 hA2
  rw [hC, hAl, hDl] at hsymp
  obtain ⟨hl, hm⟩ := square_eq_one_and_eq_zero_of_symplectic B l m hsymp
  have hBt : Bᵀ = B := transpose_eq_of_symplectic B l m hl hm hsymp
  rcases eq_one_or_eq_neg_one_of_sq_eq_one l hl with rfl | rfl
  · refine ⟨(B 0 0, B 0 1, B 1 1), Or.inl ?_⟩
    rw [uMat, hAl, hDl, hC, hm, symM_triple_eq_of_transpose_eq B hBt, ← Matrix.one_fin_two]
  · refine ⟨(-(B 0 0), -(B 0 1), -(B 1 1)), Or.inr ?_⟩
    rw [uMat, hAl, hDl, hC, hm, symM_neg_triple_eq_of_transpose_eq B hBt, fromBlocks_neg,
      neg_one_fin_two]
    simp

private theorem eq_or_eq_neg_of_mk_eq {x y : GL (Fin 2 ⊕ Fin 2) (ZMod 3)}
    (hx : x ∈ StatedSp 2 (ZMod 3)) (hy : y ∈ StatedSp 2 (ZMod 3))
    (h : (QuotientGroup.mk (⟨x, hx⟩ : StatedSp 2 (ZMod 3)) : PSp43) =
      QuotientGroup.mk (⟨y, hy⟩ : StatedSp 2 (ZMod 3))) :
    x = y ∨ x = -y := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hyx : y = x * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    calc
      y = x * (x⁻¹ * y) := by group
      _ = x * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by rw [hc]
  rcases units_zmod_three c with rfl | rfl
  · left
    rw [map_one, mul_one] at hyx
    exact hyx.symm
  · right
    rw [scalar_neg_one, mul_neg_one] at hyx
    calc
      x = -(-x) := (neg_neg x).symm
      _ = -y := by rw [hyx]

private theorem trace_conj (g h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) :
    trace ((g * h * g⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = trace (h : SpMat3) := by
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [trace_mul_cycle]
  simp

private theorem trace_uMat_one_zero_zero : trace (uMat (1, 0, 0) : SpMat3) = 1 := by
  decide +kernel

private theorem trace_uMat_zero_one_zero : trace (uMat (0, 1, 0) : SpMat3) = 1 := by
  decide +kernel

private theorem commute_of_mk_conj_eq (g h : StatedSp 2 (ZMod 3))
    (hconj : (QuotientGroup.mk g : PSp43) * QuotientGroup.mk h * (QuotientGroup.mk g)⁻¹ =
      QuotientGroup.mk h)
    (htrace : trace ((h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = 1) :
    (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) =
      (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) := by
  set x : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
    (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) *
      (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3))⁻¹
  have hx : x ∈ StatedSp 2 (ZMod 3) := by
    dsimp [x]
    exact mul_mem (mul_mem g.2 h.2) (inv_mem g.2)
  have hxeq : (QuotientGroup.mk (⟨x, hx⟩ : StatedSp 2 (ZMod 3)) : PSp43) =
      QuotientGroup.mk h := by
    have hxval : (⟨x, hx⟩ : StatedSp 2 (ZMod 3)) = g * h * g⁻¹ := Subtype.ext rfl
    rw [hxval, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hconj
  rcases eq_or_eq_neg_of_mk_eq hx h.2 hxeq with hx' | hx'
  · have := congrArg (fun z : GL (Fin 2 ⊕ Fin 2) (ZMod 3) =>
      z * (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3))) hx'
    simpa [x, mul_assoc] using this
  · exfalso
    have htr : trace (x : SpMat3) =
        trace ((h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) :=
      trace_conj (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3))
    rw [hx'] at htr
    simp only [Units.val_neg] at htr
    rw [trace_neg, htrace] at htr
    exact absurd htr (by decide)

theorem centralizer_a_b_le_E0 :
    Subgroup.centralizer ({uPSp (Multiplicative.ofAdd (1, 0, 0)),
      uPSp (Multiplicative.ofAdd (0, 1, 0))} : Set PSp43) ≤ E0 := by
  intro g hg
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk'_surjective (N := Z43) (b := g)
  let a0 : StatedSp 2 (ZMod 3) := uSpHom (Multiplicative.ofAdd (1, 0, 0))
  let b0 : StatedSp 2 (ZMod 3) := uSpHom (Multiplicative.ofAdd (0, 1, 0))
  have ha_mem : uPSp (Multiplicative.ofAdd (1, 0, 0)) ∈
      ({uPSp (Multiplicative.ofAdd (1, 0, 0)),
        uPSp (Multiplicative.ofAdd (0, 1, 0))} : Set PSp43) := by simp
  have hb_mem : uPSp (Multiplicative.ofAdd (0, 1, 0)) ∈
      ({uPSp (Multiplicative.ofAdd (1, 0, 0)),
        uPSp (Multiplicative.ofAdd (0, 1, 0))} : Set PSp43) := by simp
  have hga : (QuotientGroup.mk a0 : PSp43) * QuotientGroup.mk g0 =
      QuotientGroup.mk g0 * QuotientGroup.mk a0 := by
    have h := (Subgroup.mem_centralizer_iff.mp hg) _ ha_mem
    simpa [a0, uPSp_apply] using h
  have hgb : (QuotientGroup.mk b0 : PSp43) * QuotientGroup.mk g0 =
      QuotientGroup.mk g0 * QuotientGroup.mk b0 := by
    have h := (Subgroup.mem_centralizer_iff.mp hg) _ hb_mem
    simpa [b0, uPSp_apply] using h
  have hconj_a : (QuotientGroup.mk g0 : PSp43) * QuotientGroup.mk a0 *
      (QuotientGroup.mk g0)⁻¹ = QuotientGroup.mk a0 := by
    rw [← hga, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_b : (QuotientGroup.mk g0 : PSp43) * QuotientGroup.mk b0 *
      (QuotientGroup.mk g0)⁻¹ = QuotientGroup.mk b0 := by
    rw [← hgb, mul_assoc, mul_inv_cancel, mul_one]
  have ha_trace : trace ((a0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = 1 := by
    simpa [a0, uSpHom, uGL] using trace_uMat_one_zero_zero
  have hb_trace : trace ((b0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = 1 := by
    simpa [b0, uSpHom, uGL] using trace_uMat_zero_one_zero
  have hcomm_a := commute_of_mk_conj_eq g0 a0 hconj_a ha_trace
  have hcomm_b := commute_of_mk_conj_eq g0 b0 hconj_b hb_trace
  have hsymp : ((g0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3)ᵀ * J4 *
      ((g0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) = J4 :=
    StatedAPI.mem_statedSp_iff.mp g0.2
  have hma : ((g0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) * uMat (1, 0, 0) =
      uMat (1, 0, 0) * ((g0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) := by
    simpa [a0, uSpHom, uGL] using
      congrArg (fun z : GL (Fin 2 ⊕ Fin 2) (ZMod 3) => (z : SpMat3)) hcomm_a
  have hmb : ((g0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) * uMat (0, 1, 0) =
      uMat (0, 1, 0) * ((g0 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : SpMat3) := by
    simpa [b0, uSpHom, uGL] using
      congrArg (fun z : GL (Fin 2 ⊕ Fin 2) (ZMod 3) => (z : SpMat3)) hcomm_b
  obtain ⟨s, hs | hs⟩ :=
    eq_or_eq_neg_uMat_of_commute_of_symplectic _ hsymp hma hmb
  · refine ⟨Multiplicative.ofAdd s, ?_⟩
    rw [uPSp_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simpa [uSpHom, uGL] using hs.symm
  · refine ⟨Multiplicative.ofAdd s, ?_⟩
    rw [uPSp_apply]
    apply mk_eq_mk_of_eq_neg
    apply Units.ext
    simpa [uSpHom, uGL] using (congrArg Neg.neg hs).symm

end CFSG.LieType.PSp43Local
