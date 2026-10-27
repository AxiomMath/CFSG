module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmL43Cert
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2c
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Out
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.L43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 HBlocks TBlocks PSpL
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc Certificates.L43TwinQ8
  CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TL4
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {𝕜 : Type} [Field 𝕜]

theorem det_X1_one : (X1 (1 : 𝕜)).det = 1 := by
  rw [X1_eq_bd, det_bd, det_smul, det_smul, det_one]
  norm_num

variable (𝕜) in
@[expose] def X0 : SL(4, 𝕜) := ⟨X1 (1 : 𝕜), det_X1_one⟩

theorem X0_mul_one : ((X0 𝕜 : SL(4, 𝕜)) : Matrix (Fin 4) (Fin 4) 𝕜) *
    ((1 : GL (Fin 4) 𝕜) : Matrix (Fin 4) (Fin 4) 𝕜) =
      ((1 : GL (Fin 4) 𝕜) : Matrix (Fin 4) (Fin 4) 𝕜) * X1 (1 : 𝕜) := by
  rw [Units.val_one, Matrix.mul_one, Matrix.one_mul]
  rfl

theorem coe_bdHom_one (x : SL(2, 𝕜) × SL(2, 𝕜)) :
    ((bdHom 1 x : SL(4, 𝕜)) : Matrix (Fin 4) (Fin 4) 𝕜) =
      bd (x.1 : Matrix (Fin 2) (Fin 2) 𝕜) (x.2 : Matrix (Fin 2) (Fin 2) 𝕜) := by
  rw [coe_bdHom, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem smul_bd (c : 𝕜) (a b : Matrix (Fin 2) (Fin 2) 𝕜) : c • bd a b = bd (c • a) (c • b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

variable [CharP 𝕜 3]

variable (𝕜) in
theorem three_eq_zero' : (3 : 𝕜) = 0 := by exact_mod_cast CharP.cast_eq_zero 𝕜 3

variable (𝕜) in
@[expose] def qI : SL(2, 𝕜) := OrthQ8.sl2I

variable (𝕜) in
@[expose] noncomputable def qJ : SL(2, 𝕜) := OrthQ8.sl2J (three_eq_zero' 𝕜)

theorem coe_qI : ((qI 𝕜 : SL(2, 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) = !![0, 1; -1, 0] := rfl

theorem coe_qJ : ((qJ 𝕜 : SL(2, 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) = !![1, 1; 1, -1] := rfl

theorem ev_eq_conj_of_mA {x : Array ℕ} (hv : eltValid 4 x = true) (he : eE 4 x = 0)
    (G : SL(4, 𝕜)) (hG : mA 4 𝕜 x = (G : Matrix (Fin 4) (Fin 4) 𝕜)) :
    ev 4 𝕜 x = MulAut.conj (proj 4 𝕜 G) := by
  have hu : unitA 4 𝕜 x = Matrix.SpecialLinearGroup.toGL G :=
    Units.ext (by rw [unitA_val hv, hG]; rfl)
  unfold ev
  rw [he, pow_zero, mul_one, hu, conjAut_toGL]

theorem mA_t0 : mA 4 𝕜 t0 = X1 (1 : 𝕜) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, eA, t0, X1, two_eq_neg_one 𝕜]

theorem mA_q1a : mA 4 𝕜 q1a = bd !![0, 1; -1, 0] 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, eA, q1a, bd, two_eq_neg_one 𝕜]

theorem mA_q1b : mA 4 𝕜 q1b = bd !![1, 1; 1, -1] 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, eA, q1b, bd, two_eq_neg_one 𝕜]

theorem mA_q2a : mA 4 𝕜 q2a = bd 1 !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, eA, q2a, bd, two_eq_neg_one 𝕜]

theorem mA_q2b : mA 4 𝕜 q2b = bd 1 !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, eA, q2b, bd, two_eq_neg_one 𝕜]

theorem tw_eq (hc : CheckFacts) : tw 𝕜 = MulAut.conj (proj 4 𝕜 (X0 𝕜)) :=
  ev_eq_conj_of_mA hc.t0_valid (by decide) (X0 𝕜) mA_t0

theorem ev_q1a (hc : CheckFacts) :
    ev 4 𝕜 q1a = MulAut.conj (proj 4 𝕜 (bdHom 1 (qI 𝕜, 1))) :=
  ev_eq_conj_of_mA hc.q1a_valid (by decide) _ (by
    rw [coe_bdHom_one, mA_q1a, coe_qI, Matrix.SpecialLinearGroup.coe_one])

theorem ev_q1b (hc : CheckFacts) :
    ev 4 𝕜 q1b = MulAut.conj (proj 4 𝕜 (bdHom 1 (qJ 𝕜, 1))) :=
  ev_eq_conj_of_mA hc.q1b_valid (by decide) _ (by
    rw [coe_bdHom_one, mA_q1b, coe_qJ, Matrix.SpecialLinearGroup.coe_one])

theorem ev_q2a (hc : CheckFacts) :
    ev 4 𝕜 q2a = MulAut.conj (proj 4 𝕜 (bdHom 1 (1, qI 𝕜))) :=
  ev_eq_conj_of_mA hc.q2a_valid (by decide) _ (by
    rw [coe_bdHom_one, mA_q2a, coe_qI, Matrix.SpecialLinearGroup.coe_one])

theorem ev_q2b (hc : CheckFacts) :
    ev 4 𝕜 q2b = MulAut.conj (proj 4 𝕜 (bdHom 1 (1, qJ 𝕜))) :=
  ev_eq_conj_of_mA hc.q2b_valid (by decide) _ (by
    rw [coe_bdHom_one, mA_q2b, coe_qJ, Matrix.SpecialLinearGroup.coe_one])

theorem eq_bd_of_comm_blockQ8 (h2 : (2 : 𝕜) ≠ 0) {N : Matrix (Fin 4) (Fin 4) 𝕜} (hN : N.det ≠ 0)
    {c d : 𝕜} (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hi : bd 1 !![0, 1; -1, 0] * N = c • (N * bd 1 !![0, 1; -1, 0]))
    (hj : bd 1 !![1, 1; 1, -1] * N = d • (N * bd 1 !![1, 1; 1, -1])) :
    N = bd (ul N) (N 2 2 • 1) := by
  have E := fun k l => congrFun (congrFun hi k) l
  have F := fun k l => congrFun (congrFun hj k) l
  have hc2 : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
  have e00 : N 0 0 = c * N 0 0 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 0 0
  have e01 : N 0 1 = c * N 0 1 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 0 1
  have e02 : N 0 2 = c * -N 0 3 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 0 2
  have e03 : N 0 3 = c * N 0 2 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 0 3
  have e12 : N 1 2 = c * -N 1 3 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 1 2
  have e13 : N 1 3 = c * N 1 2 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 1 3
  have e20 : N 3 0 = c * N 2 0 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 2 0
  have e21 : N 3 1 = c * N 2 1 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 2 1
  have e22 : N 3 2 = c * -N 2 3 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 2 2
  have e23 : N 3 3 = c * N 2 2 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 2 3
  have e30 : -N 2 0 = c * N 3 0 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 3 0
  have e31 : -N 2 1 = c * N 3 1 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using E 3 1
  have f00 : N 0 0 = d * N 0 0 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using F 0 0
  have f01 : N 0 1 = d * N 0 1 := by simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using F 0 1
  have f22 : N 2 2 + N 3 2 = d * (N 2 2 + N 2 3) := by
    simpa [bd, Matrix.mul_apply, Fin.sum_univ_four] using F 2 2
  have two_mul_eq : ∀ x : 𝕜, 2 * x = 0 → x = 0 := fun x hx => (mul_eq_zero.mp hx).resolve_left h2
  have n02 : N 0 2 = 0 := two_mul_eq _ (by linear_combination e02 - c * e03 - N 0 2 * hc2)
  have n03 : N 0 3 = 0 := by rw [e03, n02, mul_zero]
  have n12 : N 1 2 = 0 := two_mul_eq _ (by linear_combination e12 - c * e13 - N 1 2 * hc2)
  have n13 : N 1 3 = 0 := by rw [e13, n12, mul_zero]
  have n20 : N 2 0 = 0 := two_mul_eq _ (by linear_combination -e30 - c * e20 - N 2 0 * hc2)
  have n30 : N 3 0 = 0 := by rw [e20, n20, mul_zero]
  have n21 : N 2 1 = 0 := two_mul_eq _ (by linear_combination -e31 - c * e21 - N 2 1 * hc2)
  have n31 : N 3 1 = 0 := by rw [e21, n21, mul_zero]
  have row0 : N 0 0 = 0 → N 0 1 = 0 → False := fun h0 h1 =>
    hN (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by
      fin_cases j
      · exact h0
      · exact h1
      · exact n02
      · exact n03)
  have hc1 : c = 1 := by
    rcases hc with hc | hc
    · exact hc
    · exfalso
      rw [hc] at e00 e01
      exact row0 (two_mul_eq _ (by linear_combination e00)) (two_mul_eq _ (by linear_combination e01))
  have hd1 : d = 1 := by
    rcases hd with hd | hd
    · exact hd
    · exfalso
      rw [hd] at f00 f01
      exact row0 (two_mul_eq _ (by linear_combination f00)) (two_mul_eq _ (by linear_combination f01))
  rw [hc1] at e22 e23
  rw [hd1] at f22
  have n23 : N 2 3 = 0 := two_mul_eq _ (by linear_combination e22 - f22)
  have n32 : N 3 2 = 0 := by rw [e22, n23]; ring
  have n33 : N 3 3 = N 2 2 := by rw [e23, one_mul]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [bd, ul, n02, n03, n12, n13, n20, n30, n21, n31, n23, n32, n33]

theorem eq_one_or_neg_one_of_ne_zero [Fintype 𝕜] (hK3 : Fintype.card 𝕜 = 3) {c : 𝕜} (hc : c ≠ 0) :
    c = 1 ∨ c = -1 := by
  rcases Q3L4.eq_zero_or_eq_one_or_eq_neg_one hK3 c with h | h | h
  · exact absurd h hc
  · exact Or.inl h
  · exact Or.inr h

theorem exists_sign_of_proj_eq [Fintype 𝕜] (hK3 : Fintype.card 𝕜 = 3) {A B : SL(4, 𝕜)}
    (h : proj 4 𝕜 A = proj 4 𝕜 B) :
    ∃ c : 𝕜, (c = 1 ∨ c = -1) ∧ (B : Matrix (Fin 4) (Fin 4) 𝕜) = c • (A : Matrix (Fin 4) (Fin 4) 𝕜) := by
  obtain ⟨c, hc⟩ := InvClassL.eq_smul_of_proj_eq h
  refine ⟨c, eq_one_or_neg_one_of_ne_zero hK3 ?_, hc⟩
  rintro rfl
  have hd := congrArg Matrix.det hc
  rw [zero_smul, Matrix.det_zero, Matrix.SpecialLinearGroup.det_coe] at hd
  exact one_ne_zero hd

theorem eq_inl_of_comm [Fintype 𝕜] (hK3 : Fintype.card 𝕜 = 3) (g : projectiveSL 4 𝕜)
    (hi : g * proj 4 𝕜 (bdHom 1 (1, qI 𝕜)) = proj 4 𝕜 (bdHom 1 (1, qI 𝕜)) * g)
    (hj : g * proj 4 𝕜 (bdHom 1 (1, qJ 𝕜)) = proj 4 𝕜 (bdHom 1 (1, qJ 𝕜)) * g) :
    ∃ a : SL(2, 𝕜), g = proj 4 𝕜 (bdHom 1 (a, 1)) := by
  obtain ⟨G, rfl⟩ := proj_surjective 4 𝕜 g
  have h2 : (2 : 𝕜) ≠ 0 := Q3L4.two_ne_zero' hK3
  rw [← map_mul, ← map_mul] at hi hj
  obtain ⟨c, hc, hci⟩ := exists_sign_of_proj_eq hK3 hi
  obtain ⟨d, hd, hdj⟩ := exists_sign_of_proj_eq hK3 hj
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_bdHom_one, coe_qI, coe_qJ,
    Matrix.SpecialLinearGroup.coe_one] at hci hdj
  have hdet : (G : Matrix (Fin 4) (Fin 4) 𝕜).det = 1 := G.2
  have hG := eq_bd_of_comm_blockQ8 h2 (by rw [hdet]; exact one_ne_zero) hc hd hci hdj
  set x : 𝕜 := (G : Matrix (Fin 4) (Fin 4) 𝕜) 2 2 with hx
  have hdx : (ul (G : Matrix (Fin 4) (Fin 4) 𝕜)).det * x ^ 2 = 1 := by
    have h1 := congrArg Matrix.det hG
    rw [det_bd, det_smul, det_one, mul_one, Fintype.card_fin, hdet] at h1
    exact h1.symm
  have hx0 : x ≠ 0 := by
    rintro h0
    rw [h0] at hdx
    simp at hdx
  have hx2 : x ^ 2 = 1 := by
    rcases eq_one_or_neg_one_of_ne_zero hK3 hx0 with h | h <;> rw [h] <;> norm_num
  have hdA : (x • ul (G : Matrix (Fin 4) (Fin 4) 𝕜)).det = 1 := by
    rw [det_smul, Fintype.card_fin, mul_comm, hdx]
  refine ⟨⟨x • ul (G : Matrix (Fin 4) (Fin 4) 𝕜), hdA⟩, ?_⟩
  refine (Q3L4.proj_eq_of_smul hx0 ?_).symm
  rw [coe_bdHom_one, Matrix.SpecialLinearGroup.coe_one]
  change (G : Matrix (Fin 4) (Fin 4) 𝕜) = x • bd (x • ul (G : Matrix (Fin 4) (Fin 4) 𝕜)) 1
  rw [smul_bd, smul_smul, ← sq, hx2, one_smul]
  exact hG

theorem swap_conj (a b : SL(2, 𝕜)) :
    proj 4 𝕜 (Q3L4.swP 1) * proj 4 𝕜 (bdHom 1 (a, b)) * proj 4 𝕜 (Q3L4.swP 1) =
      proj 4 𝕜 (bdHom 1 (b, a)) := by
  rw [← map_mul, ← map_mul, Q3L4.swP_conj]

theorem swap_mul_swap : proj 4 𝕜 (Q3L4.swP 1) * proj 4 𝕜 (Q3L4.swP 1) = 1 := by
  rw [← map_mul, Q3L4.swP_mul_swP, map_one]

theorem eq_inr_of_comm [Fintype 𝕜] (hK3 : Fintype.card 𝕜 = 3) (g : projectiveSL 4 𝕜)
    (hi : g * proj 4 𝕜 (bdHom 1 (qI 𝕜, 1)) = proj 4 𝕜 (bdHom 1 (qI 𝕜, 1)) * g)
    (hj : g * proj 4 𝕜 (bdHom 1 (qJ 𝕜, 1)) = proj 4 𝕜 (bdHom 1 (qJ 𝕜, 1)) * g) :
    ∃ a : SL(2, 𝕜), g = proj 4 𝕜 (bdHom 1 (1, a)) := by
  set s := proj 4 𝕜 (Q3L4.swP (1 : GL (Fin 4) 𝕜)) with hs
  have hss : s * s = 1 := swap_mul_swap
  have hsw : ∀ x y : projectiveSL 4 𝕜, x * y = y * x → (s * x * s) * (s * y * s) =
      (s * y * s) * (s * x * s) := by
    intro x y hxy
    calc (s * x * s) * (s * y * s) = s * x * (s * s) * y * s := by group
      _ = s * (x * y) * s := by rw [hss]; group
      _ = s * (y * x) * s := by rw [hxy]
      _ = s * y * (s * s) * x * s := by rw [hss]; group
      _ = (s * y * s) * (s * x * s) := by group
  have hi' := hsw _ _ hi
  have hj' := hsw _ _ hj
  rw [swap_conj] at hi' hj'
  obtain ⟨a, ha⟩ := eq_inl_of_comm hK3 _ hi' hj'
  refine ⟨a, ?_⟩
  calc g = s * (s * g * s) * s := by
        calc g = (s * s) * g * (s * s) := by rw [hss]; group
          _ = s * (s * g * s) * s := by group
    _ = s * proj 4 𝕜 (bdHom 1 (a, 1)) * s := by rw [ha]
    _ = proj 4 𝕜 (bdHom 1 (1, a)) := swap_conj a 1

theorem noOddNormal_centralizer_X0 [Fintype 𝕜] (hK3 : Fintype.card 𝕜 = 3) :
    NoOddNormal (Subgroup.centralizer ({proj 4 𝕜 (X0 𝕜)} : Set (projectiveSL 4 𝕜))) := by
  intro M hMC hMn hMo
  set C := Subgroup.centralizer ({proj 4 𝕜 (X0 𝕜)} : Set (projectiveSL 4 𝕜)) with hCdef
  set H := ((proj 4 𝕜).comp (bdHom (1 : GL (Fin 4) 𝕜))).range with hH
  have hX := X0_mul_one (𝕜 := 𝕜)
  have hHC : H ≤ C := Q5L4.range_bdHom_le_centralizer 1 hX
  have hHn : ∀ g ∈ C, ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun g hg =>
    Q3L4.conj_mem_range_L4 hK3 hX g (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hMn' := (Subgroup.normal_subgroupOf_iff hMC).mp hMn
  have hKodd : GorensteinWalter.IsOddPrimePower (Nat.card 𝕜) :=
    ⟨3, 1, Nat.prime_three, ⟨1, rfl⟩, le_rfl, by rw [Nat.card_eq_fintype_card, hK3, pow_one]⟩
  have hMH : M ⊓ H = ⊥ := by
    refine Q5L4.noOddNormal_range_bdHom hKodd 1 (M ⊓ H) inf_le_right ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro x k hx hk
      exact ⟨hMn' x k hx.1 (hHC hk), H.mul_mem (H.mul_mem hk hx.2) (H.inv_mem hk)⟩
    · exact hMo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hcomm : ∀ m ∈ M, ∀ x ∈ H, m * x = x * m := by
    intro m hm x hx
    have h1 : m * x * m⁻¹ * x⁻¹ ∈ M ⊓ H := by
      refine ⟨?_, H.mul_mem (hHn m (hMC hm) x hx) (H.inv_mem hx)⟩
      have : m * (x * m⁻¹ * x⁻¹) ∈ M := M.mul_mem hm (hMn' _ x (M.inv_mem hm) (hHC hx))
      rwa [show m * (x * m⁻¹ * x⁻¹) = m * x * m⁻¹ * x⁻¹ by group] at this
    rw [hMH, Subgroup.mem_bot] at h1
    calc m * x = (m * x * m⁻¹ * x⁻¹) * x * m := by group
      _ = x * m := by rw [h1, one_mul]
  have hu1 : proj 4 𝕜 (X0 𝕜) ≠ 1 := by
    rw [← Q3L4.proj_bdHom_neg_one hX, Ne, Q3L4.ker_bdHom_iff hK3]
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact Q3L4.neg_one_ne_one hK3 h
    · exact Q3L4.neg_one_ne_one hK3 h.symm
  have hu2 : proj 4 𝕜 (X0 𝕜) ^ 2 = 1 := by
    rw [← Q3L4.proj_bdHom_neg_one hX, ← map_pow, ← map_pow, Prod.pow_mk, neg_one_sq, one_pow,
      Prod.mk_one_one, map_one, map_one]
  have hord : orderOf (proj 4 𝕜 (X0 𝕜)) = 2 := orderOf_eq_prime hu2 hu1
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  rcases Q3L4.eq_of_comm_range_L4 hK3 hX m (fun x hx => hcomm m hm x hx) with h | h
  · exact h
  · exfalso
    have hdvd : orderOf m ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hm
    rw [h, hord] at hdvd
    obtain ⟨k, hk⟩ := hMo
    omega

theorem sq_mem_inner [Finite 𝕜] (h𝕜 : Nat.card 𝕜 = 3) (α : MulAut (projectiveSL 4 𝕜)) :
    α ^ 2 ∈ (MulAut.conj : projectiveSL 4 𝕜 →* MulAut (projectiveSL 4 𝕜)).range := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := 𝕜) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  rw [fieldAut_eq_one h𝕜 σ, mul_one]
  interval_cases ε
  · rw [pow_zero, mul_one, ← map_pow]
    refine LinearOut.conjAut_mem_range_of_det (A ^ 2) 1 ?_
    rw [map_pow, one_pow]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rcases unit_eq_one_or_neg 𝕜 h𝕜 (GeneralLinearGroup.det A) with h | h <;> rw [h] <;> norm_num
  · rw [pow_one]
    exact Q5L4.sq_conjAut_mul_dualAut_mem_inner A

theorem mem_inner_of_odd [Finite 𝕜] (h𝕜 : Nat.card 𝕜 = 3) {α : MulAut (projectiveSL 4 𝕜)}
    (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : projectiveSL 4 𝕜 →* MulAut (projectiveSL 4 𝕜)).range := by
  obtain ⟨m, hm⟩ := hα
  have e : α = (α ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf α + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact pow_mem (sq_mem_inner h𝕜 α) _

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.L43
