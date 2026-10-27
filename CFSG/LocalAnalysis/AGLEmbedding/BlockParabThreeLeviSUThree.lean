module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Fischer.Classification
  CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ζ : F}

@[expose] def heisXMat (ζ : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, ζ, 0; 0, 0, ζ ^ 2]

@[expose] def heisYMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def fourierMatThree (ζ : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 1, 1; 1, ζ, ζ ^ 2; 1, ζ ^ 2, ζ]

section Matrices

variable (hσ : unitaryInvolution F 2 1 ζ = ζ ^ 2) (hs : 1 + ζ + ζ ^ 2 = 0)
include hs

omit [Finite F] in
theorem cube_eq_one_of_sum : ζ ^ 3 = 1 := by
  grind

include hσ in
theorem sigma_sq_of_sum : unitaryInvolution F 2 1 (ζ ^ 2) = ζ := by
  rw [map_pow, hσ]
  grind

include hσ in
theorem heisXMat_mem :
    (heisXMat ζ).det = 1 ∧ conjTr (unitaryInvolution F 2 1) (heisXMat ζ) * heisXMat ζ = 1 := by
  refine ⟨by simp [heisXMat, det_fin_three]; grind, ?_⟩
  rw [heisXMat, conjTr_fin_three]
  simp only [map_one, map_zero, hσ, sigma_sq_of_sum hσ hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind

omit hs in
theorem heisYMat_mem :
    (heisYMat : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      conjTr (unitaryInvolution F 2 1) heisYMat * (heisYMat : Matrix (Fin 3) (Fin 3) F) = 1 := by
  refine ⟨by simp [heisYMat, det_fin_three], ?_⟩
  rw [heisYMat, conjTr_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

include hσ in
theorem fourierMat_mem :
    (fourierMatThree ζ).det = 1 ∧
      conjTr (unitaryInvolution F 2 1) (fourierMatThree ζ) * fourierMatThree ζ = 1 := by
  refine ⟨by simp [fourierMatThree, det_fin_three]; grind, ?_⟩
  rw [fourierMatThree, conjTr_fin_three]
  simp only [map_one, hσ, sigma_sq_of_sum hσ hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind

omit [Finite F] hs in
theorem heis_cube_relations (hs : 1 + ζ + ζ ^ 2 = 0) :
    heisXMat ζ ^ 3 = 1 ∧ (heisYMat : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 ∧
      (heisXMat ζ * heisYMat) ^ 3 = 1 ∧ (heisXMat ζ * (heisYMat * heisYMat)) ^ 3 = 1 ∧
      heisXMat ζ * heisYMat ≠ heisYMat * heisXMat ζ := by
  refine ⟨?_, ?_, ?_, ?_, fun h => ?_⟩
  all_goals first
    | (ext i j
       fin_cases i <;> fin_cases j <;>
         simp [heisXMat, heisYMat, pow_succ, mul_apply, Fin.sum_univ_three] <;> grind)
    | skip
  have := congrFun (congrFun h 1) 0
  simp [heisXMat, heisYMat, mul_apply, Fin.sum_univ_three] at this
  grind

omit [Finite F] hσ in
theorem fourier_conj_relations :
    fourierMatThree ζ * heisXMat ζ = heisYMat * heisYMat * fourierMatThree ζ ∧
      fourierMatThree ζ * heisYMat = heisXMat ζ * fourierMatThree ζ := by
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisXMat, heisYMat, fourierMatThree, mul_apply, Fin.sum_univ_three] <;> grind

omit [Finite F] hσ in
theorem fourier_order_relations : fourierMatThree ζ ^ 2 ≠ 1 ∧ fourierMatThree ζ ^ 4 = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun (congrFun h 1) 1
    simp [fourierMatThree, pow_two, mul_apply, Fin.sum_univ_three] at this
    grind
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMatThree, pow_succ, mul_apply, Fin.sum_univ_three] <;> grind

end Matrices

section Group

variable (hσ : unitaryInvolution F 2 1 ζ = ζ ^ 2) (hs : 1 + ζ + ζ ^ 2 = 0)

@[expose] noncomputable def heisXSU : SUid (unitaryInvolution F 2 1) 3 :=
  mkSUid _ (heisXMat ζ) (heisXMat_mem hσ hs).1 (heisXMat_mem hσ hs).2

@[expose] noncomputable def heisYSU : SUid (unitaryInvolution F 2 1) 3 :=
  mkSUid _ heisYMat heisYMat_mem.1 heisYMat_mem.2

@[expose] noncomputable def fourierElt : SUid (unitaryInvolution F 2 1) 3 :=
  mkSUid _ (fourierMatThree ζ) (fourierMat_mem hσ hs).1 (fourierMat_mem hσ hs).2

theorem coe_pow_SUid (g : SUid (unitaryInvolution F 2 1) 3) (m : ℕ) :
    (((g ^ m : SUid (unitaryInvolution F 2 1) 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ m := by
  simp

theorem cubeRel_heis :
    CubeRel (heisXSU hσ hs) heisYSU ∧ heisXSU hσ hs * heisYSU ≠ heisYSU * heisXSU hσ hs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := heis_cube_relations hs
  have hy3 : (heisYSU : SUid (unitaryInvolution F 2 1) 3) ^ 3 = 1 :=
    ext_mat (by rw [coe_pow_SUid, heisYSU, coe_mkSUid, h2]; rfl)
  have hyinv : (heisYSU : SUid (unitaryInvolution F 2 1) 3)⁻¹ = heisYSU * heisYSU := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← mul_assoc, show heisYSU * heisYSU * heisYSU =
      (heisYSU : SUid (unitaryInvolution F 2 1) 3) ^ 3 by rw [pow_three, mul_assoc], hy3]
  refine ⟨⟨ext_mat ?_, hy3, ext_mat ?_, ?_⟩, fun h => h5 ?_⟩
  · rw [coe_pow_SUid, heisXSU, coe_mkSUid, h1]
    rfl
  · rw [coe_pow_SUid, Subgroup.coe_mul, Units.val_mul, heisXSU, heisYSU, coe_mkSUid, coe_mkSUid, h3]
    rfl
  · rw [hyinv]
    refine ext_mat ?_
    rw [coe_pow_SUid, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, heisXSU,
      heisYSU, coe_mkSUid, coe_mkSUid, h4]
    rfl
  · have := congrArg (fun g : SUid (unitaryInvolution F 2 1) 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    simpa [heisXSU, heisYSU, coe_mkSUid] using this

theorem fourierElt_mem_normalizer :
    fourierElt hσ hs ∈ Subgroup.normalizer (Subgroup.closure
      ({heisXSU hσ hs, heisYSU} : Set (SUid (unitaryInvolution F 2 1) 3)) : Set _) := by
  obtain ⟨h1, h2⟩ := fourier_conj_relations (ζ := ζ) hs
  have hx : fourierElt hσ hs * heisXSU hσ hs = heisYSU * heisYSU * fourierElt hσ hs := ext_mat (by
    simp only [Subgroup.coe_mul, Units.val_mul, fourierElt, heisXSU, heisYSU, coe_mkSUid, h1])
  have hy : fourierElt hσ hs * heisYSU = heisXSU hσ hs * fourierElt hσ hs := ext_mat (by
    simp only [Subgroup.coe_mul, Units.val_mul, fourierElt, heisXSU, heisYSU, coe_mkSUid, h2])
  refine mem_normalizer_closure_of_forall_conj_mem ?_
  rintro s (rfl | rfl)
  · rw [hx, mul_inv_cancel_right]
    have hyR : (heisYSU : SUid (unitaryInvolution F 2 1) 3) ∈ Subgroup.closure
        ({heisXSU hσ hs, heisYSU} : Set (SUid (unitaryInvolution F 2 1) 3)) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact mul_mem hyR hyR
  · rw [hy, mul_inv_cancel_right]
    exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem orderOf_fourierElt : orderOf (fourierElt hσ hs) = 4 := by
  obtain ⟨h1, h2⟩ := fourier_order_relations (ζ := ζ) hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (p := 2) (n := 1) (fun h => h1 ?_) (ext_mat ?_)
  · have := congrArg (fun g : SUid (unitaryInvolution F 2 1) 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    simpa [fourierElt, coe_mkSUid] using this
  · rw [coe_pow_SUid, fourierElt, coe_mkSUid, show (2 : ℕ) ^ (1 + 1) = 4 by norm_num, h2]
    rfl

theorem pow_three_eq_one_of_commute_heis (g : SUid (unitaryInvolution F 2 1) 3)
    (hgx : g * heisXSU hσ hs = heisXSU hσ hs * g) (hgy : g * heisYSU = heisYSU * g) :
    g ^ 3 = 1 := by
  set M := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hM
  have hx : M * heisXMat ζ = heisXMat ζ * M := by
    have := congrArg (fun g : SUid (unitaryInvolution F 2 1) 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hgx
    simpa only [Subgroup.coe_mul, Units.val_mul, heisXSU, coe_mkSUid] using this
  have hy : M * heisYMat = heisYMat * M := by
    have := congrArg (fun g : SUid (unitaryInvolution F 2 1) 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hgy
    simpa only [Subgroup.coe_mul, Units.val_mul, heisYSU, coe_mkSUid] using this
  have e : ∀ i j, (M * heisXMat ζ : Matrix (Fin 3) (Fin 3) F) i j =
      (heisXMat ζ * M : Matrix (Fin 3) (Fin 3) F) i j := fun i j => congrFun (congrFun hx i) j
  have f : ∀ i j, (M * heisYMat : Matrix (Fin 3) (Fin 3) F) i j =
      (heisYMat * M : Matrix (Fin 3) (Fin 3) F) i j := fun i j => congrFun (congrFun hy i) j
  have hζ1 : ζ ≠ 1 := fun h => by rw [h] at hs; grind
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by grind
  have hζ3 : ζ ^ 2 ≠ ζ := fun h => by grind
  simp [heisXMat, heisYMat, mul_apply, Fin.sum_univ_three] at e f
  have h01 := e 0 1
  have h02 := e 0 2
  have h10 := e 1 0
  have h12 := e 1 2
  have h20 := e 2 0
  have h21 := e 2 1
  have h00 := f 1 0
  have h11 := f 2 1
  simp at h01 h02 h10 h12 h20 h21 h00 h11
  have hdet := g.2.1
  have hscal : M = Matrix.scalar (Fin 3) (M 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;> grind
  apply ext_mat
  rw [coe_pow_SUid, ← hM, hscal, ← map_pow]
  have h3 : M 0 0 ^ 3 = 1 := by
    rw [← hdet, ← hM, hscal, Matrix.scalar_apply, det_diagonal]
    simp [pow_three]
  rw [h3, map_one]
  rfl

theorem card_SUid_three_two (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (SUid (unitaryInvolution F 2 1) 3) = 216 := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv, CFSG.LieType.Steinberg.card_SU_three hF]
  norm_num

theorem normal_closure_heis (hF : Nat.card F = (2 ^ 1) ^ 2) :
    (Subgroup.closure ({heisXSU hσ hs, heisYSU} :
      Set (SUid (unitaryInvolution F 2 1) 3))).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R₃ := Subgroup.closure ({heisXSU hσ hs, heisYSU} : Set (SUid (unitaryInvolution F 2 1) 3))
    with hR₃
  obtain ⟨hR, hxy⟩ := cubeRel_heis hσ hs
  have h27 : Nat.card R₃ = 27 := card_closure_eq_of_cubeRel hR hxy
  have h216 := card_SUid_three_two hF
  have hidx : R₃.index = 8 := by
    have := Subgroup.card_mul_index R₃
    rw [h27, h216] at this
    omega
  let P : Sylow 3 (SUid (unitaryInvolution F 2 1) 3) :=
    (IsPGroup.of_card (n := 3) (by rw [h27]; norm_num)).toSylow (by rw [hidx]; norm_num)
  set N := Subgroup.normalizer (R₃ : Set (SUid (unitaryInvolution F 2 1) 3)) with hN
  have h27N : 27 ∣ Nat.card N := h27 ▸ Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have h4N : 4 ∣ Nat.card N :=
    orderOf_fourierElt hσ hs ▸ Subgroup.orderOf_dvd_natCard N (fourierElt_mem_normalizer hσ hs)
  have h108 : 108 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h27N h4N
  have hNi := Subgroup.card_mul_index N
  rw [h216] at hNi
  obtain ⟨m, hm⟩ := h108
  rw [hm] at hNi
  have hi2 : N.index = 1 ∨ N.index = 2 := by
    have h2 : m * N.index = 2 := by
      have : 108 * (m * N.index) = 108 * 2 := by rw [← mul_assoc, hNi]
      omega
    exact (Nat.dvd_prime Nat.prime_two).1 ⟨m, by rw [mul_comm]; exact h2.symm⟩
  have hmod := card_sylow_modEq_one 3 (SUid (unitaryInvolution F 2 1) 3)
  rw [Sylow.card_eq_index_normalizer P] at hmod
  have hP : (Subgroup.normalizer (P : Set (SUid (unitaryInvolution F 2 1) 3))).index =
      N.index := rfl
  rw [hP] at hmod
  rcases hi2 with h | h
  · exact Subgroup.normalizer_eq_top_iff.1 (Subgroup.index_eq_one.1 h)
  · rw [h] at hmod
    exact absurd hmod (by decide)

end Group

theorem exists_su_three_two_heis (hF : Nat.card F = (2 ^ 1) ^ 2) {L : Type*} [Group L]
    (Ψ : L ≃* SU (unitaryInvolution F 2 1) 3) :
    Nat.card L = 216 ∧ ∃ x y : L, CubeRel x y ∧ x * y ≠ y * x ∧
      (Subgroup.closure ({x, y} : Set L)).Normal ∧
      ∀ g : L, g * x = x * g → g * y = y * g → g ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
  set e : L ≃* SUid (unitaryInvolution F 2 1) 3 := Ψ.trans (conjEquiv P hP) with he
  obtain ⟨ζ, hζ0, hζ1, hζ3⟩ := exists_primitive_cube_root_of_card_four hF
  have hσ : unitaryInvolution F 2 1 ζ = ζ ^ 2 := by rw [unitaryInvolution_apply, pow_one]
  have hs : 1 + ζ + ζ ^ 2 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2) = 0 := by
      linear_combination hζ3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hζ1
    · exact h
  obtain ⟨hR, hxy⟩ := cubeRel_heis hσ hs
  refine ⟨by rw [Nat.card_congr e.toEquiv, card_SUid_three_two hF], e.symm (heisXSU hσ hs),
    e.symm heisYSU, ⟨?_, ?_, ?_, ?_⟩, fun h => hxy (e.symm.injective ?_), ?_, ?_⟩
  · rw [← map_pow, hR.cube_left, map_one]
  · rw [← map_pow, hR.cube_right, map_one]
  · rw [← map_mul, ← map_pow, hR.cube_mul, map_one]
  · rw [← map_inv, ← map_mul, ← map_pow, hR.cube_mul_inv, map_one]
  · rw [map_mul, map_mul, h]
  · have hmap : Subgroup.closure ({e.symm (heisXSU hσ hs), e.symm heisYSU} : Set L) =
        (Subgroup.closure ({heisXSU hσ hs, heisYSU} : Set _)).map e.symm.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [hmap]
    exact (normal_closure_heis hσ hs hF).map _ e.symm.surjective
  · intro g hgx hgy
    have h1 : e g * heisXSU hσ hs = heisXSU hσ hs * e g := by
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply, hgx]
    have h2 : e g * heisYSU = heisYSU * e g := by
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply, hgy]
    apply e.injective
    rw [map_pow, pow_three_eq_one_of_commute_heis hσ hs _ h1 h2, map_one]

end CFSG.AGLEmbedding
