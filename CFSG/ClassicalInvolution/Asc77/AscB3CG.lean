module

public import CFSG.ClassicalInvolution.Asc77.AscB3C1

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace B3C

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt E mat_elt)
open CFSG.LieType.Steinberg.Sp (blockMat mem_closure_sl2)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]


@[expose] def tvMat (v : Fin 2 ⊕ Fin 2 → F) (c : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  1 - c • Matrix.vecMulVec v (v ᵥ* gram F 2)

theorem tvMat_symp (v : Fin 2 ⊕ Fin 2 → F) (c : F) :
    (tvMat v c)ᵀ * gram F 2 * tvMat v c = gram F 2 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tvMat, gram, Matrix.mul_apply, Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.transpose_apply, Matrix.one_apply,
      Matrix.sub_apply, Fin.sum_univ_two]
  all_goals ring

@[expose] noncomputable def tv (v : Fin 2 ⊕ Fin 2 → F) (c : F) : StatedSp 2 F :=
  ofSymplecticMat (tvMat v c) (tvMat_symp v c)

theorem mat_tv (v : Fin 2 ⊕ Fin 2 → F) (c : F) : mat 2 F (tv v c) = tvMat v c := rfl

@[expose] noncomputable def act (g : StatedSp 2 F) (v : Fin 2 ⊕ Fin 2 → F) : Fin 2 ⊕ Fin 2 → F :=
  mat 2 F g *ᵥ v

theorem conj_tv (g : StatedSp 2 F) (v : Fin 2 ⊕ Fin 2 → F) (c : F) :
    g * tv v c * g⁻¹ = tv (act g v) c := by
  apply mat_injective
  rw [map_mul, map_mul, mat_tv, mat_tv]
  have hGGi : mat 2 F g * mat 2 F g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hJ : (mat 2 F g)ᵀ * gram F 2 * mat 2 F g = gram F 2 := mat_transpose_mul_gram_mul g
  have hJGi : gram F 2 * mat 2 F g⁻¹ = (mat 2 F g)ᵀ * gram F 2 := by
    calc gram F 2 * mat 2 F g⁻¹ = ((mat 2 F g)ᵀ * gram F 2 * mat 2 F g) * mat 2 F g⁻¹ := by
          rw [hJ]
      _ = (mat 2 F g)ᵀ * gram F 2 * (mat 2 F g * mat 2 F g⁻¹) := by simp [Matrix.mul_assoc]
      _ = (mat 2 F g)ᵀ * gram F 2 := by rw [hGGi, Matrix.mul_one]
  unfold tvMat act
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hGGi, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, hJGi,
    ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]


theorem tvMat_add (v : Fin 2 ⊕ Fin 2 → F) (c c' : F) :
    tvMat v c * tvMat v c' = tvMat v (c + c') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tvMat, gram, Matrix.mul_apply, Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply,
      Matrix.sub_apply, Fin.sum_univ_two]
  all_goals ring

theorem tv_add (v : Fin 2 ⊕ Fin 2 → F) (c c' : F) : tv v c * tv v c' = tv v (c + c') := by
  apply mat_injective
  rw [map_mul, mat_tv, mat_tv, mat_tv]
  exact tvMat_add v c c'

theorem tvMat_zero (v : Fin 2 ⊕ Fin 2 → F) : tvMat v 0 = 1 := by
  simp [tvMat]

theorem tv_zero (v : Fin 2 ⊕ Fin 2 → F) : tv v 0 = 1 := by
  apply mat_injective
  rw [mat_tv, map_one]
  exact tvMat_zero v

theorem tv_inv (v : Fin 2 ⊕ Fin 2 → F) (c : F) : (tv v c)⁻¹ = tv v (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tv_add, add_neg_cancel, tv_zero]

@[expose] def omega (x y : Fin 2 ⊕ Fin 2 → F) : F := x ⬝ᵥ (gram F 2 *ᵥ y)

theorem act_tv (u v : Fin 2 ⊕ Fin 2 → F) (a : F) :
    act (tv u a) v = v + (a * omega v u) • u := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [act, mat_tv, tvMat, omega, gram, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
      Matrix.vecMul, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply,
      Matrix.sub_apply] <;> ring

@[expose] def InSig (H : Subgroup (StatedSp 2 F)) (v : Fin 2 ⊕ Fin 2 → F) : Prop := ∀ c, tv v c ∈ H

theorem InSig.add_smul {H : Subgroup (StatedSp 2 F)} {u v : Fin 2 ⊕ Fin 2 → F} (hu : InSig H u)
    (hv : InSig H v) (hω : omega v u ≠ 0) (l : F) : InSig H (v + l • u) := by
  intro b
  have h1 : tv u (l / omega v u) * tv v b * (tv u (l / omega v u))⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (hu _) (hv b)) (H.inv_mem (hu _))
  rw [conj_tv, act_tv, div_mul_cancel₀ _ hω] at h1
  exact h1



@[expose] def vec (X : Matrix (Fin 2) (Fin 2) F) : Fin 2 ⊕ Fin 2 → F :=
  Sum.elim (fun k => X 0 k) (fun k => X 1 k)

theorem kron_act (A : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    act (kron2 A) (vec X) = vec ((A : Matrix (Fin 2) (Fin 2) F) * X) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [act, mat_kron2, kronMat, vec, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.mul_apply]

@[expose] noncomputable def Mprime (h2 : (2 : F) ≠ 0) : Subgroup (StatedSp 2 F) :=
  ((longBlock F 2 1).range ⊔ (twShort h2).range).map (MulAut.conj (Pel h2)).toMonoidHom

theorem kron2_mem (h2 : (2 : F) ≠ 0) (A : SL(2, F)) : kron2 A ∈ Mprime h2 := by
  refine ⟨twShort h2 A, Subgroup.mem_sup_right ⟨A, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, twShort_apply]
  group


@[expose] def pv (α γ : F) : Fin 2 ⊕ Fin 2 → F := Sum.elim ![0, α] ![0, γ]

theorem tv_pv_eq (α γ s : F) :
    tv (pv α γ) s = longBlock F 2 1
      (mkSL !![1 + s * α * γ, -(s * α ^ 2); s * γ ^ 2, 1 - s * α * γ] (by
        rw [Matrix.det_fin_two_of]; ring)) := by
  apply mat_injective
  rw [mat_tv, mat_longBlock]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tvMat, pv, gram, Matrix.vecMulVec, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply, Matrix.sub_apply, blockMat,
      mkSL]
  all_goals first | ring1 | (left; ring1)

theorem tv_pv_mem (α γ s : F) : tv (pv α γ) s ∈ (longBlock F 2 1).range :=
  ⟨_, (tv_pv_eq α γ s).symm⟩

theorem act_Pel_pv (h2 : (2 : F) ≠ 0) (α β : F) :
    act (Pel h2) (pv α (-(2 * β))) = vec !![α, β; -β, α] := by
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [act, mat_Pel, Pmat, pv, vec, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks]
  all_goals linear_combination β * h22



theorem elt_diff01 (c : F) :
    elt (.difference (0 : Fin 2) 1 zero_ne_one) c =
      tv (vec !![1, 0; 0, 1]) c * tv (vec !![1, 0; 0, 0]) (-c) * tv (vec !![0, 0; 0, 1]) (-c) := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_tv, mat_tv, mat_tv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [E, tvMat, vec, gram, Matrix.mul_apply, Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply,
      Matrix.sub_apply]

theorem elt_diff10 (c : F) :
    elt (.difference (1 : Fin 2) 0 zero_ne_one.symm) c =
      tv (vec !![0, 1; 1, 0]) c * tv (vec !![0, 1; 0, 0]) (-c) * tv (vec !![0, 0; 1, 0]) (-c) := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_tv, mat_tv, mat_tv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [E, tvMat, vec, gram, Matrix.mul_apply, Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply,
      Matrix.sub_apply]

theorem elt_posLong1 (c : F) :
    elt (.positiveLong (1 : Fin 2)) c = tv (vec !![0, 1; 0, 0]) (-c) := by
  apply mat_injective
  rw [mat_elt, mat_tv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [E, tvMat, vec, gram, Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.sub_apply]

theorem elt_negLong1 (c : F) :
    elt (.negativeLong (1 : Fin 2)) c = tv (vec !![0, 0; 0, 1]) c := by
  apply mat_injective
  rw [mat_elt, mat_tv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [E, tvMat, vec, gram, Matrix.vecMulVec, Matrix.vecMul, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.sub_apply]


theorem tv_H_mem (h2 : (2 : F) ≠ 0) (α β s : F) : tv (vec !![α, β; -β, α]) s ∈ Mprime h2 := by
  have h := conj_tv (Pel h2) (pv α (-(2 * β))) s
  rw [act_Pel_pv h2 α β] at h
  rw [← h]
  exact ⟨tv (pv α (-(2 * β))) s, Subgroup.mem_sup_left (tv_pv_mem _ _ _), by
    simp [MulAut.conj_apply]⟩

open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (exists_sq_add_sq)

theorem insig_of_det [Finite F] (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 2) (Fin 2) F}
    (hX : X.det ≠ 0) : InSig (Mprime h2) (vec X) := by
  obtain ⟨α, β, hαβ⟩ := exists_sq_add_sq h2 X.det
  have hdetA : (X * (X.det⁻¹ • (!![α, -β; β, α] : Matrix (Fin 2) (Fin 2) F))).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin]
    have : α * α - -β * β = X.det := by linear_combination hαβ
    rw [this]
    field_simp
  let A : SL(2, F) := ⟨X * (X.det⁻¹ • (!![α, -β; β, α] : Matrix (Fin 2) (Fin 2) F)), hdetA⟩
  have hAh : (A : Matrix (Fin 2) (Fin 2) F) * !![α, β; -β, α] = X := by
    show X * (X.det⁻¹ • (!![α, -β; β, α] : Matrix (Fin 2) (Fin 2) F)) * !![α, β; -β, α] = X
    have : (!![α, -β; β, α] : Matrix (Fin 2) (Fin 2) F) * !![α, β; -β, α] = X.det • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first | ring1 | linear_combination hαβ
    rw [Matrix.mul_assoc, Matrix.smul_mul, this, smul_smul, inv_mul_cancel₀ hX, one_smul,
      Matrix.mul_one]
  intro s
  have h1 := conj_tv (kron2 A) (vec !![α, β; -β, α]) s
  rw [kron_act, hAh] at h1
  rw [← h1]
  exact (Mprime h2).mul_mem ((Mprime h2).mul_mem (kron2_mem h2 A) (tv_H_mem h2 α β s))
    ((Mprime h2).inv_mem (kron2_mem h2 A))


theorem vec_add (X Y : Matrix (Fin 2) (Fin 2) F) : vec (X + Y) = vec X + vec Y := by
  ext i
  rcases i with i | i <;> simp [vec]

theorem omega_vec (X Y : Matrix (Fin 2) (Fin 2) F) :
    omega (vec X) (vec Y) = X 0 0 * Y 1 0 + X 0 1 * Y 1 1 - X 1 0 * Y 0 0 - X 1 1 * Y 0 1 := by
  simp [omega, vec, gram, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks]
  ring

theorem insig_add [Finite F] (h2 : (2 : F) ≠ 0) {u v : Matrix (Fin 2) (Fin 2) F}
    (hu : u.det ≠ 0) (hv : v.det ≠ 0)
    (hω : v 0 0 * u 1 0 + v 0 1 * u 1 1 - v 1 0 * u 0 0 - v 1 1 * u 0 1 ≠ 0) :
    InSig (Mprime h2) (vec (v + u)) := by
  have h := (insig_of_det h2 hu).add_smul (insig_of_det h2 hv) (by rwa [omega_vec]) 1
  rwa [one_smul, ← vec_add] at h

theorem insig_e0 [Finite F] (h2 : (2 : F) ≠ 0) : InSig (Mprime h2) (vec !![1, 0; 0, 0]) := by
  have h := insig_add h2 (u := !![-1, -1; -1, 0]) (v := !![2, 1; 1, 0])
    (by simp [Matrix.det_fin_two_of]) (by simp [Matrix.det_fin_two_of]) (by simp; norm_num)
  convert h using 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals norm_num


theorem insig_e1 [Finite F] (h2 : (2 : F) ≠ 0) : InSig (Mprime h2) (vec !![0, 1; 0, 0]) := by
  have h := insig_add h2 (u := !![-1, -1; 0, -1]) (v := !![1, 2; 0, 1])
    (by simp [Matrix.det_fin_two_of]) (by simp [Matrix.det_fin_two_of]) (by simp; norm_num)
  convert h using 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals norm_num

theorem insig_f0 [Finite F] (h2 : (2 : F) ≠ 0) : InSig (Mprime h2) (vec !![0, 0; 1, 0]) := by
  have h := insig_add h2 (u := !![-1, 0; -1, -1]) (v := !![1, 0; 2, 1])
    (by simp [Matrix.det_fin_two_of]) (by simp [Matrix.det_fin_two_of]) (by simp; norm_num)
  convert h using 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals norm_num

theorem insig_f1 [Finite F] (h2 : (2 : F) ≠ 0) : InSig (Mprime h2) (vec !![0, 0; 0, 1]) := by
  have h := insig_add h2 (u := !![0, -1; -1, -1]) (v := !![0, 1; 1, 2])
    (by simp [Matrix.det_fin_two_of]) (by simp [Matrix.det_fin_two_of]) (by simp; norm_num)
  convert h using 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals norm_num

theorem insig_I [Finite F] (h2 : (2 : F) ≠ 0) : InSig (Mprime h2) (vec !![1, 0; 0, 1]) :=
  insig_of_det h2 (by simp [Matrix.det_fin_two_of])

theorem insig_S [Finite F] (h2 : (2 : F) ≠ 0) : InSig (Mprime h2) (vec !![0, 1; 1, 0]) :=
  insig_of_det h2 (by simp [Matrix.det_fin_two_of])

theorem Mprime_eq_top [Finite F] (h2 : (2 : F) ≠ 0) : Mprime h2 = ⊤ := by
  have hshort : (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range ≤ Mprime h2 := by
    rintro _ ⟨A, rfl⟩
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (Mprime h2).comap (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show shortBlock F _ (sl2Upper c) ∈ Mprime h2
        rw [shortBlock_sl2Upper, elt_diff01]
        exact (Mprime h2).mul_mem ((Mprime h2).mul_mem (insig_I h2 c) (insig_e0 h2 (-c)))
          (insig_f1 h2 (-c))
      · show shortBlock F _ (sl2Lower c) ∈ Mprime h2
        rw [shortBlock_sl2Lower, elt_diff10]
        exact (Mprime h2).mul_mem ((Mprime h2).mul_mem (insig_S h2 c) (insig_e1 h2 (-c)))
          (insig_f0 h2 (-c))
    exact hle (mem_closure_sl2 A)
  have hlong : (longBlock F 2 1).range ≤ Mprime h2 := by
    rintro _ ⟨A, rfl⟩
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (Mprime h2).comap (longBlock F 2 1) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show longBlock F 2 1 (sl2Upper c) ∈ Mprime h2
        rw [longBlock_sl2Upper, elt_posLong1]
        exact insig_e1 h2 (-c)
      · show longBlock F 2 1 (sl2Lower c) ∈ Mprime h2
        rw [longBlock_sl2Lower, elt_negLong1]
        exact insig_f1 h2 c
    exact hle (mem_closure_sl2 A)
  have htop : (⊤ : Subgroup (StatedSp 2 F)) ≤ Mprime h2 := by
    rw [← shortBlock_sup_longBlock_eq_top F]
    exact sup_le hshort hlong
  exact top_le_iff.mp htop

theorem twShort_sup_longBlock [Finite F] (h2 : (2 : F) ≠ 0) :
    (twShort h2).range ⊔ (longBlock F 2 1).range = ⊤ := by
  have h := Mprime_eq_top h2
  have h' : (longBlock F 2 1).range ⊔ (twShort h2).range = ⊤ := by
    have h1 := congrArg (Subgroup.comap (MulAut.conj (Pel h2)).toMonoidHom) h
    rw [Mprime, Subgroup.comap_map_eq_self_of_injective (MulAut.conj (Pel h2)).injective] at h1
    simpa using h1
  rw [sup_comm]
  exact h'


end B3C

end CFSG.ClassicalInvolution.Asc77
