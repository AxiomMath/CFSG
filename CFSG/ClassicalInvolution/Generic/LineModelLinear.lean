module

public import CFSG.ClassicalInvolution.Generic.LineModel
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.ClassicalInvolution.Generic

open Matrix CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Matrices

variable {F : Type} [Field F]

@[expose] noncomputable def om12 : SL(3, F) := blockSL F 3 2 0 (by omega) rotSL

@[expose] noncomputable def om23 : SL(3, F) := blockSL F 3 2 1 (by omega) rotSL

theorem om12_mem : (om12 : SL(3, F)) ∈ B12 F := ⟨rotSL, rfl⟩

theorem om23_mem : (om23 : SL(3, F)) ∈ B23 F := ⟨rotSL, rfl⟩

theorem coe_rotSL : ((rotSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl

theorem coe_om12 :
    ((om12 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [om12, coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_rotSL]

theorem coe_om23 :
    ((om23 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  rw [om23, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_rotSL]

theorem coe_om12_inv :
    (((om12 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [om12, ← map_inv, coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_rotSL, Matrix.adjugate_fin_two]

theorem coe_om23_inv :
    (((om23 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  rw [om23, ← map_inv, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_rotSL, Matrix.adjugate_fin_two]

theorem om12_mul_om23_pow_three : ((om12 : SL(3, F)) * om23) ^ 3 = 1 := by
  apply Subtype.ext
  simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul, coe_om12, coe_om23,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def flipSL (A : SL(2, F)) : SL(2, F) :=
  ⟨!![A 0 0, -A 0 1; -A 1 0, A 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination h⟩

theorem coe_flipSL (A : SL(2, F)) :
    ((flipSL A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![A 0 0, -A 0 1; -A 1 0, A 1 1] := rfl

theorem flipSL_flipSL (A : SL(2, F)) : flipSL (flipSL A) = A := by
  apply sl_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_flipSL]

theorem om12_mul_blockSL_one_mul_inv (A : SL(2, F)) :
    (om12 : SL(3, F)) * blockSL F 3 2 1 (by omega) A * om12⁻¹ =
      om23 * blockSL F 3 2 0 (by omega) (flipSL A) * om23⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_om12, coe_om23, coe_om12_inv, coe_om23_inv,
    coe_blockSL_three_zero, coe_blockSL_three_one, coe_flipSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem conjSub_om12_B23 : conjSub (om12 : SL(3, F)) (B23 F) = conjSub om23 (B12 F) := by
  ext y
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨blockSL F 3 2 0 (by omega) (flipSL A), ⟨_, rfl⟩, ?_⟩
    exact (om12_mul_blockSL_one_mul_inv A).symm
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨blockSL F 3 2 1 (by omega) (flipSL A), ⟨_, rfl⟩, ?_⟩
    have := om12_mul_blockSL_one_mul_inv (flipSL A)
    rw [flipSL_flipSL] at this
    exact this

theorem rotSL_mul_torusHom_mul_inv (s : Fˣ) :
    (rotSL : SL(2, F)) * torusHom F s * rotSL⁻¹ = torusHom F s⁻¹ := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv,
    coe_torusHom, coe_torusHom, coe_rotSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phan.rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotSL_inv_mul_torusHom_mul (s : Fˣ) :
    (rotSL : SL(2, F))⁻¹ * torusHom F s * rotSL = torusHom F s⁻¹ := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv,
    coe_torusHom, coe_torusHom, coe_rotSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phan.rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem om12_conj_D12 {d : SL(3, F)} (hd : d ∈ D12 F) : (om12 : SL(3, F)) * d * om12⁻¹ ∈ D12 F := by
  obtain ⟨u, rfl⟩ := mem_D12_iff.mp hd
  refine mem_D12_iff.mpr ⟨u⁻¹, ?_⟩
  rw [om12, ← map_inv, ← map_mul, ← map_mul, rotSL_mul_torusHom_mul_inv]

theorem om12_inv_conj_D12 {d : SL(3, F)} (hd : d ∈ D12 F) :
    (om12 : SL(3, F))⁻¹ * d * om12 ∈ D12 F := by
  obtain ⟨u, rfl⟩ := mem_D12_iff.mp hd
  refine mem_D12_iff.mpr ⟨u⁻¹, ?_⟩
  rw [om12, ← map_inv, ← map_mul, ← map_mul, rotSL_inv_mul_torusHom_mul]

theorem om23_conj_D23 {d : SL(3, F)} (hd : d ∈ D23 F) : (om23 : SL(3, F)) * d * om23⁻¹ ∈ D23 F := by
  obtain ⟨u, rfl⟩ := mem_D23_iff.mp hd
  refine mem_D23_iff.mpr ⟨u⁻¹, ?_⟩
  rw [om23, ← map_inv, ← map_mul, ← map_mul, rotSL_mul_torusHom_mul_inv]

theorem om23_inv_conj_D23 {d : SL(3, F)} (hd : d ∈ D23 F) :
    (om23 : SL(3, F))⁻¹ * d * om23 ∈ D23 F := by
  obtain ⟨u, rfl⟩ := mem_D23_iff.mp hd
  refine mem_D23_iff.mpr ⟨u⁻¹, ?_⟩
  rw [om23, ← map_inv, ← map_mul, ← map_mul, rotSL_inv_mul_torusHom_mul]

theorem om12_not_mem_D12 : (om12 : SL(3, F)) ∉ D12 F := by
  intro h
  obtain ⟨u, hu⟩ := mem_D12_iff.mp h
  have h1 : torusHom F u = rotSL :=
    blockSL_injective (by omega : 0 + 2 ≤ 3) (hu.trans rfl)
  have h2 := congrFun (congrFun (congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h1) 0) 1
  simp [coe_torusHom, coe_rotSL] at h2

theorem om23_not_mem_D23 : (om23 : SL(3, F)) ∉ D23 F := by
  intro h
  obtain ⟨u, hu⟩ := mem_D23_iff.mp h
  have h1 : torusHom F u = rotSL :=
    blockSL_injective (by omega : 1 + 2 ≤ 3) (hu.trans rfl)
  have h2 := congrFun (congrFun (congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h1) 0) 1
  simp [coe_torusHom, coe_rotSL] at h2

end Matrices

section Line

variable {F : Type} [Field F] {G : Type} [Group G]

@[expose] def LinearA2Pair (F : Type) [Field F] (E K L : Subgroup G) : Prop :=
  ∃ θ : SL(3, F) →* G, θ.ker ≤ Subgroup.center SL(3, F) ∧ (B12 F).map θ = K ∧
    (B23 F).map θ = L ∧ centPart K E = (D12 F).map θ ∧ centPart L E = (D23 F).map θ

theorem LinearA2Pair.linearBlockStandardPair {E K L : Subgroup G} (h : LinearA2Pair F E K L) :
    ∃ W : Subgroup G, LinearBlockStandardPair F W K L := by
  obtain ⟨θ, hker, hK, hL, -, -⟩ := h
  have e : ∀ B : Subgroup SL(3, F),
      B.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = B := fun B => by
    rw [inv_one]
    exact conjSub_one B
  refine ⟨θ.range, θ, 1, rfl, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [e, hK]
  · rw [e, hL]

theorem LinearA2Pair.isLine [Finite F] {E K L : Subgroup G} (h : LinearA2Pair F E K L)
    (hK : InSigma F E K) (hL : InSigma F E L) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    IsLine E K L ∧ IsLine E L K := by
  obtain ⟨θ, hker, hKB, hLB, hHK, hHL⟩ := h
  exact isLine_of_model hK hL hodd h5 hker (fun b hb hz => B12_center b hb hz)
    (fun b hb hz => B23_center b hb hz) D12_le_B12 D23_le_B23 hKB hLB hHK hHL
    (fun d hd m hm => D12_conj_mem_B23 hd hm) (fun d hd m hm => D23_conj_mem_B12 hd hm)
    om12_mem om23_mem (fun d hd => om12_conj_D12 hd) (fun d hd => om12_inv_conj_D12 hd)
    (fun d hd => om23_conj_D23 hd) (fun d hd => om23_inv_conj_D23 hd) om12_not_mem_D12
    om23_not_mem_D23 conjSub_om12_B23 om12_mul_om23_pow_three

theorem a2Dichotomy_of_linear {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}
    [Finite F] (Fr : ToralFrame F Ω E S)
    (h : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearA2Pair F E K L ∨ LinearA2Pair F E L K) : A2Dichotomy E S := by
  intro K hK L hL hKL
  rcases h K hK L hL hKL with hc | hp | hp
  · exact Or.inl hc
  · exact Or.inr (hp.isLine (Fr.inSigma hK) (Fr.inSigma hL) Fr.odd Fr.five).1
  · exact Or.inr (hp.isLine (Fr.inSigma hL) (Fr.inSigma hK) Fr.odd Fr.five).2

@[expose] def DiagAction (θ : SL(3, F) →* G) (E : Subgroup G) : Prop :=
  ∀ e ∈ E, ∃ a b : Fˣ, ∀ x : SL(3, F), e * θ x * e⁻¹ = θ (diagConj3 a b x)

theorem mem_diagTorus2_of_diagConj2_eq {a b : Fˣ} (hab : a ≠ b) {A : SL(2, F)}
    (h : diagConj2 a b A = A) : A ∈ diagTorus2 F := by
  have h01 := congrFun (congrFun (congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h) 0) 1
  have h10 := congrFun (congrFun (congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h) 1) 0
  simp only [coe_diagConj2] at h01 h10
  simp [Matrix.mul_apply, Matrix.diagonal_apply] at h01 h10
  have hb : (b : F) * (b : F)⁻¹ = 1 := mul_inv_cancel₀ b.ne_zero
  have ha : (a : F) * (a : F)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
  have hne : (a : F) - b ≠ 0 := sub_ne_zero.mpr (fun h => hab (Units.ext h))
  have e01 : ((a : F) - b) * A 0 1 = 0 := by
    linear_combination (b : F) * h01 - (a * A 0 1) * hb
  have e10 : ((b : F) - a) * A 1 0 = 0 := by
    linear_combination (a : F) * h10 - (b * A 1 0) * ha
  have hne' : (b : F) - a ≠ 0 := sub_ne_zero.mpr (fun h => hab (Units.ext h.symm))
  exact mem_diagTorus2_of_offDiag A ((mul_eq_zero.mp e01).resolve_left hne)
    ((mul_eq_zero.mp e10).resolve_left hne')

theorem diagConj2_torusHom (a b s : Fˣ) : diagConj2 a b (torusHom F s) = torusHom F s := by
  apply sl_ext
  rw [coe_diagConj2, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem diagConj2_self (a : Fˣ) (A : SL(2, F)) : diagConj2 a a A = A := by
  apply sl_ext
  rw [coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem linearA2Pair_of_diagAction {E K L : Subgroup G} {θ : SL(3, F) →* G}
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (hK : (B12 F).map θ = K) (hL : (B23 F).map θ = L)
    (hdiag : DiagAction θ E) (hKS : InSigma F E K) (hLS : InSigma F E L) :
    LinearA2Pair F E K L := by
  refine ⟨θ, hker, hK, hL, ?_, ?_⟩
  ·
    have hinj := comp_blockSL_injective (K := F) (i := 0) (k := 2) (m := 3) hker (by omega)
      (by omega)
    obtain ⟨e₀, he₀, he₀'⟩ := hKS.exists_mem_not_mem_axis
    obtain ⟨a₀, b₀, h₀⟩ := hdiag e₀ he₀
    have hab : a₀ ≠ b₀ := by
      rintro rfl
      apply he₀'
      rw [mem_axisSub_iff]
      refine ⟨he₀, fun k hk => ?_⟩
      rw [← hK] at hk
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
      have h1 := h₀ (blockSL F 3 2 0 (by omega) A)
      rw [diagConj3_blockSL_zero, diagConj2_self] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    ext c
    constructor
    · intro hc
      rw [mem_centPart_iff] at hc
      obtain ⟨hcK, hcE⟩ := hc
      rw [← hK] at hcK
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hcK
      have h1 := h₀ (blockSL F 3 2 0 (by omega) A)
      rw [diagConj3_blockSL_zero, mul_inv_eq_iff_eq_mul.mpr (hcE e₀ he₀)] at h1
      have h2 : diagConj2 a₀ b₀ A = A := hinj h1.symm
      exact ⟨blockSL F 3 2 0 (by omega) A, ⟨A, mem_diagTorus2_of_diagConj2_eq hab h2, rfl⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      rw [mem_centPart_iff, ← hK]
      refine ⟨⟨d, D12_le_B12 hd, rfl⟩, fun e he => ?_⟩
      obtain ⟨a, b, h⟩ := hdiag e he
      obtain ⟨A, hA, rfl⟩ := hd
      have h1 := h (blockSL F 3 2 0 (by omega) A)
      rw [diagConj3_blockSL_zero] at h1
      obtain ⟨u, rfl⟩ := mem_diagTorus2_iff.mp hA
      rw [diagConj2_torusHom] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
  ·
    have hinj := comp_blockSL_injective (K := F) (i := 1) (k := 2) (m := 3) hker (by omega)
      (by omega)
    obtain ⟨e₀, he₀, he₀'⟩ := hLS.exists_mem_not_mem_axis
    obtain ⟨a₀, b₀, h₀⟩ := hdiag e₀ he₀
    have hab : b₀ ≠ 1 := by
      rintro rfl
      apply he₀'
      rw [mem_axisSub_iff]
      refine ⟨he₀, fun k hk => ?_⟩
      rw [← hL] at hk
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
      have h1 := h₀ (blockSL F 3 2 1 (by omega) A)
      rw [diagConj3_blockSL_one, diagConj2_self] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    ext c
    constructor
    · intro hc
      rw [mem_centPart_iff] at hc
      obtain ⟨hcK, hcE⟩ := hc
      rw [← hL] at hcK
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hcK
      have h1 := h₀ (blockSL F 3 2 1 (by omega) A)
      rw [diagConj3_blockSL_one, mul_inv_eq_iff_eq_mul.mpr (hcE e₀ he₀)] at h1
      have h2 : diagConj2 b₀ 1 A = A := hinj h1.symm
      exact ⟨blockSL F 3 2 1 (by omega) A, ⟨A, mem_diagTorus2_of_diagConj2_eq hab h2, rfl⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      rw [mem_centPart_iff, ← hL]
      refine ⟨⟨d, D23_le_B23 hd, rfl⟩, fun e he => ?_⟩
      obtain ⟨a, b, h⟩ := hdiag e he
      obtain ⟨A, hA, rfl⟩ := hd
      have h1 := h (blockSL F 3 2 1 (by omega) A)
      rw [diagConj3_blockSL_one] at h1
      obtain ⟨u, rfl⟩ := mem_diagTorus2_iff.mp hA
      rw [diagConj2_torusHom] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1

end Line

end CFSG.ClassicalInvolution.Generic
