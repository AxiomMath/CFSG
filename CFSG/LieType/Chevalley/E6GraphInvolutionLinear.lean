module

public import CFSG.LieType.Chevalley.E6GraphInvolutionForms
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi
open Matrix

variable {k : Type} [Field k]

variable (k) in
@[expose] def antiIdGL : GL (Fin 6) k :=
  ⟨antiId k, antiId k, antiId_mul_self, antiId_mul_self⟩

theorem coe_antiIdGL : (antiIdGL k : Matrix (Fin 6) (Fin 6) k) = antiId k := rfl

theorem antiId_mulVec (v : Fin 6 → k) (i : Fin 6) : (antiId k *ᵥ v) i = v (Fin.rev i) := by
  simp only [mulVec, dotProduct, antiId, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem antiId_alternating (h2 : (2 : k) = 0) (v : Fin 6 → k) : v ⬝ᵥ (antiId k *ᵥ v) = 0 := by
  simp only [dotProduct, antiId_mulVec, Fin.sum_univ_six]
  have h05 : Fin.rev (0 : Fin 6) = 5 := rfl
  have h14 : Fin.rev (1 : Fin 6) = 4 := rfl
  have h23 : Fin.rev (2 : Fin 6) = 3 := rfl
  have h32 : Fin.rev (3 : Fin 6) = 2 := rfl
  have h41 : Fin.rev (4 : Fin 6) = 1 := rfl
  have h50 : Fin.rev (5 : Fin 6) = 0 := rfl
  rw [h05, h14, h23, h32, h41, h50]
  linear_combination (v 0 * v 5 + v 1 * v 4 + v 2 * v 3) * h2

theorem transvection_mul_antiId :
    (Matrix.transvection (0 : Fin 6) 5 (1 : k)) * antiId k = antiId k + Matrix.single 0 0 1 := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [antiId, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_six]

theorem antiId_add_single_transpose :
    (antiId k + Matrix.single 0 0 1)ᵀ = antiId k + Matrix.single 0 0 1 := by
  rw [Matrix.transpose_add, antiId_transpose, Matrix.transpose_single]

theorem antiId_add_single_not_alternating :
    ¬ ∀ v : Fin 6 → k, v ⬝ᵥ ((antiId k + Matrix.single 0 0 1) *ᵥ v) = 0 := by
  intro h
  have h0 := h (Pi.single 0 1)
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply,
    Matrix.add_apply, Matrix.single_apply_same] at h0
  simp [antiId] at h0

theorem symmetric_of_sq_eq_one
    (h2 : (2 : k) = 0) (B : SpecialLinearGroup (Fin 6) k)
    (hB : realize h2 B * realize h2 (graphSL k B) = 1) :
    ((B : Matrix (Fin 6) (Fin 6) k) * antiId k)ᵀ = (B : Matrix (Fin 6) (Fin 6) k) * antiId k := by
  have hker : B * graphSL k B ∈ (realize h2).ker := by
    rw [MonoidHom.mem_ker, map_mul, hB]
  obtain ⟨l, hl3, hl⟩ := (mem_ker_realize h2 _).1 hker
  set M := (B : Matrix (Fin 6) (Fin 6) k) with hM
  set N := ((B⁻¹ : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) with hN
  have hMN : M * N = 1 := by
    rw [hM, hN, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hNM : N * M = 1 := by
    rw [hM, hN, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_graphSL] at hl
  have h1 : M * antiId k * Nᵀ = l • antiId k := by
    calc M * antiId k * Nᵀ = M * (antiId k * Nᵀ * antiId k) * antiId k := by
          simp only [Matrix.mul_assoc, antiId_mul_self, Matrix.mul_one]
      _ = l • antiId k := by
          rw [hl, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have h2' : M * antiId k = l • (antiId k * Mᵀ) := by
    calc M * antiId k = M * antiId k * (Nᵀ * Mᵀ) := by
          rw [← Matrix.transpose_mul, hMN, Matrix.transpose_one, Matrix.mul_one]
      _ = l • (antiId k * Mᵀ) := by
          rw [← Matrix.mul_assoc, h1, Matrix.smul_mul]
  have htr : (M * antiId k)ᵀ = antiId k * Mᵀ := by
    rw [Matrix.transpose_mul, antiId_transpose]
  have h3 : antiId k * Mᵀ = l • (M * antiId k) := by
    have := congrArg Matrix.transpose h2'
    rwa [htr, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
      antiId_transpose] at this
  have hinv : M * antiId k * (antiId k * N) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (antiId k), antiId_mul_self, Matrix.one_mul, hMN]
  have h4 : M * antiId k = (l * l) • (M * antiId k) := by
    calc M * antiId k = l • (antiId k * Mᵀ) := h2'
      _ = l • (l • (M * antiId k)) := by rw [h3]
      _ = (l * l) • (M * antiId k) := by rw [smul_smul]
  have hl2 : l * l = 1 := by
    have e : (1 : Matrix (Fin 6) (Fin 6) k) = (l * l) • 1 := by
      calc (1 : Matrix (Fin 6) (Fin 6) k) = M * antiId k * (antiId k * N) := hinv.symm
        _ = ((l * l) • (M * antiId k)) * (antiId k * N) := by rw [← h4]
        _ = (l * l) • (M * antiId k * (antiId k * N)) := Matrix.smul_mul _ _ _
        _ = (l * l) • 1 := by rw [hinv]
    have := congrFun (congrFun e 0) 0
    simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at this
    exact this.symm
  have hl1 : l = 1 := by
    calc l = l * (l * l) := by rw [hl2, mul_one]
      _ = l ^ 3 := by ring
      _ = 1 := hl3
  rw [htr, h3, hl1, one_smul]

theorem conj_realize_mul_diagramMap
    (h2 : (2 : k) = 0) (D B : SpecialLinearGroup (Fin 6) k) :
    realize h2 D * (realize h2 B * diagramMap TwistTag.E6 k) * (realize h2 D)⁻¹ =
      realize h2 (D * B * graphSL k D⁻¹) * diagramMap TwistTag.E6 k := by
  have hP := diagramMap_conj_realize h2 D⁻¹
  rw [map_inv] at hP
  calc realize h2 D * (realize h2 B * diagramMap TwistTag.E6 k) * (realize h2 D)⁻¹ =
        realize h2 D * realize h2 B *
          (diagramMap TwistTag.E6 k * (realize h2 D)⁻¹ * (diagramMap TwistTag.E6 k)⁻¹) *
            diagramMap TwistTag.E6 k := by group
    _ = _ := by rw [hP, map_mul, map_mul]

theorem coe_mul_graphSL_inv (D B : SpecialLinearGroup (Fin 6) k) :
    ((D * B * graphSL k D⁻¹ : SpecialLinearGroup (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) =
      (D : Matrix (Fin 6) (Fin 6) k) * ((B : Matrix (Fin 6) (Fin 6) k) * antiId k) *
        (D : Matrix (Fin 6) (Fin 6) k)ᵀ * antiId k := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_graphSL, inv_inv]
  simp only [Matrix.mul_assoc]

theorem sq_mul_diagramMap
    (h2 : (2 : k) = 0) (B : SpecialLinearGroup (Fin 6) k) :
    (realize h2 B * diagramMap TwistTag.E6 k) ^ 2 = realize h2 B * realize h2 (graphSL k B) := by
  have hPP := diagramMap_E6_mul_self (K := k)
  have hPinv : (diagramMap TwistTag.E6 k)⁻¹ = diagramMap TwistTag.E6 k :=
    (eq_inv_of_mul_eq_one_left hPP).symm
  rw [← diagramMap_conj_realize h2, sq, hPinv]
  calc realize h2 B * diagramMap TwistTag.E6 k * (realize h2 B * diagramMap TwistTag.E6 k) =
        realize h2 B * (diagramMap TwistTag.E6 k * realize h2 B * diagramMap TwistTag.E6 k) *
          (diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k) := by
        rw [hPP, mul_one]
        group
    _ = _ := by rw [hPP, mul_one]

theorem det_antiId_ne_zero : (antiId k).det ≠ 0 := fun h => by
  have := det_antiId_sq (E := k)
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem det_eq_one_of_congr (h2 : (2 : k) = 0) {D : Matrix (Fin 6) (Fin 6) k}
    {B T : SpecialLinearGroup (Fin 6) k}
    (h : D * ((B : Matrix (Fin 6) (Fin 6) k) * antiId k) * Dᵀ =
      (T : Matrix (Fin 6) (Fin 6) k) * antiId k) : D.det = 1 := by
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    B.2, T.2, one_mul] at e
  have e' : (D.det * D.det - 1) * (antiId k).det = 0 := by linear_combination e
  rcases mul_eq_zero.1 e' with h1 | h1
  · exact eq_one_of_mul_self_eq_one_of_two_eq_zero h2 (sub_eq_zero.1 h1)
  · exact absurd h1 det_antiId_ne_zero

theorem exists_conj_of_congr
    (h2 : (2 : k) = 0) (B T : SpecialLinearGroup (Fin 6) k)
    (D : GL (Fin 6) k)
    (hD : (D : Matrix (Fin 6) (Fin 6) k) * ((B : Matrix (Fin 6) (Fin 6) k) * antiId k) *
      (D : Matrix (Fin 6) (Fin 6) k)ᵀ = (T : Matrix (Fin 6) (Fin 6) k) * antiId k) :
    ∃ x ∈ subsystemGroup TwistTag.E6.tag k setA,
      x * (realize h2 B * diagramMap TwistTag.E6 k) * x⁻¹ =
        realize h2 T * diagramMap TwistTag.E6 k := by
  set D' : SpecialLinearGroup (Fin 6) k := ⟨D, det_eq_one_of_congr h2 hD⟩
  refine ⟨realize h2 D', by rw [← range_realize h2]; exact ⟨D', rfl⟩, ?_⟩
  rw [conj_realize_mul_diagramMap]
  congr 2
  apply Subtype.ext
  rw [coe_mul_graphSL_inv]
  change (D : Matrix (Fin 6) (Fin 6) k) * ((B : Matrix (Fin 6) (Fin 6) k) * antiId k) *
    (D : Matrix (Fin 6) (Fin 6) k)ᵀ * antiId k = T
  rw [hD, Matrix.mul_assoc, antiId_mul_self, Matrix.mul_one]

@[expose] def nonaltGL (k : Type) [Field k] : GL (Fin 6) k :=
  Matrix.SpecialLinearGroup.toGL
    (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) (1 : k)) * antiIdGL k

theorem coe_nonaltGL : (nonaltGL k : Matrix (Fin 6) (Fin 6) k) =
    antiId k + Matrix.single 0 0 1 := by
  rw [nonaltGL, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_antiIdGL]
  exact transvection_mul_antiId

theorem exists_conj_normal_form
    [Finite k] (h2 : (2 : k) = 0) {ℓ : ModGL TwistTag.E6.tag k}
    (hℓ : ℓ ∈ subsystemGroup TwistTag.E6.tag k setA)
    (hsq : (ℓ * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    (∃ x ∈ subsystemGroup TwistTag.E6.tag k setA,
        x * (ℓ * diagramMap TwistTag.E6 k) * x⁻¹ = diagramMap TwistTag.E6 k) ∨
      ∃ x ∈ subsystemGroup TwistTag.E6.tag k setA,
        x * (ℓ * diagramMap TwistTag.E6 k) * x⁻¹ =
          pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k := by
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  rw [← range_realize h2] at hℓ
  obtain ⟨B, rfl⟩ := hℓ
  rw [sq_mul_diagramMap] at hsq
  have hsym := symmetric_of_sq_eq_one h2 B hsq
  set A0 : GL (Fin 6) k := Matrix.SpecialLinearGroup.toGL B * antiIdGL k with hA0def
  have hA0 : (A0 : Matrix (Fin 6) (Fin 6) k) = (B : Matrix (Fin 6) (Fin 6) k) * antiId k := rfl
  by_cases halt : ∀ v : Fin 6 → k, v ⬝ᵥ ((A0 : Matrix (Fin 6) (Fin 6) k) *ᵥ v) = 0
  · obtain ⟨D, hD⟩ := exists_congruence_of_alternating_iff A0 (antiIdGL k)
      (by rw [hA0]; exact hsym) antiId_transpose (iff_of_true halt (antiId_alternating h2))
    left
    obtain ⟨x, hx, hxe⟩ := exists_conj_of_congr h2 B 1 D (by
      rw [← hA0, hD, coe_antiIdGL, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul])
    rw [map_one, one_mul] at hxe
    exact ⟨x, hx, hxe⟩
  · obtain ⟨D, hD⟩ := exists_congruence_of_alternating_iff A0 (nonaltGL k)
      (by rw [hA0]; exact hsym) (by rw [coe_nonaltGL]; exact antiId_add_single_transpose)
      (iff_of_false halt (by rw [coe_nonaltGL]; exact antiId_add_single_not_alternating))
    right
    obtain ⟨x, hx, hxe⟩ := exists_conj_of_congr h2 B
      (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) (1 : k)) D (by
      rw [← hA0, hD, coe_nonaltGL, ← transvection_mul_antiId]
      rfl)
    rw [realize_transvection_zero_five] at hxe
    exact ⟨x, hx, hxe⟩

theorem permLattice_sRoot : permLattice TwistTag.E6.perm sRoot = sRoot := by decide

theorem diagramMap_conj_pinnedX_negS
    (h2 : (2 : k) = 0) (c : k) :
    diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (-sRoot) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (-sRoot) c := by
  rw [← twistHom_id_eq, twistHom_id_pinnedX h2 (IsRoot.neg isRoot_sRoot), permLattice_neg,
    permLattice_sRoot]

theorem pinnedX_negS_mem_subsystemGroup
    (h2 : (2 : k) = 0) (c : k) :
    pinnedX TwistTag.E6.tag k (-sRoot) c ∈ subsystemGroup TwistTag.E6.tag k setA := by
  have hw : wordElt k flipSWord ∈ subsystemGroup TwistTag.E6.tag k setA :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      exact weylElt_mem_subsystemGroup (flipSWord_mem_setA i hi) 1
  have hs : pinnedX TwistTag.E6.tag k sRoot c ∈ subsystemGroup TwistTag.E6.tag k setA := by
    rw [← realize_transvection_zero_five h2, ← range_realize h2]
    exact ⟨_, rfl⟩
  have e := wordElt_conj_pinnedX h2 flipSWord isRoot_sRoot c
  rw [flipSWord_smul] at e
  rw [← e]
  exact mul_mem (mul_mem hw hs) (inv_mem hw)

theorem wordElt_negSWord_conj
    (h2 : (2 : k) = 0) (c : k) :
    wordElt k negSWord * pinnedX TwistTag.E6.tag k e6HighestRoot c * (wordElt k negSWord)⁻¹ =
      pinnedX TwistTag.E6.tag k (-sRoot) c := by
  rw [wordElt_conj_pinnedX h2 negSWord isRoot_e6HighestRoot, negSWord_smul]

theorem detector_of_conj
    (h2 : (2 : k) = 0) {F : Type} [Field F] (ι : F →+* k)
    {x j : ModGL TwistTag.E6.tag k}
    (hxj : x * j * x⁻¹ = pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k) :
    ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj (x⁻¹ * wordElt k negSWord)).toMonoidHom ⊔
      ((thetaRootGroup ι).map (MulAut.conj (x⁻¹ * wordElt k negSWord)).toMonoidHom).map
        (MulAut.conj j).toMonoidHom) := by
  set R₁ := (thetaRootGroup ι).map (MulAut.conj (x⁻¹ * wordElt k negSWord)).toMonoidHom
  have hj : j = x⁻¹ * (pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k) * x := by
    rw [← hxj]
    group
  have hr : x⁻¹ * pinnedX TwistTag.E6.tag k (-sRoot) 1 * x ∈ R₁ := by
    refine ⟨pinnedX TwistTag.E6.tag k e6HighestRoot (ι 1), (mem_thetaRootGroup ι).2 ⟨1, rfl⟩, ?_⟩
    rw [map_one, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← wordElt_negSWord_conj h2]
    group
  refine not_isPGroup_two_of_rootPair h2 isRoot_sRoot x (Subgroup.mem_sup_left hr)
    (Subgroup.mem_sup_right ⟨_, hr, ?_⟩)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hj]
  have hP := diagramMap_conj_pinnedX_negS h2 1
  calc x⁻¹ * (pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k) * x *
        (x⁻¹ * pinnedX TwistTag.E6.tag k (-sRoot) 1 * x) *
        (x⁻¹ * (pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k) * x)⁻¹ =
        x⁻¹ * (pinnedX TwistTag.E6.tag k sRoot 1 *
          (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (-sRoot) 1 *
            (diagramMap TwistTag.E6 k)⁻¹) * (pinnedX TwistTag.E6.tag k sRoot 1)⁻¹) * x := by
        group
    _ = _ := by rw [hP]

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_linear_Levi_involution_forms
    (f : ℕ)
    (hf : 1 ≤ f) (k : Type) [Field k] (hk : Nat.card k = 2 ^ f) :
    ∀ ℓ ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
      (ℓ * diagramMap TwistTag.E6 k) ^ 2 = 1 →
      ((∃ x ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          x * (ℓ * diagramMap TwistTag.E6 k) * x⁻¹ = diagramMap TwistTag.E6 k) ∨
        ∃ x ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          x * (ℓ * diagramMap TwistTag.E6 k) * x⁻¹ =
            pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k) ∧
      ((∃ x ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          x * (ℓ * diagramMap TwistTag.E6 k) * x⁻¹ =
            pinnedX TwistTag.E6.tag k sRoot 1 * diagramMap TwistTag.E6 k) →
        ∃ g ∈ adjointGroup TwistTag.E6.tag k,
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom ≤
              subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
            ¬ IsPGroup 2 ↥((thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom ⊔
              ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom).map
                (MulAut.conj (ℓ * diagramMap TwistTag.E6 k)).toMonoidHom)) := by
  intro ℓ hℓ hsq
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hLG : subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k =
      subsystemGroup TwistTag.E6.tag k setA := inf_eq_left.2 subsystemGroup_le_adjointGroup
  rw [hLG] at hℓ ⊢
  refine ⟨exists_conj_normal_form h2 hℓ hsq, ?_⟩
  rintro ⟨x, hx, hxj⟩
  refine ⟨x⁻¹ * wordElt k negSWord,
    mul_mem (inv_mem (subsystemGroup_le_adjointGroup hx)) (wordElt_mem_adjointGroup _), ?_,
    detector_of_conj h2 (RingHom.id k) hxj⟩
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨c, rfl⟩ := (mem_thetaRootGroup _).1 hr
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    show x⁻¹ * wordElt k negSWord * pinnedX TwistTag.E6.tag k e6HighestRoot ((RingHom.id k) c) *
      (x⁻¹ * wordElt k negSWord)⁻¹ = x⁻¹ * (wordElt k negSWord *
        pinnedX TwistTag.E6.tag k e6HighestRoot ((RingHom.id k) c) * (wordElt k negSWord)⁻¹) *
          x⁻¹⁻¹ by group, wordElt_negSWord_conj h2]
  exact mul_mem (mul_mem (inv_mem hx) (pinnedX_negS_mem_subsystemGroup h2 _)) (by
    rw [inv_inv]
    exact hx)

end CFSG.LieType.Chevalley.E6GraphInvolution
