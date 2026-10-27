module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.E6GraphLeviRealization

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi
open Matrix

section RankOne

variable {τ : Tag} {E : Type} [Field E]

theorem rootSL2_uSL_of_two
    (h2 : (2 : E) = 0) (β : Fin τ.rank → ℤ) (c : E) :
    rootSL2 τ E β (uSL c) = pinnedX τ E β c := by
  rw [rootSL2_uSL_eq]
  congr 1
  rcases pinnedSign_eq τ β with h | h <;> rw [h]
  · exact one_zsmul c
  · rw [neg_zsmul, one_zsmul, neg_eq_self_of_two h2]

theorem rootSL2_vSL_of_two
    (h2 : (2 : E) = 0) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : E) :
    rootSL2 τ E β (vSL c) = pinnedX τ E (-β) c := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := E) hβ
  rw [h, eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε, one_mul]

theorem rootSL2_injective_of_two
    (h2 : (2 : E) = 0) (β : Fin τ.rank → ℤ) :
    Function.Injective (rootSL2 τ E β) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  set W := pinnedWeyl τ E β
  have hB' : simpleRootSL2 τ E (pinnedData τ β).1 B = 1 := by
    have h := hB
    rw [rootSL2_apply] at h
    calc simpleRootSL2 τ E (pinnedData τ β).1 B =
          W⁻¹ * (W * simpleRootSL2 τ E (pinnedData τ β).1 B * W⁻¹) * W := by group
      _ = 1 := by rw [h]; group
  obtain ⟨l, hl, hBl⟩ := (exceptional_ordinary_rank_one_central_image τ E
    (pinnedData τ β).1).choose_spec.2.2.2.2.2.1 B (MonoidHom.mem_ker.2 hB')
  have hl1 : (l : E) = 1 := eq_one_of_mul_self_eq_one_of_two_eq_zero h2 (by rw [← sq]; exact hl)
  refine Subtype.ext ?_
  rw [hBl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]

@[expose] def orderThreeSL2 (E : Type) [Field E] : SL2 E :=
  vSL 1 * (uSL 1 * vSL 1 * (uSL 1)⁻¹)

theorem coe_orderThreeSL2 (h2 : (2 : E) = 0) :
    (orderThreeSL2 E : Matrix (Fin 2) (Fin 2) E) = !![0, 1; 1, 1] := by
  have hn : (-1 : E) = 1 := neg_eq_self_of_two h2 1
  ext i j
  rw [orderThreeSL2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, hn]
  all_goals first
    | linear_combination h2
    | linear_combination 2 * h2

theorem orderThreeSL2_pow_three (h2 : (2 : E) = 0) : orderThreeSL2 E ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_orderThreeSL2 h2, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination h2

theorem orderThreeSL2_ne_one (h2 : (2 : E) = 0) : orderThreeSL2 E ≠ 1 := by
  intro h
  have h' := congrArg (fun B : SL2 E => (B : Matrix (Fin 2) (Fin 2) E) 0 0) h
  simp only [coe_orderThreeSL2 h2, Matrix.SpecialLinearGroup.coe_one] at h'
  simp at h'

theorem not_isPGroup_two_of_mem {G : Type*} [Group G] {H : Subgroup G} {y : G} (hy : y ∈ H)
    (h3 : y ^ 3 = 1) (h1 : y ≠ 1) : ¬ IsPGroup 2 H := by
  intro hP
  obtain ⟨n, hn⟩ := hP ⟨y, hy⟩
  have hn' : y ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hd : orderOf y ∣ Nat.gcd (2 ^ n) 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn')
    (orderOf_dvd_of_pow_eq_one h3)
  have hcop : Nat.gcd (2 ^ n) 3 = 1 :=
    Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact h1 hd

theorem not_isPGroup_two_of_rootPair
    (h2 : (2 : E) = 0) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (x : ModGL τ E) {H : Subgroup (ModGL τ E)}
    (h₁ : x⁻¹ * pinnedX τ E (-β) 1 * x ∈ H)
    (h₂ : x⁻¹ * (pinnedX τ E β 1 * pinnedX τ E (-β) 1 * (pinnedX τ E β 1)⁻¹) * x ∈ H) :
    ¬ IsPGroup 2 H := by
  have hM : rootSL2 τ E β (orderThreeSL2 E) =
      pinnedX τ E (-β) 1 * (pinnedX τ E β 1 * pinnedX τ E (-β) 1 * (pinnedX τ E β 1)⁻¹) := by
    rw [orderThreeSL2, map_mul, map_mul, map_mul, map_inv, rootSL2_uSL_of_two h2,
      rootSL2_vSL_of_two h2 hβ]
  have hy : x⁻¹ * rootSL2 τ E β (orderThreeSL2 E) * x ∈ H := by
    rw [hM]
    have := mul_mem h₁ h₂
    rwa [show x⁻¹ * pinnedX τ E (-β) 1 * x *
        (x⁻¹ * (pinnedX τ E β 1 * pinnedX τ E (-β) 1 * (pinnedX τ E β 1)⁻¹) * x) =
      x⁻¹ * (pinnedX τ E (-β) 1 *
        (pinnedX τ E β 1 * pinnedX τ E (-β) 1 * (pinnedX τ E β 1)⁻¹)) * x by group] at this
  refine not_isPGroup_two_of_mem hy ?_ ?_
  · have e : (x⁻¹ * rootSL2 τ E β (orderThreeSL2 E) * x) ^ 3 =
        x⁻¹ * rootSL2 τ E β (orderThreeSL2 E) ^ 3 * x := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, ← map_pow, orderThreeSL2_pow_three h2, map_one]
    group
  · intro h
    apply orderThreeSL2_ne_one h2
    apply rootSL2_injective_of_two h2 β
    rw [map_one]
    calc rootSL2 τ E β (orderThreeSL2 E) =
          x * (x⁻¹ * rootSL2 τ E β (orderThreeSL2 E) * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group

end RankOne

section Congruence

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Module
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_symplectic_basis)

variable {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ}

theorem exists_symmetric_normal_form (M : GL (Fin n) k) (hM : (M : Matrix (Fin n) (Fin n) k)ᵀ = M) :
    ∃ H C : GL (Fin n) k,
      (M : Matrix (Fin n) (Fin n) k) = H * C * (H : Matrix (Fin n) (Fin n) k)ᵀ ∧
      (((C : Matrix (Fin n) (Fin n) k) = 1 ∧
          ¬∀ v : Fin n → k, v ⬝ᵥ ((M : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0) ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) k) = blockSwapJ n r ∧
          ∀ v : Fin n → k, v ⬝ᵥ ((M : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0) := by
  have hsq : ∀ a : k, IsSquare a := FiniteField.isSquare_of_char_two (ringChar.eq k 2)
  have hBsymm : (Matrix.toBilin' (M : Matrix (Fin n) (Fin n) k)).IsSymm := ⟨fun v w => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
      hM, dotProduct_comm]⟩
  have hBnd : (Matrix.toBilin' (M : Matrix (Fin n) (Fin n) k)).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero
      ((Matrix.isUnit_iff_isUnit_det _).mp M.isUnit).ne_zero)
  by_cases halt : ∀ v : Fin n → k, v ⬝ᵥ ((M : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0
  · have hBalt : (Matrix.toBilin' (M : Matrix (Fin n) (Fin n) k)).IsAlt := fun v => by
      rw [Matrix.toBilin'_apply']
      exact halt v
    obtain ⟨m, b, hd, hb⟩ := exists_symplectic_basis _ hBalt hBnd
    rw [Module.finrank_fin_fun] at hd
    have hmm : m + m = n := by omega
    obtain ⟨H, C, hC, hA, -⟩ :=
      exists_congruence_of_basis M (b.reindex (finSumFinEquiv.trans (finCongr hmm)))
    refine ⟨H, C, hA, Or.inr ⟨m, hd, ?_, halt⟩⟩
    rw [hC]
    ext i j
    obtain ⟨x, rfl⟩ := (finSumFinEquiv.trans (finCongr hmm)).surjective i
    obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr hmm)).surjective j
    rw [BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, ← BilinForm.toMatrix_apply, hb, J_apply_eq_blockSwapJ hmm]
  · push Not at halt
    obtain ⟨x, hx⟩ := halt
    obtain ⟨b, hb⟩ := exists_orthonormal_basis_of_charTwo hsq hBsymm hBnd
      (Or.inr ⟨x, by rw [Matrix.toBilin'_apply']; exact hx⟩)
    obtain ⟨H, C, hC, hA, -⟩ :=
      exists_congruence_of_basis M (b.reindex (finCongr (Module.finrank_fin_fun k)))
    refine ⟨H, C, hA, Or.inl ⟨?_, fun h => hx (h x)⟩⟩
    rw [hC]
    ext i j
    rw [BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply, hb, Matrix.one_apply]
    simp only [(finCongr (Module.finrank_fin_fun k)).symm.injective.eq_iff]

theorem exists_congruence_of_alternating_iff (M M' : GL (Fin n) k)
    (hM : (M : Matrix (Fin n) (Fin n) k)ᵀ = M) (hM' : (M' : Matrix (Fin n) (Fin n) k)ᵀ = M')
    (halt : (∀ v : Fin n → k, v ⬝ᵥ ((M : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0) ↔
      ∀ v : Fin n → k, v ⬝ᵥ ((M' : Matrix (Fin n) (Fin n) k) *ᵥ v) = 0) :
    ∃ D : GL (Fin n) k,
      (D : Matrix (Fin n) (Fin n) k) * M * (D : Matrix (Fin n) (Fin n) k)ᵀ = M' := by
  obtain ⟨H, C, hHC, hC⟩ := exists_symmetric_normal_form M hM
  obtain ⟨H', C', hHC', hC'⟩ := exists_symmetric_normal_form M' hM'
  have hCC : (C : Matrix (Fin n) (Fin n) k) = C' := by
    rcases hC with ⟨hC1, hna⟩ | ⟨r, hr, hCr, ha⟩ <;>
      rcases hC' with ⟨hC1', hna'⟩ | ⟨r', hr', hCr', ha'⟩
    · rw [hC1, hC1']
    · exact absurd (halt.2 ha') hna
    · exact absurd (halt.1 ha) hna'
    · have : r = r' := by omega
      rw [hCr, hCr', this]
  refine ⟨H' * H⁻¹, ?_⟩
  have hHH : ((H⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * H = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hHHt : (H : Matrix (Fin n) (Fin n) k)ᵀ *
      ((H⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ = 1 := by
    rw [← transpose_mul, hHH, transpose_one]
  rw [hHC, hHC', Units.val_mul, transpose_mul, ← hCC]
  calc (H' : Matrix (Fin n) (Fin n) k) * ((H⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        (H * C * (H : Matrix (Fin n) (Fin n) k)ᵀ) *
        (((H⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ * (H' : Matrix (Fin n) (Fin n) k)ᵀ) =
        H' * (((H⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * H) * C *
          ((H : Matrix (Fin n) (Fin n) k)ᵀ *
            ((H⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ) *
            (H' : Matrix (Fin n) (Fin n) k)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hHH, hHHt, Matrix.mul_one, Matrix.mul_one]

end Congruence

@[expose] def negSWord : List (Fin TwistTag.E6.tag.rank) :=
  ([0, 5, 2, 4, 3, 1, 2, 4, 3, 0, 5, 2, 4, 3, 1] : List (Fin 6))

@[expose] def flipSWord : List (Fin TwistTag.E6.tag.rank) :=
  ([0, 5, 2, 4, 3, 2, 4, 0, 5] : List (Fin 6))

theorem negSWord_smul
    : (coxeterSystem TwistTag.E6.tag).wordProd negSWord • e6HighestRoot =
    -sRoot := by
  rw [wordProd_smul]
  decide

theorem flipSWord_smul
    : (coxeterSystem TwistTag.E6.tag).wordProd flipSWord • sRoot = -sRoot := by
  rw [wordProd_smul]
  decide

theorem weylTwist_negSWord :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd negSWord) =
      (coxeterSystem TwistTag.E6.tag).wordProd negSWord :=
  weylTwist_wordProd_eq (by decide)

theorem flipSWord_mem_setA : ∀ i ∈ flipSWord, i ∈ setA := by
  simp only [setA, Set.mem_ofPred_eq]
  decide

theorem isRoot_sRoot : IsRoot TwistTag.E6.tag sRoot :=
  mem_rootFinset.1 (by decide +kernel)

end CFSG.LieType.Chevalley.E6GraphInvolution
