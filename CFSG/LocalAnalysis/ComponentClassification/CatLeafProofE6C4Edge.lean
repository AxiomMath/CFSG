module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Frame

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (blk hom_ext_sl2 blk_zero_tv01 blk_zero_tv10 blk_one_tv01
  blk_one_tv10)
open scoped MatrixGroups Matrix

section Sign

variable (K : Type) [Field K]

@[expose] def sl3SignDiag : SL(3, K) :=
  ⟨Matrix.diagonal ![-1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem sl3SignDiag_mul_self : sl3SignDiag K * sl3SignDiag K = 1 := by
  apply Subtype.ext
  show Matrix.diagonal ![(-1 : K), -1, 1] * Matrix.diagonal ![-1, -1, 1] = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp

theorem conj_sl3SignDiag_tv {i j : Fin 3} (hij : i ≠ j) (c : K) :
    MulAut.conj (sl3SignDiag K) (tv i j c) =
      tv i j (![(-1 : K), -1, 1] i * ![(-1 : K), -1, 1] j * c) := by
  rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right (sl3SignDiag_mul_self K)]
  apply Subtype.ext
  show Matrix.diagonal ![(-1 : K), -1, 1] * (tv i j c : SL(3, K)).val *
    Matrix.diagonal ![-1, -1, 1] = (tv i j _ : SL(3, K)).val
  rw [tv_val hij, tv_val hij]
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all

theorem conj_sl3SignDiag_comp_blk
    :
    (MulAut.conj (sl3SignDiag K)).toMonoidHom.comp (blk K 0) = blk K 0 ∧
      (MulAut.conj (sl3SignDiag K)).toMonoidHom.comp (blk K 1) =
        (blk K 1).comp (diagConj K (-1)) := by
  have hu : ∀ c : K, diagConj K (-1) (tv 0 1 c) = tv 0 1 (-c) := fun c => by
    rw [tv_zero_one_eq_uSL, diagConj_uSL, tv_zero_one_eq_uSL]
    simp
  have hv : ∀ c : K, diagConj K (-1) (tv 1 0 c) = tv 1 0 (-c) := fun c => by
    rw [tv_one_zero_eq_vSL, diagConj_vSL, tv_one_zero_eq_vSL]
    simp
  refine ⟨hom_ext_sl2 (fun c => ?_) (fun c => ?_), hom_ext_sl2 (fun c => ?_) (fun c => ?_)⟩ <;>
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  · rw [blk_zero_tv01, conj_sl3SignDiag_tv K (by decide)]
    simp
  · rw [blk_zero_tv10, conj_sl3SignDiag_tv K (by decide)]
    simp
  · rw [blk_one_tv01, conj_sl3SignDiag_tv K (by decide), hu, blk_one_tv01]
    simp
  · rw [blk_one_tv10, conj_sl3SignDiag_tv K (by decide), hv, blk_one_tv10]
    simp

end Sign

section Edge

variable {K : Type} [Field K]

theorem commute_canonicalRep_e6C4Word
    (M : SL(2, K)) :
    Commute (canonicalRep (coxeterSystem TwistTag.E6.tag) K e6C4Word) (e6F4Rho K 3 M) := by
  have c : ∀ a b : Fin 6, a ≠ b → (Pi.single a 1 : Fin 6 → ℤ) ⬝ᵥ
      (TwistTag.E6.tag.symmetrizedCartan *ᵥ (Pi.single b 1 : Fin 6 → ℤ)) = 0 →
      ∀ A B : SL(2, K), Commute (simpleRootSL2 TwistTag.E6.tag K a A)
        (simpleRootSL2 TwistTag.E6.tag K b B) := fun a b hab h0 A B =>
    commute_simpleRootSL2_of_orth (t := TwistTag.E6) hab h0 A B
  rw [canonicalRep_e6C4Word, ← simpleRootSL2_nSL, ← simpleRootSL2_nSL]
  change Commute _ (simpleRootSL2 TwistTag.E6.tag K ⟨0, by decide⟩ M *
    simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩ M)
  exact ((c 1 0 (by decide) (by decide) _ M).mul_right (c 1 5 (by decide) (by decide) _ M)).mul_left
    ((c 3 0 (by decide) (by decide) _ M).mul_right (c 3 5 (by decide) (by decide) _ M))

variable [Finite K]

theorem exists_e6C4_sl3_one_zero
    :
    ∃ ψ : SL(3, K) →* ModGL TwistTag.E6.tag K,
      ψ.comp (blk K 0) = e6C4Rho K 1 ∧ ψ.comp (blk K 1) = e6C4Rho K 0 := by
  obtain ⟨ψa, ha0, ha1⟩ := exists_e6_sl3 K (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ψb, hb0, hb1⟩ := exists_e6_sl3 K (i := ⟨5, by decide⟩) (j := ⟨4, by decide⟩)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hc0, hc1⟩ := conj_sl3SignDiag_comp_blk K
  set ψb' := ψb.comp (MulAut.conj (sl3SignDiag K)).toMonoidHom with hψb'
  have hb'0 : ψb'.comp (blk K 0) = simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩ := by
    rw [hψb', MonoidHom.comp_assoc, hc0, hb0]
  have hb'1 : ψb'.comp (blk K 1) =
      (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩).comp (diagConj K (-1)) := by
    rw [hψb', MonoidHom.comp_assoc, hc1, ← MonoidHom.comp_assoc, hb1]
  have hca : ψa.range ≤ (simpleRootSL2 TwistTag.E6.tag K ⟨0, by decide⟩).range ⊔
      (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩).range :=
    range_le_of_blk ψa (by rw [ha0]; exact le_sup_left) (by rw [ha1]; exact le_sup_right)
  have hcb : ψb'.range ≤ (simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩).range ⊔
      (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩).range := by
    refine range_le_of_blk ψb' (by rw [hb'0]; exact le_sup_left) ?_
    rw [hb'1, MonoidHom.range_comp]
    exact (Subgroup.map_le_range _ _).trans le_sup_right
  have c : ∀ a b : Fin 6, a ≠ b → (Pi.single a 1 : Fin 6 → ℤ) ⬝ᵥ
      (TwistTag.E6.tag.symmetrizedCartan *ᵥ (Pi.single b 1 : Fin 6 → ℤ)) = 0 →
      ∀ A B : SL(2, K), Commute (simpleRootSL2 TwistTag.E6.tag K a A)
        (simpleRootSL2 TwistTag.E6.tag K b B) := fun a b hab h0 A B =>
    commute_simpleRootSL2_of_orth (t := TwistTag.E6) hab h0 A B
  have hab : ∀ A B, Commute (ψa A) (ψb' B) := by
    intro A B
    have hA := hca ⟨A, rfl⟩
    have hB := hcb ⟨B, rfl⟩
    rw [Subgroup.sup_eq_closure] at hA hB
    refine commute_of_mem_closure ?_ hA hB
    rintro _ (⟨A', rfl⟩ | ⟨A', rfl⟩) _ (⟨B', rfl⟩ | ⟨B', rfl⟩)
    · exact c 0 5 (by decide) (by decide) A' B'
    · exact c 0 4 (by decide) (by decide) A' B'
    · exact c 2 5 (by decide) (by decide) A' B'
    · exact c 2 4 (by decide) (by decide) A' B'
  refine ⟨(MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K e6C4Word)).toMonoidHom.comp
    (pairHom ψa ψb' hab), MonoidHom.ext fun M => ?_, MonoidHom.ext fun M => ?_⟩
  · rw [(e6C4Rho_eq_e6F4Rho K).1, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pairHom_apply, ← MonoidHom.comp_apply ψa, ha0,
      ← MonoidHom.comp_apply ψb', hb'0]
    change _ * e6F4Rho K 3 M * _ = e6F4Rho K 3 M
    rw [(commute_canonicalRep_e6C4Word M).eq, mul_inv_cancel_right]
  · rw [e6C4Rho_zero_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, pairHom_apply, ← MonoidHom.comp_apply ψa, ha1,
      ← MonoidHom.comp_apply ψb', hb'1, MonoidHom.comp_apply]

end Edge

end CFSG.ComponentClassification.CatLeafProof
