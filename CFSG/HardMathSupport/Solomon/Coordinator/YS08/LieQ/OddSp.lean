module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddForm
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl

section Sp

variable (r : ℕ) {F : Type} [Field F] [Finite F]

theorem ea1_Sp : EA1ε (spForm r F) (fun _ => True) (natRep (StatedSp r F)) 1 := by
  have hσ : (spForm r F).σ = RingEquiv.refl F := rfl
  intro x y _ hxy
  obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry r F
    { toFun := fun v => v + (spForm r F).β x v • y + (spForm r F).β y v • x
      map_add' := fun u v => by
        simp only [(spForm r F).add_right, add_smul]
        abel
      map_smul' := fun a v => by
        simp only [(spForm r F).smul_right, RingHom.id_apply, smul_add, smul_smul] }
    ((spForm r F).β_siegel hσ (spForm_self r F) hxy)
  exact ⟨0, g, fun v => by rw [hg v, zero_smul, add_zero, one_mul]; rfl⟩

theorem ea2_Sp : EA2ε (spForm r F) (fun _ => True) (natRep (StatedSp r F)) := by
  have hσ : (spForm r F).σ = RingEquiv.refl F := rfl
  intro x _
  obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry r F
    { toFun := fun v => v + (spForm r F).β x v • x
      map_add' := fun u v => by
        simp only [(spForm r F).add_right, add_smul]
        abel
      map_smul' := fun a v => by
        simp only [(spForm r F).smul_right, RingHom.id_apply, smul_add, smul_smul] }
    ((spForm r F).β_transvection hσ (spForm_self r F) x)
  exact ⟨1, g, one_ne_zero, fun v => by rw [hg v, one_mul]; rfl⟩

variable {q : ℕ} [Fact q.Prime] [CharP F q]

theorem radRigidInner_PSp (hr : 2 ≤ r) : RadRigidInner q (StatedProj (StatedSp r F)) := by
  have hdim : 3 ≤ Module.finrank F (Fin r ⊕ Fin r → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine radRigidInner_of_rigid (H := StatedSp r F)
    ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime q _) (natRep (StatedSp r F)) (natRep_injective _)
    (fun Q => isoFlag (spForm r F) (natRep (StatedSp r F)) Q) (fun Q _ => isoFlag_zero _ _ Q)
    (fun Q _ => ⟨_, isoFlag_top _ _ Q⟩)
    (fun Q _ => normalizer_le_flagStab_isoFlag _ _ (isIsometric_natRep_statedSp r F) Q)
    (fun Q hQ => le_flagKernel_isoFlag _ _ q (isIsometric_natRep_statedSp r F) Q hQ)
    (fun x hx => mem_statedScalars_of_natRep _ x hx) ?_
  exact rigidInner_form (spForm r F) (fun _ => True) (spForm r F).IsTotallyIsotropic
    (natRep (StatedSp r F)) (fun Q => isoFlag (spForm r F) (natRep (StatedSp r F)) Q) (Or.inl rfl)
    (fun c => rfl) hdim (fun U hU => hU) (fun U _ v _ => trivial) (natRep_injective _)
    (ea1_Sp r) (Or.inl (ea2_Sp r))
    (fun Q _ => ⟨isoSeq (spForm r F) (natRep (StatedSp r F)) Q, Module.finrank F (Fin r ⊕ Fin r → F),
      isoSeq_zero _ _ Q, isoSeq_mono _ _ Q, isoSeq_isTotallyIsotropic _ _ Q, rfl⟩)
    (isIsometric_natRep_statedSp r F)

end Sp

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
