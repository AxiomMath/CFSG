module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4L2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4L
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympL4Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open scoped commutatorElement

variable {F : Type} [Field F]

theorem exists_scalar_of_conjAut_eq [Finite F] {X Y : GL (Fin 4) F}
    (h : conjAut 4 F X = conjAut 4 F Y) :
    ∃ lam : Fˣ, X = GeneralLinearGroup.scalar (Fin 4) lam * Y := by
  have h1 : conjAut 4 F (X * Y⁻¹) * fieldAut 4 F 1 = 1 := by
    rw [map_one, mul_one, map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
  exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩

theorem conjAut_dualAut_ne [Finite F] (A B : GL (Fin 4) F) :
    conjAut 4 F A * dualAut 4 F ≠ conjAut 4 F B := by
  intro h
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (n := 4) (K := F) (by norm_num)
  have : dualAut 4 F = conjAut 4 F (A⁻¹ * B) := by
    rw [map_mul, map_inv, ← h]
    group
  rw [this]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem lin_or_graph {u : MulAut (projectiveSL 4 F)} (h : Surv4Orth u) :
    (∃ A : GL (Fin 4) F, IsT12 A ∧ u = conjAut 4 F A) ∨
      ∃ A : GL (Fin 4) F, (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A ∧
        u = conjAut 4 F A * dualAut 4 F := by
  rcases h with ⟨B, hB, hfr, rfl⟩ | ⟨A, c, hc, hns, rfl⟩ | ⟨A, hu, hA⟩
  · exact Or.inl ⟨B, Or.inl ⟨hB, hfr⟩, rfl⟩
  · exact Or.inl ⟨A, Or.inr ⟨c, hc, hns⟩, rfl⟩
  · exact Or.inr ⟨A, hA, hu⟩

theorem eq_of_mem_commutator {I : Subgroup (projectiveSL 4 F)}
    {φ : SpecialLinearGroup (Fin 4) F →* SpecialLinearGroup (Fin 4) F}
    (hφ : ∀ s ∈ I.comap (proj 4 F), proj 4 F (φ s) = proj 4 F s) :
    ∀ s ∈ ⁅I.comap (proj 4 F), I.comap (proj 4 F)⁆, φ s = s := by
  have hc : ∀ s ∈ I.comap (proj 4 F),
      ∃ t ∈ center (SpecialLinearGroup (Fin 4) F), φ s = t * s := by
    intro s hs
    refine ⟨φ s * s⁻¹, scalars_le_center 4 F ?_, by group⟩
    have : φ s * s⁻¹ ∈ (proj 4 F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ s hs, mul_inv_cancel]
    rwa [ker_proj] at this
  have hle : ⁅I.comap (proj 4 F), I.comap (proj 4 F)⁆ ≤
      MonoidHom.eqLocus φ (MonoidHom.id _) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨t, ht, hta⟩ := hc a ha
    obtain ⟨t', ht', htb⟩ := hc b hb
    show φ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hta, htb, commutator_central_left ht,
      commutator_central_right ht']
  exact fun s hs => hle hs

theorem transpose_mul_of_graph {A : GL (Fin 4) F} {s : SpecialLinearGroup (Fin 4) F}
    (h : slConjugation 4 F A (slGraphAut 4 F s) = s) :
    (s : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (s : Matrix (Fin 4) (Fin 4) F) = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  set S : GL (Fin 4) F := SpecialLinearGroup.toGL s with hS
  have hm := congrArg (fun t : SpecialLinearGroup (Fin 4) F =>
    ((SpecialLinearGroup.toGL t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
  simp only [toGL_slConjugation, Units.val_mul] at hm
  have hg : ((SpecialLinearGroup.toGL (slGraphAut 4 F s) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = ((S⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    rw [hS, ← map_inv]
    rfl
  rw [hg] at hm
  have hA1 := inv_mul_self A
  have hA2 := mul_inv_self A
  have hss : (S : Matrix (Fin 4) (Fin 4) F)ᵀ * ((S⁻¹ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← transpose_mul, inv_mul_self, transpose_one]
  have e1 : ((S⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (S : Matrix (Fin 4) (Fin 4) F) *
        (A : Matrix (Fin 4) (Fin 4) F) := by
    rw [← hm]
    simp only [Matrix.mul_assoc]
    rw [hA1, Matrix.mul_one, ← Matrix.mul_assoc, hA1, Matrix.one_mul]
  show (S : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
    (S : Matrix (Fin 4) (Fin 4) F) = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  calc (S : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (S : Matrix (Fin 4) (Fin 4) F)
      = (S : Matrix (Fin 4) (Fin 4) F)ᵀ * (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (S : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F)) *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        simp only [Matrix.mul_assoc]
        rw [hA2, Matrix.mul_one]
    _ = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← e1, hss, Matrix.one_mul]

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
