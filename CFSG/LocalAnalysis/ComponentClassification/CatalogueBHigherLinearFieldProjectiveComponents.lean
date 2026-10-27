module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearField

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

theorem pgl_projection_central_kernel (n : ℕ) (K : Type u) [Field K] :
    (ProjGenLinGroup.mk : GL (Fin n) K →* ProjGenLinGroup (Fin n) K).ker ≤
      Subgroup.center (GL (Fin n) K) := by
  rw [ProjGenLinGroup.ker_mk]

theorem projective_pComponent_lift (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] (M : Subgroup (ProjGenLinGroup (Fin n) K))
    (hM : CFSG.IsPComponent p M) :
    ∃ L : Subgroup (GL (Fin n) K), CFSG.IsPComponent p L ∧
      L.map ProjGenLinGroup.mk = M := by
  obtain ⟨L, hL, hLM, _⟩ := CatalogueBCentralQuotient.pComponent_exists_lift p
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
    (pgl_projection_central_kernel n K) M hM
  exact ⟨L, hL, hLM⟩

theorem projective_pComponent_classification (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (M : Subgroup (ProjGenLinGroup (Fin n) K)) (hM : CFSG.IsPComponent p M) :
    2 ≤ n ∧ (n ≠ 2 ∨ Nat.card K ≠ 2) ∧ (n ≠ 2 ∨ Nat.card K ≠ 3) ∧
      M = pslRange n K ∧ CFSG.IsQuasisimple M := by
  obtain ⟨L, hL, hLM⟩ := projective_pComponent_lift n K p M hM
  obtain ⟨hn2, h22, h23, hLeq, hLquasi⟩ :=
    CatalogueBGeneralLinear.pComponent_classification n K hn p L hL
  have hMeq : M = pslRange n K := by
    rw [← hLM, hLeq]
    exact (pslRange_eq_map n K).symm
  have hMquasi : CFSG.IsQuasisimple M := by
    rw [← hLM]
    exact (CatalogueBCentralQuotient.pComponent_quasisimple_iff
      ProjGenLinGroup.mk (pgl_projection_central_kernel n K) p L hL).mp hLquasi
  exact ⟨hn2, h22, h23, hMeq, hMquasi⟩

theorem projective_small_no_pComponent (K : Type u) [Field K] [Finite K]
    (hsmall : Nat.card K = 2 ∨ Nat.card K = 3) (p : ℕ) [Fact p.Prime]
    (M : Subgroup (ProjGenLinGroup (Fin 2) K)) : ¬ CFSG.IsPComponent p M := by
  intro hM
  obtain ⟨L, hL, _⟩ := projective_pComponent_lift 2 K p M hM
  exact CatalogueBGeneralLinear.generalLinear_small_no_pComponent 2 K
    (Or.inr ⟨rfl, hsmall⟩) p L hL

@[expose] def projectivePComponentEquivPSL
    (n : ℕ) (K : Type u) [Field K] [Finite K] (hn : 1 ≤ n)
    (p : ℕ) [Fact p.Prime] (M : Subgroup (ProjGenLinGroup (Fin n) K))
    (hM : CFSG.IsPComponent p M) : M ≃* ProjectiveSpecialLinearGroup (Fin n) K :=
  (MulEquiv.subgroupCongr
    (projective_pComponent_classification n K hn p M hM).2.2.2.1).trans
      (pslRangeEquiv n K).symm

theorem projectivePComponentEquivPSL_toPGL
    (n : ℕ) (K : Type u) [Field K] [Finite K] (hn : 1 ≤ n)
    (p : ℕ) [Fact p.Prime] (M : Subgroup (ProjGenLinGroup (Fin n) K))
    (hM : CFSG.IsPComponent p M) (x : M) :
    ProjectiveSpecialLinearGroup.toPGL (projectivePComponentEquivPSL n K hn p M hM x) =
      x.val :=
  pslRangeEquiv_symm_toPGL n K _

end

end CFSG.ComponentClassification.CatalogueBHigherLinearField
