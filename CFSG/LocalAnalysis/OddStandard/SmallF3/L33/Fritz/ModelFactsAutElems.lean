module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsData

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

structure IsL33Model {L : Type} [Group L] (M : AutModel L (Equiv.Perm (Fin 26))) : Prop where
  P_eq : M.P = QP.originalSubgroup
  A_eq : M.A = QA.originalSubgroup

theorem exists_isL33Model {L : Type} [Group L]
    (hL : LieModel L .PSL 3 3 1) : ∃ M : AutModel L (Equiv.Perm (Fin 26)), IsL33Model M := by
  obtain ⟨M, hP, hA⟩ := exists_autModel hL
  exact ⟨M, ⟨hP, hA⟩⟩

namespace IsL33Model

variable {L : Type} [Group L] {M : AutModel L (Equiv.Perm (Fin 26))}

theorem P_le_A (h : IsL33Model M) : M.P ≤ M.A := by
  rw [h.P_eq, h.A_eq]
  exact model_P_le_A

theorem modelX_mem_P (h : IsL33Model M) : modelX ∈ M.P := by
  rw [h.P_eq]
  exact model_inner_mem.1

theorem modelY_mem_P (h : IsL33Model M) : modelY ∈ M.P := by
  rw [h.P_eq]
  exact model_inner_mem.2.1

theorem modelK_mem_A (h : IsL33Model M) : modelK ∈ M.A := by
  rw [h.A_eq]
  exact model_outer_mem.1

theorem modelK_not_mem_P (h : IsL33Model M) : modelK ∉ M.P := by
  rw [h.P_eq]
  exact model_outer_mem.2

theorem modelG1_mem_A (h : IsL33Model M) : modelG1 ∈ M.A := by
  rw [h.A_eq]
  exact model_inner_mem.2.2.2.2.2.2.1

theorem modelG2_mem_A (h : IsL33Model M) : modelG2 ∈ M.A := by
  rw [h.A_eq]
  exact model_inner_mem.2.2.2.2.2.2.2

@[expose] noncomputable def elX (h : IsL33Model M) : L := M.e.symm ⟨modelX, h.modelX_mem_P⟩

@[expose] noncomputable def elY (h : IsL33Model M) : L := M.e.symm ⟨modelY, h.modelY_mem_P⟩

@[expose] noncomputable def elK (h : IsL33Model M) : MulAut L := liftA M modelK h.modelK_mem_A

@[expose] noncomputable def elG1 (h : IsL33Model M) : MulAut L := liftA M modelG1 h.modelG1_mem_A

@[expose] noncomputable def elG2 (h : IsL33Model M) : MulAut L := liftA M modelG2 h.modelG2_mem_A

theorem e_elX (h : IsL33Model M) : (M.e h.elX : Equiv.Perm (Fin 26)) = modelX := by
  simp only [elX, MulEquiv.apply_symm_apply]

theorem e_elY (h : IsL33Model M) : (M.e h.elY : Equiv.Perm (Fin 26)) = modelY := by
  simp only [elY, MulEquiv.apply_symm_apply]

theorem ι_elK (h : IsL33Model M) : M.ι h.elK = modelK := by
  simp only [elK, ι_liftA]

theorem ι_elG1 (h : IsL33Model M) : M.ι h.elG1 = modelG1 := by
  simp only [elG1, ι_liftA]

theorem ι_elG2 (h : IsL33Model M) : M.ι h.elG2 = modelG2 := by
  simp only [elG2, ι_liftA]

theorem ι_conj (h : IsL33Model M) (a : L) :
    M.ι (MulAut.conj a) = (M.e a : Equiv.Perm (Fin 26)) := by
  rw [← liftA_e M h.P_le_A a, ι_liftA]

theorem e_apply (φ : MulAut L) (u : L) :
    (M.e (φ u) : Equiv.Perm (Fin 26)) = M.ι φ * (M.e u : Equiv.Perm (Fin 26)) * (M.ι φ)⁻¹ := by
  exact M.spec φ u

theorem apply_eq_iff (φ : MulAut L) (u v : L) :
    φ u = v ↔
      M.ι φ * (M.e u : Equiv.Perm (Fin 26)) * (M.ι φ)⁻¹ = (M.e v : Equiv.Perm (Fin 26)) := by
  constructor
  · intro h
    rw [← h]
    exact (e_apply φ u).symm
  · intro h
    apply M.e.injective
    apply Subtype.ext
    rw [e_apply φ u]
    exact h

end IsL33Model

end CFSG.OddStandard.SmallF3.L33
