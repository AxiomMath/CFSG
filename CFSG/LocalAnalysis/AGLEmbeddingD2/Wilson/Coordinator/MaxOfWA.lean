module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Hover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.NormMaxQ11
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JInv

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem normMax_Q11_of_WA
    (hWA : ∀ T' : Subgroup J, C0p ≤ T' → T' ≤ M2 → ¬ T' ≤ C0p →
      (∃ i : Fin 7, rRep i ∈ T') ∨ mElt ∈ T') :
    NormMax (Q11Sylow : Subgroup J) := by
  have hgens : c1j ∈ Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) ∧
      nrm₂ ∈ Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) ∧
      qz ∈ Subgroup.normalizer (Q11 : Set J) ⊓ Subgroup.centralizer ({jInv} : Set J) :=
    ⟨NormalizerAction.C0_le_inf (Subgroup.subset_closure (Set.mem_insert _ _)),
      NormalizerAction.C0_le_inf (Subgroup.subset_closure (Set.mem_insert_of_mem _
        (Set.mem_insert _ _))),
      NormalizerAction.C0_le_inf (Subgroup.subset_closure (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl)))⟩
  have hover := hover_of_WA NormalizerAction.gam_conj_jInv hgens hWA
  refine Proving.normMax_Q11_of_hover ?_
  rw [Q11Sylow_coe]
  exact hover

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
