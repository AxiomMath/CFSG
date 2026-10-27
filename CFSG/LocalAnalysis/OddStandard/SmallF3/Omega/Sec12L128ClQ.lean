module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClWr
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_normal_perfect_type {Q : Type} [Group Q]
    (hQ : IsO4Plus4 Q ∨ IsO4Minus4 Q ∨ IsL34Two Q) (P : Subgroup Q) [hPn : P.Normal]
    (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥) :
    P.index = 2 ∧ (Nonempty (↥P ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))) ∨
      LieModel ↥P .PSL 2 2 4 ∨ LieModel ↥P .PSL 3 2 2) := by
  rcases hQ with h | ⟨E, hEn, hEi, hE, -⟩ | ⟨E, hEn, hEi, hE, -⟩
  ·
    obtain ⟨e⟩ : Nonempty (Q ≃* WrZ2 ↥(alternatingGroup (Fin 5))) := h
    let N : Subgroup (WrZ2 ↥(alternatingGroup (Fin 5))) := P.map e.toMonoidHom
    haveI : N.Normal := hPn.map e.toMonoidHom e.surjective
    have hNperf : ⁅N, N⁆ = N := by
      rw [← Subgroup.map_commutator, hP]
    have hN1 : N ≠ ⊥ := fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective P e.injective).mp h)
    obtain ⟨hidx, ⟨f⟩⟩ := sec128_pf_wr_type N hNperf hN1
    refine ⟨?_, Or.inl ⟨(P.equivMapOfInjective e.toMonoidHom e.injective).trans f⟩⟩
    rw [← Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective P]
    exact hidx
  ·
    have hPE : P ≤ E := sec128_perfect_le_index_two E hEi P hP
    haveI : IsSimpleGroup ↥E :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hE
    have hPeq : P = E := sec128_eq_of_simple E P hPE hP1
    subst hPeq
    exact ⟨hEi, Or.inr (Or.inl hE)⟩
  ·
    have hPE : P ≤ E := sec128_perfect_le_index_two E hEi P hP
    haveI : IsSimpleGroup ↥E :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hE
    have hPeq : P = E := sec128_eq_of_simple E P hPE hP1
    subst hPeq
    exact ⟨hEi, Or.inr (Or.inr hE)⟩

end CFSG.OddStandard.SmallF3.Omega
