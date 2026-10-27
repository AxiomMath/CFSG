module

public import CFSG.LocalAnalysis.StandardType.FS81.RootFusionGen

public section

namespace CFSG.Holt.SL6

open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In isSylow2In_map_subtype)

theorem exists_isSylow2In_of_mulEquiv {X : Type} [Group X] {L : Subgroup X} {Γ : Type*} [Group Γ]
    [Finite Γ] (φ : ↥L ≃* Γ) (P : Sylow 2 Γ) :
    ∃ S : Subgroup X, IsSylow2In S L ∧ ∀ y : ↥L, φ y ∈ (P : Subgroup Γ) ↔ (y : X) ∈ S := by
  have : Finite ↥L := Finite.of_equiv Γ φ.symm.toEquiv
  let Q : Sylow 2 ↥L := Sylow.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective P
  have hQ : (Q : Subgroup ↥L) = (P : Subgroup Γ).map φ.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  refine ⟨(Q : Subgroup ↥L).map L.subtype, isSylow2In_map_subtype Q, fun y => ?_⟩
  have h1 : (y : X) ∈ (Q : Subgroup ↥L).map L.subtype ↔ y ∈ (Q : Subgroup ↥L) :=
    Subgroup.mem_map_iff_mem L.subtype_injective
  rw [h1, hQ, Subgroup.mem_map_equiv, MulEquiv.symm_symm]

end CFSG.Holt.SL6
