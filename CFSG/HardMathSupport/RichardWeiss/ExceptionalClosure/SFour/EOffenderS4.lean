module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.EOffender
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderQ
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eOffenderData_of_section {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S)
    {r d : ℕ} (e : Fin d ≃ OmegaE r 4)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) ≤ Wr r 4) :
    EOffenderData S (blockV S L) := by
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.1 (hMV ((le_sup_left : L ≤ L ⊔ S) hl)) v⁻¹).1
      ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  refine ⟨CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L,
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le,
    fun x hx => hMV ((le_sup_right : S ≤ L ⊔ S) hx), fun A hAmax => ?_⟩
  have hAJ : A ≤ thompsonJ S := le_iSup₂_of_le A hAmax le_rfl
  have := offender_ineq e π θ hπ hequiv hθV hUV hW A hAJ
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left] at this ⊢
  exact this

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
