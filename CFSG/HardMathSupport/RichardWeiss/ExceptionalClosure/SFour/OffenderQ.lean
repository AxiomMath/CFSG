module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderCount
public import CFSG.HardMathSupport.RichardWeiss.Proving.EqualityOffender
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem offender_ineq {S L : Subgroup G}
    {r d : ℕ} (e : Fin d ≃ OmegaE r 4)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hUV : ⁅blockV S L, L⁆ ≤ blockV S L)
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) ≤ Wr r 4)
    (A : Subgroup G) (hAJ : A ≤ thompsonJ S) :
    (A ⊓ Subgroup.centralizer (blockV S L : Set G)).relIndex A ≤
      (blockV S L ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockV S L) := by
  classical
  obtain ⟨n, hn1, hn2⟩ := exists_count_le_index_altFix e θ hθV hW A hAJ
  have h4 := altFix_index_le hπ hequiv (A := A)
  have hVne : (Subgroup.centralizer (A : Set G)).relIndex (blockV S L) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h5 := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer (A : Set G)) hUV hVne
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
  exact hn1.trans (hn2.trans (h4.trans h5))

theorem blockV_le_thompsonJ_of_offender {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S)
    {r d : ℕ} (e : Fin d ≃ OmegaE r 4)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G))
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) ≤ Wr r 4) :
    blockV S L ≤ thompsonJ S := by
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hVS : blockV S L ≤ S :=
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.1 (hMV ((le_sup_left : L ≤ L ⊔ S) hl)) v⁻¹).1
      ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  obtain ⟨A, hAmax⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
  have hAJ : A ≤ thompsonJ S := le_iSup₂_of_le A hAmax le_rfl
  exact CFSG.HardMathSupport.RichardWeiss.Proving.le_thompsonJ_of_relIndex_le hAmax hVel hVS
    (offender_ineq e π θ hπ hequiv hθV hUV hW A hAJ)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
