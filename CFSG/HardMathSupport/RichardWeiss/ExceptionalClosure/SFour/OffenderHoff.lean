module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderEquality
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderFixed

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender (IsExp2 orbitStab)

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem hoff_of_not_full {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) {d : ℕ} (hd : d = 7 ∨ 9 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hnf : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ¬ ((¬ ∃ p, ∀ g ∈ (A.subgroupOf (L ⊔ S)).map θ, g p = p) ∧
        (∀ i : Fin d, Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) i) = 2) ∧
        Nat.card (orbitStab ((A.subgroupOf (L ⊔ S)).map θ)) =
          Nat.card ((A.subgroupOf (L ⊔ S)).map θ))) :
    ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Nat.card ((A.subgroupOf (L ⊔ S)).map θ) ≤
        (altFix d ((A.subgroupOf (L ⊔ S)).map θ)).index := by
  classical
  intro A hAmax
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hLM : L ≤ L ⊔ S := le_sup_left
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hVS : blockV S L ≤ S :=
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := hVn l (hLM hl) v⁻¹ ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  have hAM : A ≤ L ⊔ S := hAmax.1.trans hSM
  have h1 := altFix_index_le hπ hequiv (A := A)
  have hVne : (Subgroup.centralizer (A : Set G)).relIndex (blockV S L) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer (A : Set G)) hUV hVne
  have h3 := relIndex_le_of_isMaxElemAbelian hAmax hVel hVS
  have h4 := relIndex_le_card_image hAM θ hθV
  have hoffend : (altFix d ((A.subgroupOf (L ⊔ S)).map θ)).index ≤
      Nat.card ((A.subgroupOf (L ⊔ S)).map θ) := h1.trans (h2.trans (h3.trans h4))
  have hexp : IsExp2 ((A.subgroupOf (L ⊔ S)).map θ) := by
    rintro g ⟨a, ha, rfl⟩
    have hsq : a * a = 1 := by
      apply Subtype.ext
      have := hAmax.2.1.2 _ (Subgroup.mem_subgroupOf.1 ha)
      simpa [pow_two] using this
    rw [← map_mul, hsq, map_one]
  have hne : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hd' : Nat.card (Fin d) = 7 ∨ 9 ≤ Nat.card (Fin d) := by
    simpa [Nat.card_eq_fintype_card] using hd
  rw [index_altFix] at hoffend ⊢
  exact card_le_offIdx_of_shape hexp hoffend hd' (hnf A hAmax)

theorem commutator_ne_bot_of_moved_pair_of_not_full {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {d : ℕ} (hd : d = 7 ∨ 9 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hnf : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ¬ ((¬ ∃ p, ∀ g ∈ (A.subgroupOf (L ⊔ S)).map θ, g p = p) ∧
        (∀ i : Fin d, Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) i) = 2) ∧
        Nat.card (orbitStab ((A.subgroupOf (L ⊔ S)).map θ)) =
          Nat.card ((A.subgroupOf (L ⊔ S)).map θ)))
    {p q : Fin d} (hpq : p ≠ q)
    (hJ : ∀ m : ↥(L ⊔ S), (m : G) ∈ thompsonJ S →
      (θ m p = p ∧ θ m q = q) ∨ (θ m p = q ∧ θ m q = p))
    (s : ↥(L ⊔ S)) (hsS : (s : G) ∈ S) (hs1 : θ s p ≠ p) (hs2 : θ s p ≠ q) :
    ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥ :=
  commutator_ne_bot_of_moved_pair hA hSL (by omega) π θ hπ hequiv hθV
    (hoff_of_not_full hA hd π θ hπ hequiv hθV hnf) hpq hJ s hsS hs1 hs2

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
