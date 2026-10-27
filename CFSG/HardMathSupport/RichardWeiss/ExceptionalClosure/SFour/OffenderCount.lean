module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderAux
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.IndexLower
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G] [Finite G]

theorem exists_count_le_index_altFix {S L : Subgroup G}
    {r d : ℕ} (e : Fin d ≃ OmegaE r 4) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) ≤ Wr r 4)
    (A : Subgroup G) (hAJ : A ≤ thompsonJ S) :
    ∃ n : ℕ, (Subgroup.centralizer (blockV S L : Set G)).relIndex A ≤ n ∧
      n ≤ (altFix d ((A.subgroupOf (L ⊔ S)).map θ)).index := by
  classical
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hAM : A ≤ L ⊔ S := hAJ.trans ((thompsonJ_le_self S).trans hSM)
  let θ' : ↥(L ⊔ S) →* Perm (OmegaE r 4) := e.permCongrHom.toMonoidHom.comp θ
  let a : Fin r → Fin d := fun k => e.symm (Sum.inl (k, false))
  let b : Fin r → Fin d := fun k => e.symm (Sum.inl (k, true))
  let γ : Fin 4 → Fin d := fun j => e.symm (Sum.inr j)
  have hainj : Function.Injective a := fun i j h => by
    have := Sum.inl.inj (e.symm.injective h)
    exact (Prod.mk.inj this).1
  have hba : ∀ i j, b i ≠ a j := fun i j h => by
    have := Sum.inl.inj (e.symm.injective h)
    exact absurd (Prod.mk.inj this).2 (by simp)
  have haγ : ∀ i j, a i ≠ γ j := fun i j h => Sum.inl_ne_inr (e.symm.injective h)
  have hbγ : ∀ i j, b i ≠ γ j := fun i j h => Sum.inl_ne_inr (e.symm.injective h)
  set E : Subgroup (Perm (Fin d)) := (A.subgroupOf (L ⊔ S)).map θ with hE
  set E' : Subgroup (Perm (OmegaE r 4)) := (A.subgroupOf (L ⊔ S)).map θ' with hE'
  have hE'E : E' = E.map e.permCongrHom.toMonoidHom := by
    rw [hE', hE, Subgroup.map_map]
  have hE'W : E' ≤ Wr r 4 := by
    refine le_trans (Subgroup.map_mono ?_) hW
    intro m hm
    exact Subgroup.mem_subgroupOf.2 (hAJ (Subgroup.mem_subgroupOf.1 hm))
  have hγE : ∀ g ∈ E, g (γ 0) = γ 0 := by
    intro g hg
    have hmem : e.permCongrHom.toMonoidHom g ∈ Wr r 4 :=
      hE'W (hE'E ▸ ⟨g, hg, rfl⟩)
    have h1 := Wr_apply_inr hmem 0
    have h2 : e (g (e.symm (Sum.inr 0))) = Sum.inr 0 := h1
    simpa using congrArg e.symm h2
  have ht : ∀ k ∈ movedPairs E', ∃ g ∈ E, g (b k) = a k := by
    intro k hk
    obtain ⟨g', hg', hgk⟩ := mem_movedPairs.1 hk
    rw [hE'E] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    refine ⟨g, hg, ?_⟩
    have h2 : e (g (e.symm (Sum.inl (k, true)))) = Sum.inl (k, false) := hgk
    simpa [a, b] using congrArg e.symm h2
  have hlow := two_pow_le_index_altFix a b (γ 0) hainj hba (fun i => haγ i 0)
    (fun i => hbγ i 0) E hγE (movedPairs E') ht
  have h2 := relIndex_le_card_image hAM θ hθV
  have h3 : Nat.card E ≤ 2 ^ (movedPairs E').card := by
    have hcard : Nat.card E = Nat.card E' := by
      rw [hE'E]
      exact (Subgroup.card_map_of_injective e.permCongrHom.injective).symm
    rw [hcard]
    exact card_le_two_pow_movedPairs hE'W
  exact ⟨_, h2.trans h3, hlow⟩

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
