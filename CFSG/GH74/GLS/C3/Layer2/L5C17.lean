module

public import CFSG.GH74.GLS.C3.Layer2.L5C2
public import CFSG.GH74.GLS.C3.Layer2.L5C14

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Bridge

variable {h : IsAConfig 5 x K T Q S a}

theorem Coord5.fusionHyp_of_model
    (c : Coord5 h) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hn24 : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A)
    {S' : Subgroup G} (hS' : IsSylow2In S' ⊤) (hTS' : T ≤ S')
    {M : Type} [Group M] [Finite M] (ψ : ↥S' ≃* M) (emb : ↥T5 →* M)
    (hemb : ∀ t, ψ ⟨c.iotaT t, hTS' (c.iotaT_mem_T t)⟩ = emb t) :
    FusionHyp M emb (Erel ψ) := by
  have hsymm : ∀ t : ↥T5, ((ψ.symm (emb t) : ↥S') : G) = c.iotaT t := fun t => by
    rw [← hemb t, MulEquiv.symm_apply_apply]
  refine ⟨Erel.equiv ψ, Erel.conj ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg t s hts
    show IsConj ((ψ.symm (emb t) : ↥S') : G) ((ψ.symm (emb s) : ↥S') : G)
    rw [hsymm, hsymm]
    exact c.iotaT_conj hg hts
  · intro A hA i
    obtain ⟨n, hn⟩ := hn24 A hA
    show IsConj ((ψ.symm (emb (elT i)) : ↥S') : G) ((ψ.symm (emb (elT (A i))) : ↥S') : G)
    rw [hsymm, hsymm, c.iotaT_elT, c.iotaT_elT]
    refine isConj_iff.2 ⟨n.1, ?_⟩
    rw [← hn]
    exact (Coord5.rhoG_spec c n i).symm
  · intro x' hx'
    have h1 : IsConj x ((ψ.symm x' : ↥S') : G) := by
      have h2 : IsConj ((ψ.symm (emb x0T5) : ↥S') : G) ((ψ.symm x' : ↥S') : G) := hx'
      rwa [hsymm, c.iotaT_x0] at h2
    have h3 := card_cent_le_of_conj hS'.2.1 ψ (isSylowOf_iff.1 h.sylowT) h1
    rw [card_T_five h c] at h3
    exact h3
  · intro t t' _ hE hext
    exact scp_bridge hS' ψ hE hext
  · intro H hH u hu hu2
    exact thompson_bridge ig_15_15 hs hnab hS' ψ hH hu hu2

end Bridge

end CFSG.GH74.GLS.C3.Layer2.L5
