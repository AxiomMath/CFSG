module

public import CFSG.ClassicalInvolution.Q3.TL3T37

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem pairVec_not_comm_list : ∀ b : Bool, ∀ i j : Fin 4, i ≠ j →
    ∃ k ∈ (bif b then kList else kStarList),
      k * ofVec (TL4.pairVec i j) ≠ ofVec (TL4.pairVec i j) * k := by
  decide +kernel

theorem not_comm_memBar_pairVec (hn : 5 ≤ n) {δ : Finset (Fin n)} (hδ : δ.card = 4) (b : Bool)
    {a c : Fin n} (ha : a ∈ δ) (hc : c ∈ δ) (hac : a ≠ c) :
    ¬ ∀ x ∈ memBar δ hδ b,
      x * mkQ n (ofVec (TL4.pairVec a c)) = mkQ n (ofVec (TL4.pairVec a c)) * x := by
  intro h
  set ι := emb δ hδ with hι
  have hr : ∀ x ∈ δ, ∃ i, ι i = x := fun x hx => by
    have : x ∈ Set.range ι := by rw [hι, range_emb]; exact_mod_cast hx
    exact this
  obtain ⟨i, rfl⟩ := hr a ha
  obtain ⟨j, rfl⟩ := hr c hc
  have hij : i ≠ j := fun e => hac (by rw [e])
  obtain ⟨k, hk, hne⟩ := pairVec_not_comm_list b i j hij
  have hx := h _ (TC.Thin.mkQ_embed_mem_memBar hk)
  rw [← TC.Thin.embedVec_pairVec, ← TC.Thin.embed_ofVec, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul] at hx
  exact hne (embed_injective ι
    (mkQ_inj_of_supportedOn hn (embed_supportedOn ι _) (embed_supportedOn ι _) hx))

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem comm_orb_K {x : G} (hx : x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)) {k : G} (hk : k ∈ K) :
    x * k = k * x := by
  have hle : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ Subgroup.centralizer (K : Set G) :=
    pSpan_le fun L hL l hl => Subgroup.mem_centralizer_iff.mpr fun k' hk' =>
      comm_of_mem_omegaNbr hS.hyp hS.two hS.adj.1 (hS.orb_subset hL) k' hk' l hl
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) k hk).symm

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
