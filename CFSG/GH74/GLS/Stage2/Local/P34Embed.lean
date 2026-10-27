module

public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingSylow
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open CFSG.DisconnectedInvolutionGraph.Helpers

section Rank

theorem pRank_eq_zero_of_card_eq_one {Q : Type} [Group Q] [Finite Q] (h : Nat.card Q = 1) :
    pRank 2 Q = 0 := by
  unfold pRank
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro r ⟨A, -, hA⟩
  have h1 : Nat.card ↥A ≤ Nat.card Q := Subgroup.card_le_card_group A
  rw [h, hA] at h1
  have h2 : 2 ^ r ≤ 2 ^ 0 := by simpa using h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

variable {G : Type} [Group G] [Finite G]

theorem even_card_of_pRank {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hr : 1 ≤ pRank 2 ↥Q) :
    Even (Nat.card ↥Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rcases k with _ | k
  · exfalso
    have := pRank_eq_zero_of_card_eq_one (Q := ↥Q) (by simpa using hk)
    omega
  · rw [hk]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩

end Rank

section Strong

variable {G : Type} [Group G] [Finite G]

theorem not_exists_stronglyEmbedded (hstd : Std G) : ¬ ∃ M : Subgroup G, DisconnectedInvolutionGraph.Helpers.IsStronglyEmbedded M := by
  rintro ⟨M, hM⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 M) := inferInstance
  obtain ⟨S, hS⟩ := stronglyEmbedded_sylow_inheritance M hM T
  have hSM : (S : Subgroup G) ≤ M := by
    rw [← hS]
    exact Subgroup.map_subtype_le _
  have hrank : 3 ≤ pRank 2 ↥(S : Subgroup G) := by
    rw [(SectionRank.pRank_sylow S).2]
    exact hstd.rank.1
  apply hstd.noUniq
  refine ⟨M, hM.1, S, fun _ => ?_, fun h => absurd h (by omega)⟩
  refine iSup_le fun Q => iSup_le fun hQS => iSup_le fun hQ2 => iSup_le fun _ => ?_
  have hQ : IsPGroup 2 ↥Q := IsPGroup.to_le S.isPGroup' hQS
  exact stronglyEmbedded_even_subgroup_normalizer_le M hM Q (hQS.trans hSM)
    (even_card_of_pRank hQ (by omega))

omit [Finite G] in
theorem orderOf_eq_of_isConj' {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

omit [Finite G] in
theorem closure_involutions_eq_top (hs : IsSimpleGroup G) {z : G} (hz : orderOf z = 2) :
    Subgroup.closure {t : G | orderOf t = 2} = ⊤ := by
  have hN : Subgroup.normalClosure {t : G | orderOf t = 2} ≠ ⊥ := by
    intro h
    have hzmem : z ∈ Subgroup.normalClosure {t : G | orderOf t = 2} :=
      Subgroup.subset_normalClosure hz
    rw [h, Subgroup.mem_bot] at hzmem
    rw [hzmem, orderOf_one] at hz
    omega
  have htop : Subgroup.normalClosure {t : G | orderOf t = 2} = ⊤ :=
    (hs.eq_bot_or_eq_top_of_normal _).resolve_left hN
  have hle : Subgroup.normalClosure {t : G | orderOf t = 2} ≤
      Subgroup.closure {t : G | orderOf t = 2} := by
    rw [Subgroup.normalClosure]
    refine Subgroup.closure_mono ?_
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    exact (orderOf_eq_of_isConj' hax).symm.trans ha
  rw [htop] at hle
  exact top_le_iff.1 hle

theorem exists_stronglyEmbedded_of_closed (hs : IsSimpleGroup G) {H : Subgroup G} (hH : H ≠ ⊤)
    {z : G} (hz : orderOf z = 2) (hzH : z ∈ H)
    (hclosed : ∀ t ∈ H, orderOf t = 2 → centralizer ({t} : Set G) ≤ H) :
    ∃ M : Subgroup G, DisconnectedInvolutionGraph.Helpers.IsStronglyEmbedded M := by
  classical
  apply disconnected_exists_stronglyEmbedded
  obtain ⟨u, hu, huH⟩ : ∃ u : G, orderOf u = 2 ∧ u ∉ H := by
    by_contra hno
    push Not at hno
    apply hH
    have h1 : Subgroup.closure {t : G | orderOf t = 2} ≤ H :=
      (Subgroup.closure_le _).2 (fun t ht => hno t ht)
    rw [closure_involutions_eq_top hs hz] at h1
    exact top_le_iff.1 h1
  intro hpre
  have hreach := hpre ⟨z, hz⟩ ⟨u, hu⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ v : Involution G,
      Relation.ReflTransGen (Open.disconnectedInvolutionCommutingGraph G).Adj ⟨z, hz⟩ v → (v : G) ∈ H := by
    intro v hv
    induction hv with
    | refl => exact hzH
    | @tail b c _ hadj ih =>
      obtain ⟨_, hcomm⟩ := (involutionGraph_adj_iff _ _).1 hadj
      exact hclosed _ ih b.property (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  exact huH (key _ hreach)

end Strong

end CFSG.GH74.GLS.Stage2.Local.P34
