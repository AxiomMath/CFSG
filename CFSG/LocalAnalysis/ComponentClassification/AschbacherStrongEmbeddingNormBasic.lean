module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingNormSplit

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {X : Type*} [Group X] [Finite X]

theorem twoRank_le_one_of_mulEquiv {Y : Type*} [Group Y] [Finite Y] (e : X ≃* Y)
    (h : twoRank Y ≤ 1) : twoRank X ≤ 1 := by
  apply twoRank_le_one_of_odd_kernel e.toMonoidHom _ h
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [hker, Subgroup.card_bot]
  exact odd_one

theorem twoRank_le_one_of_hull_top {x : X} (hhull : involutionPointHull x = ⊤)
    (h : twoRank (involutionPointHull x) ≤ 1) : twoRank X ≤ 1 :=
  twoRank_le_one_of_mulEquiv
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hhull.symm)) h

omit [Finite X] in
theorem mem_of_orderOf_two_of_odd_index {N : Subgroup X} [N.Normal] (hN : Odd N.index)
    {g : X} (hg : orderOf g = 2) : g ∈ N := by
  have hdvd : orderOf (QuotientGroup.mk g : X ⧸ N) ∣ 2 :=
    hg ▸ orderOf_map_dvd (QuotientGroup.mk' N) g
  have hdvd' : orderOf (QuotientGroup.mk g : X ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
    exact h
  · rw [h] at hdvd'
    exact absurd (hN.of_dvd_nat hdvd') (by decide)

omit [Finite X] in
theorem eq_top_of_odd_index_of_hull_top {x : X} (hx : orderOf x = 2)
    (hhull : involutionPointHull x = ⊤) (N : Subgroup X) (hN : N.Normal) (hodd : Odd N.index) :
    N = ⊤ := by
  have : N.Normal := hN
  apply eq_top_iff.mpr
  rw [← hhull]
  refine (Subgroup.closure_le _).mpr fun t ht => ?_
  exact mem_of_orderOf_two_of_odd_index hodd (class_orderOf hx ht)

theorem normSplit_of_stronglyEmbedded {X : Type} [Group X] [Finite X] {M : Subgroup X} {x : X}
    (hx : orderOf x = 2) (hcentral : InvolutionPointCentralSylow x)
    (hhull : involutionPointHull x = ⊤) (hO : CFSG.oddCore X = ⊥)
    (hse : fusionStronglyEmbedded M) : NormSplit X M x := by
  by_cases hiso : ∀ t ∈ involutionPointClass x, Commute x t → t = x
  · exact Or.inl (twoRank_le_one_of_hull_top hhull
      (twoRank_hull_le_one_of_isolated hx hcentral hiso))
  obtain ⟨t, ht, hxt, hne⟩ : ∃ t ∈ involutionPointClass x, Commute x t ∧ t ≠ x := by
    by_contra h
    apply hiso
    intro t ht hxt
    by_contra hne
    exact h ⟨t, ht, hxt, hne⟩
  have hB := fusionIsBenderGroup_of_stronglyEmbedded hO
    (eq_top_of_odd_index_of_hull_top hx hhull) hse hx (class_orderOf hx ht) hxt hne.symm
  have hcomm : commutator X = ⊤ :=
    commutator_eq_top_of_bender hB (exists_noncommuting_of_stronglyEmbedded hse)
  refine Or.inr ⟨1, one_pow 2, Subgroup.one_mem _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_one_eq_bot, bot_inf_eq]
  · rw [Subgroup.zpowers_one_eq_bot, bot_sup_eq, hcomm]
  · let e : X ≃* commutator X :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcomm.symm)
    have he : ∀ y : X, ((e y : commutator X) : X) = y := fun _ => rfl
    have hmap : M.map e.toMonoidHom = M.subgroupOf (commutator X) := by
      ext w
      constructor
      · rintro ⟨m, hm, rfl⟩
        change ((e m : commutator X) : X) ∈ M
        rw [he]
        exact hm
      · intro hw
        exact ⟨w, hw, Subtype.ext (he w)⟩
    have h := hse.map_mulEquiv e
    rwa [hmap] at h
  · intro s _
    rw [hcomm]
    exact Subgroup.mem_top _

end CFSG.ComponentClassification.AschbacherStrongEmbedding
