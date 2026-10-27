module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartSeven
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Bridge

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AS76b (oddCoreIn oUpperTwoPrime NormalIn)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure conjugateSubgroup
  subgroup_le_relative_weak_closure)

variable {G : Type} [Group G] [Finite G]

theorem normalIn_or_exists_or_isCyclic (h3 : AschbacherTheorem3.Theorem3Statement)
    {K J T R : Subgroup G} (hK : TightlyEmbedded K) (hJ : TightlyEmbedded J)
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    NormalIn (weakClosure K T (R ⊔ T) ⊔ oddCoreIn K) (K ⊔ T) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (K ⊔ T) →*
          Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Function.Surjective φ ∧ φ.ker = (oddCoreIn K).subgroupOf (oUpperTwoPrime (K ⊔ T))) ∨
      IsCyclic T := by
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hSN : R ⊔ T ≤ normalizer (K : Set G) := sup_le (hR.le.trans hKN) hTK
  have hWle : weakClosure K T (R ⊔ T) ≤ K ⊔ T :=
    (weakClosure_le K T (R ⊔ T)).trans (sup_le_sup_right hR.le T)
  have hbarW := bar_weakClosure hSN hTK hT2
  rcases thm3Conclusion h3 hK hJ hKJ hfac hT hT1 hR hTR with
      ⟨hcyc, -, -⟩ | h2 | h3alt | ⟨x, -, -, -, -, -, hNW, -, -⟩ | ⟨hN5, -⟩
  ·
    right
    right
    obtain ⟨eT⟩ := nonempty_mulEquiv_bar hTK hT2
    exact isCyclic_of_surjective eT.symm.toMonoidHom eT.symm.surjective
  ·
    left
    refine normalIn_of_le_normalizer hTK hWle ?_
    have hWT : relativeWeakClosure (bar K K) (bar K T) (bar K (R ⊔ T)) = bar K T := by
      refine le_antisymm (iSup_le fun c => iSup_le fun _ => ?_)
        (subgroup_le_relative_weak_closure _ _ _ (bar_mono K le_sup_right))
      have hc := h2 (mem_sup_left c.2)
      rw [mem_normalizer_iff_map_conj_eq] at hc
      exact hc.le
    rw [hbarW, hWT]
    exact h2
  ·
    right
    left
    exact Asc75T4.exists_surjective_of_thm3Alt3 hTK h3alt
  ·
    left
    refine normalIn_of_le_normalizer hTK hWle ?_
    rw [hbarW]
    exact hNW
  ·
    left
    refine normalIn_of_le_normalizer hTK hWle ?_
    rw [hbarW]
    exact hN5

end CFSG.ComponentClassification.Asc76.Lemma22
