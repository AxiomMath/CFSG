module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

theorem commutatorElement_mem_gammaE_perm {n : ℕ} {E : Subgroup (Perm (Fin n))}
    {e c d : Perm (Fin n)} (he : e ∈ E) (he1 : e ≠ 1) (hc : sign c = 1) (hd : sign d = 1)
    (hce : c * e = e * c) (hde : d * e = e * d) :
    ⁅c, d⁆ ∈ gammaE (alternatingGroup (Fin n)) E := by
  have hle : centDer (alternatingGroup (Fin n)) e ≤ gammaE (alternatingGroup (Fin n)) E :=
    le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)
  exact hle (commutator_mem_commutator
    ⟨mem_alternatingGroup.2 hc, mem_centralizer_singleton_iff.2 hce⟩
    ⟨mem_alternatingGroup.2 hd, mem_centralizer_singleton_iff.2 hde⟩)

theorem commutatorElement_mem_nE {W : Type*} [Group W] {X E : Subgroup W} {x h : W} (hx : x ∈ E)
    (hh : h ∈ gammaE X E) : ⁅x, h⁆ ∈ nE X E :=
  commutator_mem_commutator hx hh

theorem closure_range_carmichaelPerm {n : ℕ} (hn : 3 ≤ n) :
    closure (Set.range (carmichaelPerm (n := n))) = alternatingGroup (Fin n) := by
  have h := congrArg (Subgroup.map (alternatingGroup (Fin n)).subtype)
    (closure_range_carmichaelCycle hn)
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

section S1

@[expose] def s1a : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def s1b : Perm (Fin 6) := swap 2 4 * swap 3 5

theorem s1a_mem : s1a ∈ closure ({s1a, s1b} : Set (Perm (Fin 6))) :=
  subset_closure (Set.mem_insert _ _)

theorem s1b_mem : s1b ∈ closure ({s1a, s1b} : Set (Perm (Fin 6))) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem s1ab_mem : s1a * s1b ∈ closure ({s1a, s1b} : Set (Perm (Fin 6))) :=
  mul_mem s1a_mem s1b_mem

theorem s1_mem_2 :
    carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s1a, s1b}) := by
  rw [show carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 6) =
      ⁅s1b, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 3 * swap 3 5)⁆⁆ * ⁅s1b, ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 3 * swap 3 2 * swap 1 4 * swap 4 5)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s1b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))
      (commutatorElement_mem_nE s1b_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem s1_mem_3 :
    carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s1a, s1b}) := by
  rw [show carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 6) =
      ⁅s1b, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 2 * swap 1 5)⁆⁆ * ⁅s1b, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 3 * swap 3 1 * swap 1 2 * swap 4 5)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 3 * swap 3 2 * swap 1 4 * swap 4 5)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s1b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))
      (commutatorElement_mem_nE s1b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem s1_mem_4 :
    carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s1a, s1b}) := by
  rw [show carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 6) =
      ⁅s1b, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 2 * swap 1 5)⁆⁆ * ⁅s1b, ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 3 * swap 3 2 * swap 1 4 * swap 4 5)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s1b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))
      (commutatorElement_mem_nE s1b_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem s1_mem_5 :
    carmichaelPerm (⟨5, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s1a, s1b}) := by
  rw [show carmichaelPerm (⟨5, by decide⟩ : CarmichaelIndex 6) =
      ⁅s1b, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 3 * swap 3 5)⁆⁆ * ⁅s1b, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 5 * swap 5 2 * swap 1 4 * swap 4 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 0 5 * swap 5 1 * swap 1 2 * swap 3 4)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s1b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))
      (commutatorElement_mem_nE s1b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s1a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s1ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem alternatingGroup_le_nE_s1 :
    alternatingGroup (Fin 6) ≤ nE (alternatingGroup (Fin 6)) (closure {s1a, s1b}) := by
  refine (closure_range_carmichaelPerm (by norm_num)).symm.le.trans ?_
  rw [closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact s1_mem_2
  · exact s1_mem_3
  · exact s1_mem_4
  · exact s1_mem_5

end S1

section S2

@[expose] def s2a : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def s2b : Perm (Fin 6) := swap 4 5

theorem s2a_mem : s2a ∈ closure ({s2a, s2b} : Set (Perm (Fin 6))) :=
  subset_closure (Set.mem_insert _ _)

theorem s2b_mem : s2b ∈ closure ({s2a, s2b} : Set (Perm (Fin 6))) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem s2ab_mem : s2a * s2b ∈ closure ({s2a, s2b} : Set (Perm (Fin 6))) :=
  mul_mem s2a_mem s2b_mem

theorem s2_mem_2 :
    carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s2a, s2b}) := by
  rw [show carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 6) =
      ⁅s2a, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆⁆ * ⁅s2b, ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 1 3 * swap 3 2)⁆ * ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s2a_mem
        (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))
      (commutatorElement_mem_nE s2b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s2b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem s2_mem_3 :
    carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s2a, s2b}) := by
  rw [show carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 6) =
      ⁅s2a, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆⁆ * ⁅s2b, ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 1 2 * swap 4 5)⁆ * ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s2a_mem
        (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))
      (commutatorElement_mem_nE s2b_mem
        ((mul_mem (commutatorElement_mem_gammaE_perm s2b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem s2_mem_4 :
    carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s2a, s2b}) := by
  rw [show carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 6) =
      ⁅s2a, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 1 3 * swap 3 2)⁆ * ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆⁆ by
    decide +kernel]
  exact commutatorElement_mem_nE s2a_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s2b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))

theorem s2_mem_5 :
    carmichaelPerm (⟨5, by decide⟩ : CarmichaelIndex 6) ∈
      nE (alternatingGroup (Fin 6)) (closure {s2a, s2b}) := by
  rw [show carmichaelPerm (⟨5, by decide⟩ : CarmichaelIndex 6) =
      ⁅s2a, ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3)⁆ * ⁅(swap 2 3 * swap 4 5 : Perm (Fin 6)), (swap 1 2 * swap 4 5)⁆ * ⁅(swap 2 4 * swap 3 5 : Perm (Fin 6)), (swap 0 2 * swap 1 3)⁆⁆ by
    decide +kernel]
  exact commutatorElement_mem_nE s2a_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s2b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_perm s2ab_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))

theorem alternatingGroup_le_nE_s2 :
    alternatingGroup (Fin 6) ≤ nE (alternatingGroup (Fin 6)) (closure {s2a, s2b}) := by
  refine (closure_range_carmichaelPerm (by norm_num)).symm.le.trans ?_
  rw [closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact s2_mem_2
  · exact s2_mem_3
  · exact s2_mem_4
  · exact s2_mem_5

end S2

section S3

@[expose] def s3a : Perm (Fin 5) := swap 1 2

@[expose] def s3b : Perm (Fin 5) := swap 3 4

theorem s3a_mem : s3a ∈ closure ({s3a, s3b} : Set (Perm (Fin 5))) :=
  subset_closure (Set.mem_insert _ _)

theorem s3b_mem : s3b ∈ closure ({s3a, s3b} : Set (Perm (Fin 5))) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem s3_mem_2 :
    carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 5) ∈
      nE (alternatingGroup (Fin 5)) (closure {s3a, s3b}) := by
  rw [show carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 5) =
      ⁅s3a, ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 1 * swap 3 4)⁆⁆ by
    decide +kernel]
  exact commutatorElement_mem_nE s3a_mem
        (commutatorElement_mem_gammaE_perm s3b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))

theorem s3_mem_3 :
    carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 5) ∈
      nE (alternatingGroup (Fin 5)) (closure {s3a, s3b}) := by
  rw [show carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 5) =
      ⁅s3b, ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 3 * swap 3 4)⁆⁆ * ⁅s3b, ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 3 * swap 3 4)⁆ * ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 1 * swap 3 4)⁆ * ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 3 * swap 3 4)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s3b_mem
        (commutatorElement_mem_gammaE_perm s3a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))
      (commutatorElement_mem_nE s3b_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_perm s3a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s3b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_perm s3a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem s3_mem_4 :
    carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 5) ∈
      nE (alternatingGroup (Fin 5)) (closure {s3a, s3b}) := by
  rw [show carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 5) =
      ⁅s3b, ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 4 * swap 4 3)⁆⁆ * ⁅s3b, ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 3 * swap 3 4)⁆ * ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 1 * swap 3 4)⁆ * ⁅(swap 1 2 * swap 3 4 : Perm (Fin 5)), (swap 0 3 * swap 3 4)⁆⁆ by
    decide +kernel]
  exact mul_mem (commutatorElement_mem_nE s3b_mem
        (commutatorElement_mem_gammaE_perm s3a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))
      (commutatorElement_mem_nE s3b_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_perm s3a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_perm s3b_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_perm s3a_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)))))

theorem alternatingGroup_le_nE_s3 :
    alternatingGroup (Fin 5) ≤ nE (alternatingGroup (Fin 5)) (closure {s3a, s3b}) := by
  refine (closure_range_carmichaelPerm (by norm_num)).symm.le.trans ?_
  rw [closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact s3_mem_2
  · exact s3_mem_3
  · exact s3_mem_4

end S3

end CFSG.ComponentClassification.RankTwoAlt
