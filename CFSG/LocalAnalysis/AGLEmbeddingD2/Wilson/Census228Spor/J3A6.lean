module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Presented
public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import CFSG.RankThree.Native.ONTripleA6

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Subgroup Equiv Equiv.Perm CFSG.CosetTable CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.RankThree.Native.ONTriple

def a6a : alternatingGroup (Fin 6) :=
  ⟨swap 2 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

def a6b : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * (swap 1 5 * swap 1 4 * swap 1 3), by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

def a6gen : Fin 2 → alternatingGroup (Fin 6) := ![a6a, a6b]

theorem a6_rels : ∀ w ∈ j3tLiftRels, evalW a6gen w = 1 := by
  decide +kernel

theorem sK1_word :
    ((a6a * a6b * a6b * a6a * a6b * a6a * a6b⁻¹ * a6a * a6b⁻¹ : alternatingGroup (Fin 6)) :
      Perm (Fin 6)) = sK1 := by
  decide +kernel

theorem sK2_word :
    ((a6b⁻¹ * a6a * a6b⁻¹ * a6a * a6b * a6a * a6b * a6b * a6a : alternatingGroup (Fin 6)) :
      Perm (Fin 6)) = sK2 := by
  decide +kernel

theorem closure_a6gen : closure (Set.range a6gen) = ⊤ := by
  set H := closure (Set.range a6gen)
  have ha : a6a ∈ H := subset_closure ⟨0, rfl⟩
  have hb : a6b ∈ H := subset_closure ⟨1, rfl⟩
  have hbi : a6b⁻¹ ∈ H := H.inv_mem hb
  have h1 : (a6a * a6b * a6b * a6a * a6b * a6a * a6b⁻¹ * a6a * a6b⁻¹ :
      alternatingGroup (Fin 6)) ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem ha hb) hb) ha) hb) ha) hbi) ha) hbi
  have h2 : (a6b⁻¹ * a6a * a6b⁻¹ * a6a * a6b * a6a * a6b * a6b * a6a :
      alternatingGroup (Fin 6)) ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem hbi ha) hbi) ha) hb) ha) hb) hb) ha
  have hle : closure {g | g ∈ [sK1, sK2]} ≤ H.map (alternatingGroup (Fin 6)).subtype := by
    rw [closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    rcases hg with rfl | rfl
    · exact ⟨_, h1, sK1_word⟩
    · exact ⟨_, h2, sK2_word⟩
  rw [closure_sK_eq_alt] at hle
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

section D


theorem j3tD_liftRels : ∀ w ∈ j3tLiftRels, evalW j3tD w = 1 := by
  have h5a : evalW j3tD (wordPow j3tAB 5) = 1 := j3tD_rels _ (by simp [j3tA6Rels])
  have h5b : evalW j3tD (wordPow j3tABB 5) = 1 := j3tD_rels _ (by simp [j3tA6Rels])
  intro w hw
  simp only [j3tLiftRels, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact j3tD_rels _ (by simp [j3tA6Rels])
  · exact j3tD_rels _ (by simp [j3tA6Rels])
  · rw [evalW_wordPow, show 15 = 5 * 3 by norm_num, pow_mul, ← evalW_wordPow, h5a, one_pow]
  · rw [evalW_wordPow, show 15 = 5 * 3 by norm_num, pow_mul, ← evalW_wordPow, h5b, one_pow]
  · rw [evalW_commW, h5a, commutatorElement_one_left]
  · rw [evalW_commW, h5a, commutatorElement_one_left]
  · rw [evalW_commW, h5b, commutatorElement_one_left]
  · rw [evalW_commW, h5b, commutatorElement_one_left]
  · rw [evalW_commW, commutatorElement_eq_one_iff_mul_comm]
    exact j3t_det.2.2

theorem nonempty_mulEquiv_D_alt6 :
    Nonempty (closure (Set.range j3tD) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hfin, hcard⟩ := card_le_of_cyclicCheckC j3tLiftRels [2] (by norm_num) j3t_lift_check
  have hD := j3t_derived.2
  have hA : Nat.card (closure (Set.range a6gen)) = 360 := by
    rw [closure_a6gen]
    have := card_alt_six
    rw [← this]
    exact Nat.card_congr (Subgroup.topEquiv (G := alternatingGroup (Fin 6))).toEquiv
  obtain ⟨e⟩ := nonempty_mulEquiv_of_presented j3tD a6gen j3tLiftRels j3tD_liftRels a6_rels hfin
    360 (by omega) hD.ge hA.ge
  exact ⟨e.trans ((MulEquiv.subgroupCongr closure_a6gen).trans Subgroup.topEquiv)⟩

end D

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
