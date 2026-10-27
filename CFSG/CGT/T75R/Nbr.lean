module

public import CFSG.CGT.Timmesfeld75.Sec3Eight
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB1

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Nbr (T L S V : Subgroup G) : Prop where
  sec3 : Sec3 T V
  conj : ∃ v : G, V = conjSubgroup v T
  hL : normIn T V = L
  hS : normIn V T ≤ S

variable {T L S V : Subgroup G} {x : G}

theorem Nbr.conj_x (hV : Nbr T L S V) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxS : x ∈ S) :
    Nbr T L S (conjSubgroup x V) where
  sec3 := hV.sec3.conj_of_mem_normalizer hxT
  conj := by
    obtain ⟨v, hv⟩ := hV.conj
    exact ⟨x * v, by rw [hv, conjSubgroup_conjSubgroup]⟩
  hL := by
    rw [normIn_conj_left_of_mem_normalizer hxT, hV.hL]
    exact mem_normalizer_iff_conjSubgroup_eq.1 hxL
  hS := by
    rw [normIn_conj_right_of_mem_normalizer hxT]
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy
    exact S.mul_mem (S.mul_mem hxS (hV.hS he)) (S.inv_mem hxS)

theorem Nbr.comm_conj_x [IsSimpleGroup G] (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hSz : Section3SzInput) (hnab : ∃ a b : G, a * b ≠ b * a) (hV : Nbr T L S V)
    (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (T : Set G))
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hxS : x ∈ S) :
    ∀ y ∈ normIn V T, ∀ z ∈ normIn (conjSubgroup x V) T, y * z = z * y := by
  have hSL' : S ≤ Subgroup.normalizer (normIn T V : Set G) := by
    rw [hV.hL]; exact hSL
  have hel := section3Eight h214 hInv hSz hnab hV.sec3 hS2 hSN hSL' hV.hS
  intro y hy z hz
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := hSN hxS
  rw [normIn_conj_right_of_mem_normalizer hxT] at hz
  refine elemAbelian_mul_comm hel ?_ ?_
  · refine Subgroup.mem_iSup_of_mem (⟨1, S.one_mem⟩ : S) ?_
    show y ∈ conjSubgroup (1 : G) (normIn V T)
    rw [conjSubgroup_one]
    exact hy
  · exact Subgroup.mem_iSup_of_mem (⟨x, hxS⟩ : S) hz

end CFSG.CGT.T75R
