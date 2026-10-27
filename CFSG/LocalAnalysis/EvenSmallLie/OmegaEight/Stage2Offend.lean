module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Enum
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Search

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def invsOf (keys : Array ℕ) : List ℕ :=
  keys.toList.filter fun k => k != idK && mulK k k == idK

@[expose] def commOf (I : List ℕ) (r : ℕ) : List ℕ :=
  I.filter fun z => z != r && mulK z r == mulK r z

@[expose] def allRoots (B : ℕ) (I base : List ℕ) : Bool :=
  I.all fun r => rootCheck B r (commOf I r) base

theorem pairwise_of_sortedK {A : Array ℕ} (hs : sortedK A = true) : A.toList.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < A.size := by simpa using hi
  have hj' : j < A.size := by simpa using hj
  have h := Enum.lt_of_sortedK hs hij hj'
  simp only [Array.getElem_toList]
  rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi',
    Array.getElem?_eq_getElem hj', Option.getD_some, Option.getD_some] at h

theorem mem_toList_of_lt {A : Array ℕ} {i : ℕ} (hi : i < A.size) : A.getD i 0 ∈ A.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  exact Array.getElem_mem_toList hi

theorem offender_bound {gs : Array (ℕ × ℕ)} {E : Enum} (h : enumOK gs E = true)
    {B : ℕ} {base : List ℕ} {Z : Set Vec12} (hbase : ∀ v < 4096, toVec 12 v ∈ Z → v ∈ base)
    (hchk : allRoots B (invsOf E.keys) base = true) {A : Subgroup GL12} (hA : A ≤ grpOf gs)
    (hsq : ∀ a ∈ A, a * a = 1) (hne : A ≠ ⊥) : Nat.card A * Nat.card ↥(Z ∩ fixV A) ≤ B := by
  obtain ⟨⟨r, hrA⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hsorted := pairwise_of_sortedK (Enum.of_enumOK h).2.1
  have hinv : ∀ z ∈ A, z ≠ 1 → ∃ t ∈ invsOf E.keys, Rep t z := by
    intro z hz hz1
    obtain ⟨i, hi, hrep⟩ := Enum.exists_key h (hA hz)
    refine ⟨E.keys.getD i 0, List.mem_filter.2 ⟨mem_toList_of_lt hi, ?_⟩, hrep⟩
    have hk := Enum.key_lt h hi
    have h1 : E.keys.getD i 0 ≠ idK := fun e => hz1 (hrep.unique (e ▸ rep_one))
    have h2 : mulK (E.keys.getD i 0) (E.keys.getD i 0) = idK :=
      (hrep.mul hrep).key_unique (by rw [hsq z hz]; exact rep_one) (mulK_lt _ _) idK_lt
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    exact ⟨h1, h2⟩
  obtain ⟨R, hRI, hR⟩ := hinv r hrA (by simpa using hr1)
  have hall := hchk
  simp only [allRoots, List.all_eq_true] at hall
  have hRlt : R < 2 ^ 144 := by
    obtain ⟨hR1, -⟩ := List.mem_filter.1 hRI
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hR1
    simp only [Array.getElem_toList, Array.length_toList] at e hi
    rw [← e]
    have := Enum.key_lt h hi
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this
  refine bound_of_rootCheck hsq hR hrA (fun z hz hz1 hzr => ?_) ?_ (fun t ht => ?_) hbase
    (hall R hRI)
  · obtain ⟨t, htI, hrt⟩ := hinv z hz hz1
    refine ⟨t, List.mem_filter.2 ⟨htI, ?_⟩, hrt⟩
    have htlt : t < 2 ^ 144 := by
      obtain ⟨ht1, -⟩ := List.mem_filter.1 htI
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem ht1
      simp only [Array.getElem_toList, Array.length_toList] at e hi
      rw [← e]
      have := Enum.key_lt h hi
      rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this
    have h1 : t ≠ R := fun e => hzr (hrt.unique (e ▸ hR))
    have hcomm := commute_of_sq hsq hz hrA
    have h2 : mulK t R = mulK R t :=
      (hrt.mul hR).key_unique (by rw [hcomm]; exact hR.mul hrt) (mulK_lt _ _) (mulK_lt _ _)
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    exact ⟨h1, h2⟩
  · exact (hsorted.filter _).filter _
  · obtain ⟨ht1, -⟩ := List.mem_filter.1 ht
    obtain ⟨ht2, -⟩ := List.mem_filter.1 ht1
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem ht2
    simp only [Array.getElem_toList, Array.length_toList] at e hi
    rw [← e]
    have := Enum.key_lt h hi
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this

end CFSG.EvenSmallLie.OmegaEight.Stage2
