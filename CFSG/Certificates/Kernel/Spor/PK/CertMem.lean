module

public import CFSG.Certificates.Kernel.Spor.PK.CertBridge

public section

namespace CFSG.KS.PK

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : Nat}

theorem certificate_strong_mem (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    (j : Fin (certificate hn gens words base hbase).strongCount) :
    (certificate hn gens words base hbase).strong.get j ∈
      (certificate hn gens words base hbase).originalSubgroup := by
  revert j
  set Q := certificate hn gens words base hbase
  intro j
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount, j.val = a →
      Q.strong.get j ∈ Q.originalSubgroup := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · let l : Fin Q.originalCount := ⟨j.val, hj⟩
        have hcast : Fin.castLE Q.originalCount_le l = j := Fin.ext rfl
        rw [← hcast, certificate_initial hn gens words base hbase l]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList Q.original l)
      · rw [certificate_words hn gens words base hbase j (Nat.le_of_not_gt hj)]
        apply schreierWordValue_mem_subgroup Q.strong.get (Nat.le_of_lt j.isLt)
          (Q.derivation j (Nat.le_of_not_gt hj)) Q.originalSubgroup
        intro l
        exact ih l.val (by omega) ⟨l.val, l.isLt.trans j.isLt⟩ rfl
  exact all j.val j rfl

theorem certificate_enumeration_mem (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    ∀ g ∈ enumeration (certificate hn gens words base hbase),
      g ∈ (certificate hn gens words base hbase).originalSubgroup := by
  set Q := certificate hn gens words base hbase
  have hle : Q.levelSubgroup 0 ≤ Q.originalSubgroup := by
    rw [RawSchreierDatum.levelSubgroup, Q.levelGenerators_zero]
    apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.strong g).1 hg
    exact certificate_strong_mem hn gens words base hbase j
  intro g hg
  apply hle
  refine mem_of_mem_products (Q.levelSubgroup 0).toSubmonoid _ ?_ g hg
  intro T hT t ht
  simp only [List.mem_map, List.mem_finRange, true_and] at hT
  obtain ⟨i, rfl⟩ := hT
  exact Q.levelSubgroup_antitone 0 i.val (Nat.zero_le _)
    (mem_levelSubgroup_of_mem_levelTransversals Q i ht)

end CFSG.KS.PK

end
