module

public import CFSG.Certificates.SchreierChainOrder

public section

namespace CFSG.Certificates.RawSchreierDatum

variable {n : ℕ}

theorem orbit_mul_next_le_level (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Nat.card (Q.orbitPoints i) * Nat.card (Q.levelSubgroup (i.val + 1)) ≤
      Nat.card (Q.levelSubgroup i.val) := by
  have hcard := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Q.levelSubgroup i.val) (Q.base.get i))
  rw [Nat.card_prod, ← Q.orbitPoints_eq_orbit i] at hcard
  rw [← hcard]
  refine Nat.mul_le_mul_left _ ?_
  have hle := Q.levelSubgroup_succ_le_stabilizer i
  refine Nat.card_le_card_of_injective
    (fun g => ⟨⟨g.1, (hle g.2).1⟩, MulAction.mem_stabilizer_iff.2 ?_⟩) ?_
  · exact MulAction.mem_stabilizer_iff.1 (hle g.2).2
  · intro a b hab
    exact Subtype.ext (congrArg (fun x => x.1.1) hab)

theorem orbit_product_le_level (Q : RawSchreierDatum n) (i : ℕ) (hi : i ≤ Q.baseCount) :
    (((List.finRange Q.baseCount).drop i).map fun j => Nat.card (Q.orbitPoints j)).prod ≤
      Nat.card (Q.levelSubgroup i) := by
  have go : ∀ d i, i + d = Q.baseCount →
      (((List.finRange Q.baseCount).drop i).map fun j => Nat.card (Q.orbitPoints j)).prod ≤
        Nat.card (Q.levelSubgroup i) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hdrop : (List.finRange Q.baseCount).drop i = [] :=
        List.drop_eq_nil_iff.2 (by simp; omega)
      rw [hdrop, List.map_nil, List.prod_nil]
      exact Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    | succ d ih =>
      intro i hi
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      have hlen : i < (List.finRange Q.baseCount).length := by
        simp only [List.length_finRange]
        omega
      have hentry : (List.finRange Q.baseCount)[i] = j := by
        apply Fin.ext
        simp only [List.getElem_finRange, Fin.val_cast]
        rfl
      rw [List.drop_eq_getElem_cons hlen, hentry, List.map_cons, List.prod_cons]
      exact (Nat.mul_le_mul_left _ (ih (i + 1) (by omega))).trans (Q.orbit_mul_next_le_level j)
  exact go (Q.baseCount - i) i (by omega)

theorem strong_get_mem_originalSubgroup_of
    (Q : RawSchreierDatum n)
    (h1 : ∀ j : Fin Q.originalCount,
      Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j)
    (h2 : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
      Q.strong.get j = Q.derivationValue j hj) (j : Fin Q.strongCount) :
    Q.strong.get j ∈ Q.originalSubgroup := by
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount,
      j.val = a → Q.strong.get j ∈ Q.originalSubgroup := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · let l : Fin Q.originalCount := ⟨j.val, hj⟩
        have hcast : Fin.castLE Q.originalCount_le l = j := Fin.ext rfl
        rw [← hcast, h1 l]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList Q.original l)
      · rw [h2 j (Nat.le_of_not_gt hj)]
        apply schreierWordValue_mem_subgroup Q.strong.get
          (Nat.le_of_lt j.isLt) (Q.derivation j (Nat.le_of_not_gt hj)) Q.originalSubgroup
        intro l
        exact ih l.val (by omega) ⟨l.val, l.isLt.trans j.isLt⟩ rfl
  exact all j.val j rfl

theorem levelSubgroup_zero_le_originalSubgroup_of (Q : RawSchreierDatum n)
    (h1 : ∀ j : Fin Q.originalCount,
      Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j)
    (h2 : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
      Q.strong.get j = Q.derivationValue j hj) :
    Q.levelSubgroup 0 ≤ Q.originalSubgroup := by
  rw [levelSubgroup, Q.levelGenerators_zero]
  apply (Subgroup.closure_le _).2
  intro g hg
  obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.strong g).1 hg
  exact Q.strong_get_mem_originalSubgroup_of h1 h2 j

theorem mem_originalSubgroup_of_sift (Q : RawSchreierDatum n)
    (h1 : ∀ j : Fin Q.originalCount,
      Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j)
    (h2 : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
      Q.strong.get j = Q.derivationValue j hj) {g : Equiv.Perm (Fin n)}
    (hs : Q.sift g 0 = true) : g ∈ Q.originalSubgroup :=
  Q.levelSubgroup_zero_le_originalSubgroup_of h1 h2 (Q.sift_mem_levelSubgroup 0 g hs)

theorem orderCertificate_le_card (Q : RawSchreierDatum n)
    (h1 : ∀ j : Fin Q.originalCount,
      Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j)
    (h2 : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
      Q.strong.get j = Q.derivationValue j hj) :
    Q.orderCertificate ≤ Nat.card Q.originalSubgroup := by
  have h := Q.orbit_product_le_level 0 (Nat.zero_le _)
  rw [List.drop_zero] at h
  unfold orderCertificate
  rw [List.map_congr_left (fun i _ => Q.orbitSize_eq_card i)]
  exact h.trans (Subgroup.card_le_of_le (Q.levelSubgroup_zero_le_originalSubgroup_of h1 h2))

end CFSG.Certificates.RawSchreierDatum
