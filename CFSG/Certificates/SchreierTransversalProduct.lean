module

public import CFSG.Certificates.SchreierChainOrder

public section

namespace CFSG.Certificates.RawSchreierDatum

variable {n : ℕ} (Q : RawSchreierDatum n)

@[expose] def orbitTransversal (i : Fin Q.baseCount) (x : Q.orbitPoints i) :
    Equiv.Perm (Fin n) :=
  (Q.transversal? i x).getD 1

theorem orbitTransversal_spec (i : Fin Q.baseCount) (x : Q.orbitPoints i) :
    Q.transversal? i x = some (Q.orbitTransversal i x) ∧
      Q.orbitTransversal i x ∈ Q.levelSubgroup i.val ∧
      Q.orbitTransversal i x (Q.base.get i) = x :=
  Q.transversal_getD_spec i x x.2

@[expose] def transversalSuffix (x : ∀ i : Fin Q.baseCount, Q.orbitPoints i) (j : ℕ) :
    Equiv.Perm (Fin n) :=
  (((List.finRange Q.baseCount).drop j).map fun i => Q.orbitTransversal i (x i)).prod

theorem transversalSuffix_zero (x : ∀ i : Fin Q.baseCount, Q.orbitPoints i) :
    Q.transversalSuffix x 0 = (List.ofFn fun i => Q.orbitTransversal i (x i)).prod := by
  rw [transversalSuffix, List.drop_zero, List.ofFn_eq_map]

theorem transversalSuffix_of_lt (x : ∀ i : Fin Q.baseCount, Q.orbitPoints i) {j : ℕ}
    (hj : j < Q.baseCount) :
    Q.transversalSuffix x j =
      Q.orbitTransversal ⟨j, hj⟩ (x ⟨j, hj⟩) * Q.transversalSuffix x (j + 1) := by
  rw [transversalSuffix, transversalSuffix,
    List.drop_eq_getElem_cons (by rw [List.length_finRange]; exact hj)]
  simp

theorem transversalSuffix_of_le (x : ∀ i : Fin Q.baseCount, Q.orbitPoints i) {j : ℕ}
    (hj : Q.baseCount ≤ j) : Q.transversalSuffix x j = 1 := by
  rw [transversalSuffix, List.drop_eq_nil_of_le (by rw [List.length_finRange]; exact hj),
    List.map_nil, List.prod_nil]

theorem transversalSuffix_mem (x : ∀ i : Fin Q.baseCount, Q.orbitPoints i) (j : ℕ) :
    Q.transversalSuffix x j ∈ Q.levelSubgroup j := by
  obtain ⟨d, hd⟩ : ∃ d, Q.baseCount - j = d := ⟨_, rfl⟩
  induction d generalizing j with
  | zero =>
    rw [Q.transversalSuffix_of_le x (by omega)]
    exact one_mem _
  | succ d ih =>
    have hj : j < Q.baseCount := by omega
    rw [Q.transversalSuffix_of_lt x hj]
    exact mul_mem (Q.orbitTransversal_spec ⟨j, hj⟩ (x ⟨j, hj⟩)).2.1
      (Q.levelSubgroup_antitone j (j + 1) (Nat.le_succ j) (ih (j + 1) (by omega)))

theorem transversalSuffix_apply_base (x : ∀ i : Fin Q.baseCount, Q.orbitPoints i) {j : ℕ}
    (hj : j < Q.baseCount) : Q.transversalSuffix x j (Q.base.get ⟨j, hj⟩) = x ⟨j, hj⟩ := by
  rw [Q.transversalSuffix_of_lt x hj, Equiv.Perm.mul_apply,
    Q.levelSubgroup_fixes_base_index (j + 1) _ (Q.transversalSuffix_mem x (j + 1)) ⟨j, hj⟩
      (Nat.lt_succ_self j)]
  exact (Q.orbitTransversal_spec ⟨j, hj⟩ (x ⟨j, hj⟩)).2.2

theorem eq_of_transversalSuffix_eq (x y : ∀ i : Fin Q.baseCount, Q.orbitPoints i) (j : ℕ)
    (h : Q.transversalSuffix x j = Q.transversalSuffix y j) :
    ∀ i : Fin Q.baseCount, j ≤ i.val → x i = y i := by
  obtain ⟨d, hd⟩ : ∃ d, Q.baseCount - j = d := ⟨_, rfl⟩
  induction d generalizing j with
  | zero =>
    intro i hi
    exact absurd i.2 (by omega)
  | succ d ih =>
    have hj : j < Q.baseCount := by omega
    have hxy : x ⟨j, hj⟩ = y ⟨j, hj⟩ := by
      apply Subtype.ext
      rw [← Q.transversalSuffix_apply_base x hj, ← Q.transversalSuffix_apply_base y hj, h]
    have h' : Q.transversalSuffix x (j + 1) = Q.transversalSuffix y (j + 1) := by
      rw [Q.transversalSuffix_of_lt x hj, Q.transversalSuffix_of_lt y hj, hxy] at h
      exact mul_left_cancel h
    intro i hi
    rcases Nat.eq_or_lt_of_le hi with hij | hij
    · have : i = ⟨j, hj⟩ := Fin.ext hij.symm
      rw [this, hxy]
    · exact ih (j + 1) h' (by omega) i hij

theorem schreier_transversal_product_bijection (hQ : ValidSchreier Q) :
    (∀ (i : Fin Q.baseCount) (x : Q.orbitPoints i),
      Q.transversal? i x = some (Q.orbitTransversal i x) ∧
        Q.orbitTransversal i x (Q.base.get i) = x) ∧
    ∃ Φ : (∀ i : Fin Q.baseCount, Q.orbitPoints i) → Q.originalSubgroup,
      (∀ x, (Φ x : Equiv.Perm (Fin n)) =
        (List.ofFn fun i => Q.orbitTransversal i (x i)).prod) ∧
      Function.Bijective Φ ∧
      (Q.baseCount = 0 → (∀ x y : (∀ i : Fin Q.baseCount, Q.orbitPoints i), x = y) ∧
        ∀ x, Φ x = 1) := by
  refine ⟨fun i x => ⟨(Q.orbitTransversal_spec i x).1, (Q.orbitTransversal_spec i x).2.2⟩, ?_⟩
  have hmem : ∀ x : (∀ i : Fin Q.baseCount, Q.orbitPoints i),
      Q.transversalSuffix x 0 ∈ Q.originalSubgroup := fun x => by
    rw [← Q.levelSubgroup_zero_eq_original hQ]
    exact Q.transversalSuffix_mem x 0
  let Φ : (∀ i : Fin Q.baseCount, Q.orbitPoints i) → Q.originalSubgroup :=
    fun x => ⟨Q.transversalSuffix x 0, hmem x⟩
  have hinj : Function.Injective Φ := by
    intro x y h
    funext i
    exact Q.eq_of_transversalSuffix_eq x y 0 (congrArg Subtype.val h) i (Nat.zero_le _)
  have : Finite (∀ i : Fin Q.baseCount, Q.orbitPoints i) := Pi.finite
  have hcard : Nat.card Q.originalSubgroup ≤
      Nat.card (∀ i : Fin Q.baseCount, Q.orbitPoints i) := by
    rw [Q.original_card_eq_orbit_product hQ, Nat.card_pi]
  refine ⟨Φ, fun x => Q.transversalSuffix_zero x, hinj.bijective_of_nat_card_le hcard,
    fun hk => ⟨fun x y => funext fun i => absurd i.2 (by omega), fun x => ?_⟩⟩
  exact Subtype.ext (Q.transversalSuffix_of_le x (by omega))

end CFSG.Certificates.RawSchreierDatum
