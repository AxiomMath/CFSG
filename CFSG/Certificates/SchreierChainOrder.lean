module

public import CFSG.Certificates.SchreierChainOrderMembership
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.Certificates.RawSchreierDatum

@[expose] def levelStabilizerEquiv {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : Fin Q.baseCount) :
    MulAction.stabilizer (Q.levelSubgroup i.val) (Q.base.get i) ≃*
      Q.levelSubgroup (i.val + 1) where
  toFun g := ⟨g.val.val, by
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ i]
    exact ⟨g.val.property, g.property⟩⟩
  invFun h := ⟨⟨h.val, Q.levelSubgroup_antitone i.val (i.val + 1) (Nat.le_succ _) h.property⟩,
    (Q.levelSubgroup_succ_le_stabilizer i h.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem levelStabilizerEquiv_val {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : Fin Q.baseCount)
    (g : MulAction.stabilizer (Q.levelSubgroup i.val) (Q.base.get i)) :
    (Q.levelStabilizerEquiv hQ i g : Equiv.Perm (Fin n)) = g.val.val := rfl

theorem level_card_eq_orbit_mul_next {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : Fin Q.baseCount) :
    Nat.card (Q.levelSubgroup i.val) =
      Nat.card (Q.orbitPoints i) * Nat.card (Q.levelSubgroup (i.val + 1)) := by
  have hcard := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Q.levelSubgroup i.val) (Q.base.get i))
  rw [Nat.card_prod, ← Q.orbitPoints_eq_orbit i,
    Nat.card_congr (Q.levelStabilizerEquiv hQ i).toEquiv] at hcard
  exact hcard.symm

theorem level_card_eq_orbit_product {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (i : ℕ) (hi : i ≤ Q.baseCount) :
    Nat.card (Q.levelSubgroup i) =
      (((List.finRange Q.baseCount).drop i).map fun j => Nat.card (Q.orbitPoints j)).prod := by
  have go : ∀ d i, i + d = Q.baseCount →
      Nat.card (Q.levelSubgroup i) =
        (((List.finRange Q.baseCount).drop i).map fun j => Nat.card (Q.orbitPoints j)).prod := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hi' : i = Q.baseCount := by omega
      subst i
      have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
        List.drop_eq_nil_iff.2 (by simp)
      simp only [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.card_bot,
        hdrop, List.map_nil, List.prod_nil]
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
      rw [Q.level_card_eq_orbit_mul_next hQ j, ih (i + 1) (by omega)]
  exact go (Q.baseCount - i) i (by omega)

theorem original_card_eq_orbit_product {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) :
    Nat.card Q.originalSubgroup = ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i) := by
  rw [← Q.levelSubgroup_zero_eq_original hQ, Fin.prod_univ_def]
  simpa only [List.drop_zero] using Q.level_card_eq_orbit_product hQ 0 (Nat.zero_le _)

@[expose] def orbitSize {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) : ℕ :=
  (Q.orbitSearch i).keys.length

@[expose] def orderCertificate {n : ℕ} (Q : RawSchreierDatum n) : ℕ :=
  ((List.finRange Q.baseCount).map Q.orbitSize).prod

theorem orbitSize_eq_card {n : ℕ} (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Q.orbitSize i = Nat.card (Q.orbitPoints i) := by
  have hset : Q.orbitPoints i = ((Q.orbitSearch i).keys.toFinset : Set (Fin n)) := by
    ext x
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact SchreierOrbitState.mem_points_iff_mem_keys (Q.orbitSearch i) x
  rw [hset]
  have hcard : Nat.card ((Q.orbitSearch i).keys.toFinset : Set (Fin n)) =
      (Q.orbitSearch i).keys.toFinset.card := by
    exact Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
  rw [hcard, List.toFinset_card_of_nodup (Q.orbitSearch_keys_nodup i)]
  rfl

theorem orderCertificate_eq_card {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) :
    Q.orderCertificate = Nat.card Q.originalSubgroup := by
  rw [Q.original_card_eq_orbit_product hQ, Fin.prod_univ_def]
  unfold orderCertificate
  congr 1
  apply List.map_congr_left
  intro i _
  exact Q.orbitSize_eq_card i

theorem originalSubgroup_empty_base_eq_bot {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (hbase : Q.baseCount = 0) : Q.originalSubgroup = ⊥ := by
  rw [← Q.levelSubgroup_zero_eq_original hQ, ← hbase]
  exact Q.levelSubgroup_terminal_eq_bot hQ

theorem empty_base_order_one {n : ℕ} (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (hbase : Q.baseCount = 0) :
    Nat.card Q.originalSubgroup = 1 ∧ Q.orderCertificate = 1 := by
  constructor
  · rw [Q.originalSubgroup_empty_base_eq_bot hQ hbase, Subgroup.card_bot]
  · have hindices : List.finRange Q.baseCount = [] := by
      rw [hbase]
      rfl
    simp only [orderCertificate, hindices, List.map_nil, List.prod_nil]

theorem schreier_chain_order {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) :
    (∀ (i : ℕ), i ≤ Q.baseCount → Q.levelSubgroup i = Q.originalSubgroup ⊓
      fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList.take i}) ∧
      Q.levelSubgroup Q.baseCount = ⊥ ∧
      Nat.card Q.originalSubgroup = ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i) ∧
      (∀ h : Equiv.Perm (Fin n), Q.sift h 0 = true ↔ h ∈ Q.originalSubgroup) ∧
      (Q.baseCount = 0 → Nat.card Q.originalSubgroup = 1 ∧ Q.orderCertificate = 1) :=
  ⟨Q.levelSubgroup_eq_pointwise_stabilizer hQ, Q.levelSubgroup_terminal_eq_bot hQ,
    Q.original_card_eq_orbit_product hQ, Q.sift_eq_true_iff_mem_original hQ,
    Q.empty_base_order_one hQ⟩

end CFSG.Certificates.RawSchreierDatum
