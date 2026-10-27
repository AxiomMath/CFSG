module

public import CFSG.CGT.L5R.L2SubL
public import CFSG.CGT.M24R.L2Enum
public import Certificates.Certificate21196

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

@[expose] def B8L : Subgroup N8 := Subgroup.closure {bL 0, bL 1, bL 2}

abbrev DL : Subgroup N8 := Subgroup.normalizer (B8L : Set N8)

theorem idT_mem_eightT {P Q R : Table} : idT 16 ∈ eightT P Q R := by
  simp only [eightT]
  exact List.mem_cons_self

theorem P_mem_eightT {P Q R : Table} : P ∈ eightT P Q R := by
  simp only [eightT]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem Q_mem_eightT {P Q R : Table} : Q ∈ eightT P Q R := by
  simp only [eightT]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem R_mem_eightT {P Q R : Table} : R ∈ eightT P Q R := by
  simp only [eightT]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem b8List_size : ∀ X ∈ b8List, X.size = 16 :=
  eightT_size (wTab_size _) (wTab_size _) (wTab_size _)

section B

theorem bCheckL_spec : b8List.Nodup ∧ (∀ X ∈ b8List, compT 16 X X = idT 16) ∧
    (∀ X ∈ b8List, ∀ Y ∈ b8List, compT 16 X Y ∈ b8List) ∧
    (∀ X ∈ b8List.tail, (mkCtx ()).isTt X = false) ∧ (mkCtx ()).isTt gamT = false := by
  have h := Certificates.certificate21196.1
  simp only [bCheckL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
    List.contains_iff_mem, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem forall₂_b8 : List.Forall₂ IsTab b8List (eightE (bL 0) (bL 1) (bL 2)) :=
  forall₂_eight (isTab_betaT 0) (isTab_betaT 1) (isTab_betaT 2)

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem mem_B8L_iff (x : N8) : x ∈ B8L ↔ x ∈ eightE (bL 0) (bL 1) (bL 2) := by
  obtain ⟨-, hsq, hmul, -⟩ := bCheckL_spec
  constructor
  · intro hx
    let S : Subgroup N8 :=
      { carrier := {y | ∃ Y ∈ b8List, IsTab Y y}
        one_mem' := ⟨idT 16, idT_mem_eightT, IsTab.one⟩
        mul_mem' := by
          rintro a b ⟨X, hX, ha⟩ ⟨Y, hY, hb⟩
          exact ⟨_, hmul X hX Y hY, ha.mul hb⟩
        inv_mem' := by
          rintro a ⟨X, hX, ha⟩
          have h1 : a * a = 1 := by
            have := ha.mul ha
            rw [hsq X hX] at this
            exact this.eq_of_eq hcard IsTab.one
          refine ⟨X, hX, ?_⟩
          rw [inv_eq_of_mul_eq_one_right h1]
          exact ha }
    have hle : B8L ≤ S := by
      refine (Subgroup.closure_le S).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨_, P_mem_eightT, isTab_betaT 0⟩
      · exact ⟨_, Q_mem_eightT, isTab_betaT 1⟩
      · exact ⟨_, R_mem_eightT, isTab_betaT 2⟩
    obtain ⟨Y, hY, hYx⟩ := hle hx
    obtain ⟨e, he, hYe⟩ := exists_of_forall₂' forall₂_b8 hY
    rw [hYx.eq_of_eq hcard hYe]
    exact he
  · intro hx
    have h0 : bL 0 ∈ B8L := Subgroup.subset_closure (by simp)
    have h1 : bL 1 ∈ B8L := Subgroup.subset_closure (by simp)
    have h2 : bL 2 ∈ B8L := Subgroup.subset_closure (by simp)
    simp only [eightE, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact B8L.one_mem
    · exact h0
    · exact h1
    · exact B8L.mul_mem h0 h1
    · exact h2
    · exact B8L.mul_mem h0 h2
    · exact B8L.mul_mem h1 h2
    · exact B8L.mul_mem (B8L.mul_mem h0 h1) h2

omit hcard in
theorem eightE_b8_nodup : (eightE (bL 0) (bL 1) (bL 2)).Nodup :=
  nodup_of_forall₂ forall₂_b8 b8List_size bCheckL_spec.1

theorem card_B8L : Nat.card B8L = 8 := by
  classical
  have hset : (B8L : Set N8) = ((eightE (bL 0) (bL 1) (bL 2)).toFinset : Set N8) := by
    ext x
    simp only [SetLike.mem_coe, List.coe_toFinset, Set.mem_ofPred_eq]
    exact mem_B8L_iff hcard x
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup eightE_b8_nodup]
  rfl

theorem isB8_iff {X : Table} {x : N8} (hX : IsTab X x) (hXs : X.size = 16) :
    isB8 X = true ↔ x ∈ B8L := by
  rw [isB8, List.contains_iff_mem, mem_B8L_iff hcard]
  constructor
  · intro h
    obtain ⟨e, he, hXe⟩ := exists_of_forall₂' forall₂_b8 h
    rw [hX.eq_of_eq hcard hXe]
    exact he
  · intro h
    obtain ⟨Y, hY, hYx⟩ := exists_of_forall₂ forall₂_b8 h
    rw [table_eq_of_rep hX hYx hXs (b8List_size Y hY)]
    exact hY

theorem b8_spec : (∀ Y ∈ b8List, ∃ y ∈ B8L, IsTab Y y) ∧ ∀ y ∈ B8L, ∃ Y ∈ b8List, IsTab Y y := by
  refine ⟨fun Y hY => ?_, fun y hy => ?_⟩
  · obtain ⟨e, he, hYe⟩ := exists_of_forall₂' forall₂_b8 hY
    exact ⟨e, (mem_B8L_iff hcard e).2 he, hYe⟩
  · exact exists_of_forall₂ forall₂_b8 ((mem_B8L_iff hcard y).1 hy)

end B

end CFSG.CGT.L5R
