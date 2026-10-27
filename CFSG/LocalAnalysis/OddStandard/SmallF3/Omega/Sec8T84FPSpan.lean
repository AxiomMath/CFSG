module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def sec8t84Prod4 {M : Type*} [Monoid M] (a b c d : M) : List M :=
  let s1 := [1, a]
  let s2 := s1 ++ s1.map (b * ·)
  let s3 := s2 ++ s2.map (c * ·)
  s3 ++ s3.map (d * ·)

private lemma sec8t84Prod4_mem_closure {M : Type*} [Group M] (S : Subgroup M) {a b c d : M}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    ∀ x ∈ sec8t84Prod4 a b c d, x ∈ S := by
  have hstep : ∀ (p : M), p ∈ S → ∀ l : List M, (∀ x ∈ l, x ∈ S) →
      ∀ x ∈ l ++ l.map (p * ·), x ∈ S := by
    intro p hp l hl x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hl x hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact S.mul_mem hp (hl y hy)
  have hl1 : ∀ x ∈ ([1, a] : List M), x ∈ S := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact S.one_mem
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact absurd hx (by simp)
  have hl2 := hstep b hb _ hl1
  have hl3 := hstep c hc _ hl2
  have hl4 := hstep d hd _ hl3
  simpa only [sec8t84Prod4] using hl4

theorem sec8t84_elemAb_of_prod4 {M : Type} [Group M] [Finite M] {a b c d : M}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a) (hbc : b * c = c * b)
    (hbd : b * d = d * b) (hcd : c * d = d * c) (hnd : (sec8t84Prod4 a b c d).Nodup) :
    ∃ A : Subgroup M, A ≤ centralizer ({a} : Set M) ∧ CFSG.Open.IsElemAbelian 2 A ∧
      16 ≤ Nat.card A := by
  classical
  let S : Set M := {a, b, c, d}
  let A : Subgroup M := Subgroup.closure S
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exact hab | exact hab.symm | exact hac | exact hac.symm
      | exact had | exact had.symm | exact hbc | exact hbc.symm
      | exact hbd | exact hbd.symm | exact hcd | exact hcd.symm
  haveI hAcomm : IsMulCommutative A :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcommS x hx y hy)
  have hA2 : ∀ x ∈ A, x ^ 2 = 1 := by
    intro x hx
    change x ∈ Subgroup.closure S at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · simpa [pow_two] using ha
      · simpa [pow_two] using hb
      · simpa [pow_two] using hc
      · simpa [pow_two] using hd
    | one => simp
    | mul y z hy hz ihy ihz =>
      have hc' : y * z = z * y :=
        congrArg Subtype.val (hAcomm.is_comm.comm (⟨y, hy⟩ : A) (⟨z, hz⟩ : A))
      rw [Commute.mul_pow (show Commute y z from hc'), ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have haS : a ∈ S := by
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hbS : b ∈ S := by
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hcS : c ∈ S := by
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hdS : d ∈ S := by
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have haA : a ∈ A := Subgroup.subset_closure haS
  have hcent : A ≤ centralizer ({a} : Set M) :=
    (Subgroup.le_centralizer A).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  haveI : Fintype M := Fintype.ofFinite M
  have hlen : (sec8t84Prod4 a b c d).length = 16 := by simp [sec8t84Prod4]
  have hmem : ∀ x ∈ sec8t84Prod4 a b c d, x ∈ A :=
    sec8t84Prod4_mem_closure A (Subgroup.subset_closure haS) (Subgroup.subset_closure hbS)
      (Subgroup.subset_closure hcS) (Subgroup.subset_closure hdS)
  have hcardList : Nat.card {x // x ∈ sec8t84Prod4 a b c d} = 16 := by
    rw [← Nat.card_congr (hnd.getEquiv (sec8t84Prod4 a b c d)), Nat.card_fin, hlen]
  have hinj : Function.Injective
      (fun x : {x // x ∈ sec8t84Prod4 a b c d} => (⟨x.1, hmem x.1 x.2⟩ : A)) := by
    intro x y h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcardList] at hle
  exact ⟨A, hcent, ⟨hAcomm, hA2⟩, hle⟩

end CFSG.OddStandard.SmallF3.Omega
