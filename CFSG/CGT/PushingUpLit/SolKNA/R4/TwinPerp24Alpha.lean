module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23Odd
public import CFSG.ClassicalInvolution.Asc77.AscT7AFrame
public import CFSG.ClassicalInvolution.Asc77.WP3L54Prelim

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open CFSG CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Alpha

variable {Y : Type} [Group Y] [Finite Y]

theorem commutator_le_alphaOf {A : Subgroup Y} {a : Y} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ⁅oddCoreIn (Subgroup.centralizer ({a} : Set Y)), A⁆ ≤ alphaOf A := by
  refine le_sup_of_le_left ?_
  exact le_iSup₂_of_le a ha
    (le_iSup (fun _ : a ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({a} : Set Y)), A⁆) ha1)

theorem mem_normalizer_alphaOf {A : Subgroup Y} {n : Y} (hn : n ∈ Subgroup.normalizer (A : Set Y)) :
    n ∈ Subgroup.normalizer (alphaOf A : Set Y) := by
  rw [mem_normalizer_iff_conjSub_eq, ← alphaOf_conjSub, mem_normalizer_iff_conjSub_eq.mp hn]

theorem le_normalizer_alphaOf {A : Subgroup Y} (hA2 : IsPGroup 2 A) {a : Y} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hAC : A ≤ Subgroup.centralizer ({a} : Set Y))
    (hfac : ∀ c ∈ Subgroup.centralizer ({a} : Set Y),
      ∃ o ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)),
        ∃ n ∈ Subgroup.centralizer ({a} : Set Y),
          n ∈ Subgroup.normalizer (A : Set Y) ∧ c = o * n) :
    Subgroup.centralizer ({a} : Set Y) ≤ Subgroup.normalizer (alphaOf A : Set Y) := by
  intro c hc
  obtain ⟨o, ho, n, -, hn, rfl⟩ := hfac c hc
  refine Subgroup.mul_mem _ ?_ (mem_normalizer_alphaOf hn)
  have hAN : A ≤ Subgroup.normalizer (oddCoreIn (Subgroup.centralizer ({a} : Set Y)) : Set Y) :=
    hAC.trans (normalizer_oddCoreIn _)
  obtain ⟨p, hp, q, hq, rfl⟩ := Lemma54Proof.exists_mul_of_mem hA2 hAN (odd_card_oddCoreIn _) ho
  refine Subgroup.mul_mem _ ?_ ?_
  · exact (alphaOf A).le_normalizer (commutator_le_alphaOf ha ha1 hp)
  · refine mem_normalizer_alphaOf ?_
    refine Lemma54Proof.mem_normalizer_of_forall_commute fun x hx => ?_
    exact (Subgroup.mem_centralizer_iff.mp hq.2 x hx).symm

theorem le_normalizer_of_alphaOf_eq_bot {A : Subgroup Y} {a : Y} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hα : alphaOf A = ⊥)
    (hfac : ∀ c ∈ Subgroup.centralizer ({a} : Set Y),
      ∃ o ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)),
        ∃ n ∈ Subgroup.centralizer ({a} : Set Y),
          n ∈ Subgroup.normalizer (A : Set Y) ∧ c = o * n) :
    Subgroup.centralizer ({a} : Set Y) ≤ Subgroup.normalizer (A : Set Y) := by
  intro c hc
  obtain ⟨o, ho, n, -, hn, rfl⟩ := hfac c hc
  refine Subgroup.mul_mem _ ?_ hn
  refine Lemma54Proof.mem_normalizer_of_forall_commute fun x hx => ?_
  exact Perp23.commute_of_alpha hα ha ha1 ho hx

end Alpha

section Pair

variable {Y : Type} [Group Y]

theorem closure_pair_comm_gen {a b : Y} (ha : a * a = 1) (hab : a * b = b * a) {x : Y}
    (hx : x ∈ Subgroup.closure ({a, b} : Set Y)) : x * a = a * x ∧ x * b = b * x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨rfl, hab⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨hab.symm, rfl⟩
  | one => simp
  | mul x y _ _ h1 h2 =>
    refine ⟨?_, ?_⟩
    · rw [mul_assoc, h2.1, ← mul_assoc, h1.1, mul_assoc]
    · rw [mul_assoc, h2.2, ← mul_assoc, h1.2, mul_assoc]
  | inv x _ h =>
    exact ⟨Commute.inv_left h.1, Commute.inv_left h.2⟩

theorem closure_pair_comm {a b : Y} (ha : a * a = 1) (hab : a * b = b * a) {x y : Y}
    (hx : x ∈ Subgroup.closure ({a, b} : Set Y)) (hy : y ∈ Subgroup.closure ({a, b} : Set Y)) :
    x * y = y * x := by
  have hxg := closure_pair_comm_gen ha hab hx
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact hxg.1
    · rw [Set.mem_singleton_iff.mp hy]
      exact hxg.2
  | one => simp
  | mul y z _ _ h1 h2 => rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  | inv y _ h => exact Commute.inv_right h

theorem closure_pair_sq {a b : Y} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set Y), x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff.mp hx]
      exact hb
  | one => simp
  | mul x y hx hy h1 h2 =>
    have hc := closure_pair_comm ha hab hy hx
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  | inv x _ h =>
    rw [inv_mul_eq_iff_eq_mul, mul_one]
    exact (eq_inv_of_mul_eq_one_left h).symm

theorem closure_pair_mul {a b : Y} (ha : a * a = 1) :
    Subgroup.closure ({a, a * b} : Set Y) = Subgroup.closure ({a, b} : Set Y) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff.mp hx]
      have h1 : a * (a * b) ∈ Subgroup.closure ({a, a * b} : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      rwa [← mul_assoc, ha, one_mul] at h1

theorem isPGroup_two_of_sq {E : Subgroup Y} (h : ∀ x ∈ E, x * x = 1) : IsPGroup 2 E := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have := h x x.2
  simpa [pow_two] using this

end Pair

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
