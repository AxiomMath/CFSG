module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Fischer.Classification.O3

abbrev Pt := ZMod 3 × ZMod 3

@[expose] def IsTauClosed (S : Set Pt) : Prop := ∀ p ∈ S, ∀ q ∈ S, -p - q ∈ S

theorem three_nsmul_pt (x : Pt) : (3 : ℕ) • x = 0 := by
  obtain ⟨a, b⟩ := x
  fin_cases a <;> fin_cases b <;> rfl

theorem neg_two_nsmul (x : Pt) : -(x + x) = x := by
  obtain ⟨a, b⟩ := x
  fin_cases a <;> fin_cases b <;> rfl

theorem exists_addSubgroup_of_equivalence {R : Pt → Pt → Prop} (hR : Equivalence R)
    (htr : ∀ p q t, R p q → R (p + t) (q + t)) (hτ : ∀ p, IsTauClosed {q | R p q}) :
    ∃ K : AddSubgroup Pt, ∀ p q, R p q ↔ q - p ∈ K := by
  have hadd : ∀ a b : Pt, R 0 a → R 0 b → R 0 (a + b) := by
    intro a b ha hb
    have h1 := hτ 0 a ha b hb
    have h2 := hτ 0 _ h1 0 (hR.refl 0)
    simpa [add_comm] using h2
  have hneg : ∀ a : Pt, R 0 a → R 0 (-a) := by
    intro a ha
    have h := hτ 0 0 (hR.refl 0) a ha
    simpa using h
  let K : AddSubgroup Pt :=
    { carrier := {r | R 0 r}
      zero_mem' := hR.refl 0
      add_mem' := fun ha hb => hadd _ _ ha hb
      neg_mem' := fun ha => hneg _ ha }
  refine ⟨K, fun p q => ?_⟩
  show R p q ↔ R 0 (q - p)
  constructor
  · intro h
    have := htr p q (-p) h
    rwa [add_neg_cancel, ← sub_eq_add_neg] at this
  · intro h
    have := htr 0 (q - p) p h
    rwa [zero_add, sub_add_cancel] at this

@[expose] def inCoset (p r x : Pt) : Bool :=
  decide (x = p) || decide (x = p + r) || decide (x = p + r + r)

theorem inCoset_zero_iff {r x : Pt} : inCoset 0 r x = true ↔ (x = 0 ∨ x = r ∨ x = r + r) := by
  simp [inCoset, or_assoc]

@[expose] def lineGen : Fin 4 → Pt
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)

theorem mem_zmultiples_iff {r x : Pt} :
    x ∈ AddSubgroup.zmultiples r ↔ x = 0 ∨ x = r ∨ x = r + r := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have h3 : (3 : ℤ) • r = 0 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, natCast_zsmul, three_nsmul_pt]
    have hn : n • r = (n % 3) • r := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
      rw [add_zsmul, mul_comm, mul_zsmul, h3, zsmul_zero, add_zero]
    rw [hn]
    have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
    have h1 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
    interval_cases (n % 3)
    · left; rw [zero_zsmul]
    · right; left; rw [one_zsmul]
    · right; right; rw [show (2 : ℤ) = 1 + 1 by rfl, add_zsmul, one_zsmul]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, zero_zsmul _⟩
    · exact ⟨1, one_zsmul _⟩
    · exact ⟨2, by rw [show (2 : ℤ) = 1 + 1 by rfl, add_zsmul, one_zsmul]⟩

theorem span_pair_eq (r s x : Pt) (hr : r ≠ 0) (hs : s ≠ 0) (hsr : s ≠ r) (hsrr : s ≠ r + r) :
    ∃ a b : ZMod 3, x = a • r + b • s := by
  revert r s x
  decide

theorem addSubgroup_cases (K : AddSubgroup Pt) :
    K = ⊥ ∨ K = ⊤ ∨ K = AddSubgroup.zmultiples (1, 0) ∨ K = AddSubgroup.zmultiples (0, 1) ∨
      K = AddSubgroup.zmultiples (1, 1) ∨ K = AddSubgroup.zmultiples (1, 2) := by
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  obtain ⟨⟨r, hrK⟩, hr0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).1 hbot
  have hr0 : r ≠ 0 := fun h => hr0 (Subtype.ext h)
  have hle : AddSubgroup.zmultiples r ≤ K := (AddSubgroup.zmultiples_le_of_mem hrK)
  by_cases hK : (K : Set Pt) ⊆ AddSubgroup.zmultiples r
  · have hKeq : K = AddSubgroup.zmultiples r := le_antisymm hK hle
    right; right
    rw [hKeq]
    have key : ∀ r : Pt, r ≠ 0 → ∃ i : Fin 4, ∀ x : Pt,
        (inCoset 0 r x = inCoset 0 (lineGen i) x) := by
      decide +kernel
    obtain ⟨i, hi⟩ := key r hr0
    have hset : AddSubgroup.zmultiples r = AddSubgroup.zmultiples (lineGen i) := by
      ext x
      rw [mem_zmultiples_iff, mem_zmultiples_iff]
      rw [← inCoset_zero_iff, ← inCoset_zero_iff, hi x]
    rw [hset]
    fin_cases i
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · right; left
    obtain ⟨s, hsK, hs⟩ := Set.not_subset.1 hK
    rw [SetLike.mem_coe, mem_zmultiples_iff, not_or, not_or] at hs
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, rfl⟩ := span_pair_eq r s x hr0 hs.1 hs.2.1 hs.2.2
    have hsm : ∀ {y : Pt}, y ∈ K → ∀ c : ZMod 3, c • y ∈ K := fun {y} hy c => by
      have hc : inCoset 0 y (c • y) = true := by
        have key : ∀ c : ZMod 3, ∀ y : Pt, inCoset 0 y (c • y) = true := by decide
        exact key c y
      rcases inCoset_zero_iff.1 hc with h | h | h <;> rw [h]
      · exact zero_mem K
      · exact hy
      · exact add_mem hy hy
    exact add_mem (hsm hrK a) (hsm hsK b)

@[expose] def tauStep (S : Finset Pt) : Finset Pt := S ∪ (S ×ˢ S).image fun x => -x.1 - x.2

theorem tauStep_subset {S : Set Pt} (hS : IsTauClosed S) {T : Finset Pt} (hT : (T : Set Pt) ⊆ S) :
    (tauStep T : Set Pt) ⊆ S := by
  intro x hx
  rw [tauStep, Finset.coe_union, Set.mem_union] at hx
  rcases hx with hx | hx
  · exact hT hx
  · rw [Finset.coe_image] at hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    rw [Finset.coe_product, Set.mem_prod] at hab
    exact hS a (hT hab.1) b (hT hab.2)

theorem tauStep_three_eq_univ (q s : Pt) (hq : q ≠ 0) (hs : s ≠ 0) (hsq : s ≠ q)
    (hsq' : s ≠ -q) : tauStep (tauStep (tauStep {0, q, s})) = Finset.univ := by
  revert q s
  decide +kernel

theorem IsTauClosed.translate {S : Set Pt} (hS : IsTauClosed S) (t : Pt) :
    IsTauClosed {x | x + t ∈ S} := by
  intro a ha b hb
  have h := hS _ ha _ hb
  show -a - b + t ∈ S
  have ht : -(a + t) - (b + t) = -a - b + t := by
    have := neg_two_nsmul t
    rw [show -(a + t) - (b + t) = -a - b + -(t + t) by abel, this]
  rwa [ht] at h

theorem IsTauClosed.eq_univ_of_not_collinear {S : Set Pt} (hS : IsTauClosed S) {p q s : Pt}
    (hp : p ∈ S) (hq : q ∈ S) (hs : s ∈ S) (hqp : q ≠ p) (hsp : s ≠ p) (hsq : s ≠ q)
    (hl : s ≠ -p - q) : S = Set.univ := by
  set S' : Set Pt := {x | x + p ∈ S}
  have hS' : IsTauClosed S' := hS.translate p
  have h0 : (0 : Pt) ∈ S' := by simpa [S'] using hp
  have hq' : q - p ∈ S' := by simpa [S'] using hq
  have hs' : s - p ∈ S' := by simpa [S'] using hs
  have hne1 : q - p ≠ 0 := sub_ne_zero.2 hqp
  have hne2 : s - p ≠ 0 := sub_ne_zero.2 hsp
  have hne3 : s - p ≠ q - p := fun h => hsq (sub_left_inj.1 h)
  have hne4 : s - p ≠ -(q - p) := by
    intro h
    apply hl
    have h2 : -(p + p) = p := neg_two_nsmul p
    calc s = s - p + p := by abel
      _ = -(q - p) + p := by rw [h]
      _ = -q + (p + p) := by abel
      _ = -q + -(-(p + p)) := by rw [neg_neg]
      _ = -p - q := by rw [h2]; abel
  have hT : (({0, q - p, s - p} : Finset Pt) : Set Pt) ⊆ S' := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h0
    · exact hq'
    · exact hs'
  have hall := tauStep_subset hS' (tauStep_subset hS' (tauStep_subset hS' hT))
  rw [tauStep_three_eq_univ _ _ hne1 hne2 hne3 hne4, Finset.coe_univ] at hall
  rw [Set.eq_univ_iff_forall]
  intro x
  have := hall (Set.mem_univ (x - p))
  simpa [S'] using this

end CFSG.Fischer.Classification.O3
