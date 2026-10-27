module

public import Certificates.Data.Kernel.PosWalk
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card

public section

namespace CFSG.KC.PosWalk

open CFSG.KC.Loop CFSG.KS.PEnum

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem walkK_cons (Cl : Nat → Nat) (k l : Nat) (wd : List Nat) (x : Nat) :
    walkK Cl k (l :: wd) x = walkK Cl k wd (wstepK Cl k x l) := by
  change strictN (wstepK Cl k x l) (walkK Cl k wd) = _
  rw [strictN_eq']

theorem walk_sound {α : Type*} {Cl : Nat → Nat} {T G : Nat → α} {pc : α → α → α} {k cnt : Nat}
    (hcl : ∀ x < cnt, ∀ l < k, wstepK Cl k x l < cnt ∧ T (wstepK Cl k x l) = pc (T x) (G l)) :
    ∀ wd : List Nat, (∀ l ∈ wd, l < k) → ∀ x < cnt,
      walkK Cl k wd x < cnt ∧ T (walkK Cl k wd x) = wd.foldl (fun a l => pc a (G l)) (T x)
  | [], _, _, hx => ⟨hx, rfl⟩
  | l :: wd, hw, x, hx => by
    obtain ⟨h1, h2⟩ := hcl x hx l (hw l List.mem_cons_self)
    have ih := walk_sound hcl wd (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ h1
    rw [walkK_cons, List.foldl_cons, ← h2]
    exact ih

theorem pathPosK_zero (Cl PL : Nat → Nat) (k fuel x : Nat) : pathPosK Cl k PL fuel x 0 = x := by
  cases fuel <;> rfl

theorem pathPosK_succ (Cl PL : Nat → Nat) (k fuel x n : Nat) :
    pathPosK Cl k PL (fuel + 1) x (n + 1) =
      wstepK Cl k (pathPosK Cl k PL fuel x (parOf PL (n + 1))) (labOf PL (n + 1)) := by
  change strictN (pathPosK Cl k PL fuel x (parOf PL (n + 1)))
    (fun p => wstepK Cl k p (labOf PL (n + 1))) = _
  rw [strictN_eq']

theorem pathPos_sound {α : Type*} {Cl PL : Nat → Nat} {T G : Nat → α} {pc : α → α → α}
    {k cnt : Nat}
    (hcl : ∀ x < cnt, ∀ l < k, wstepK Cl k x l < cnt ∧ T (wstepK Cl k x l) = pc (T x) (G l))
    (htree : ∀ y < cnt, y ≠ 0 → parOf PL y < y ∧ labOf PL y < k ∧
      T y = pc (T (parOf PL y)) (G (labOf PL y)))
    (hassoc : ∀ x < cnt, ∀ y < cnt, ∀ l < k, pc (pc (T x) (T y)) (G l) = pc (T x) (pc (T y) (G l)))
    (hid : ∀ x < cnt, pc (T x) (T 0) = T x) :
    ∀ fuel y, y ≤ fuel → y < cnt → ∀ x < cnt,
      pathPosK Cl k PL fuel x y < cnt ∧ T (pathPosK Cl k PL fuel x y) = pc (T x) (T y)
  | fuel, 0, _, _, x, hx => by
    rw [pathPosK_zero, hid x hx]
    exact ⟨hx, rfl⟩
  | 0, n + 1, hy, _, _, _ => absurd hy (by omega)
  | fuel + 1, n + 1, hy, hyc, x, hx => by
    obtain ⟨hp, hl, ht⟩ := htree (n + 1) hyc (by omega)
    obtain ⟨ih1, ih2⟩ :=
      pathPos_sound hcl htree hassoc hid fuel (parOf PL (n + 1)) (by omega) (by omega) x hx
    obtain ⟨h1, h2⟩ := hcl _ ih1 _ hl
    rw [pathPosK_succ]
    refine ⟨h1, ?_⟩
    rw [h2, ih2, hassoc x hx _ (by omega) _ hl, ← ht]

theorem cntK_succ (n : Nat) (f : Nat → Bool) :
    cntK (n + 1) f = cntK n f + (if f n then 1 else 0) := by
  change Bool.rec (motive := fun _ => Nat) (cntK n f) (Nat.succ (cntK n f)) (f n) = _
  cases f n <;> rfl

theorem cntK_eq (f : Nat → Bool) : ∀ n, cntK n f = ((List.range n).filter f).length
  | 0 => rfl
  | n + 1 => by
    rw [cntK_succ, cntK_eq f n, List.range_succ, List.filter_append, List.length_append]
    cases h : f n <;> simp [h]

section Closure

variable {M : Type*} [Group M]

theorem mem_closure_of_tree {m ng : Nat} {f h : Nat → M} (h0 : f 0 = 1)
    (htree : ∀ i < m, i ≠ 0 → ∃ p < i, ∃ l < ng, f i = f p * h l) :
    ∀ i < m, f i ∈ Subgroup.closure (h '' {l | l < ng}) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0]
      exact Subgroup.one_mem _
    · obtain ⟨p, hp, l, hl, e⟩ := htree i hi (by omega)
      rw [e]
      exact Subgroup.mul_mem _ (ih p hp (by omega)) (Subgroup.subset_closure ⟨l, hl, rfl⟩)

theorem closure_subset_of_closed {m ng : Nat} {f h : Nat → M} (h0 : f 0 = 1) (hm : 0 < m)
    (hcl : ∀ i < m, ∀ l < ng, ∃ j < m, f i * h l = f j) :
    ∀ x ∈ Subgroup.closure (h '' {l | l < ng}), x ∈ f '' {i | i < m} := by
  have hfin : (f '' {i | i < m}).Finite := (Set.finite_lt_nat m).image f
  have key : ∀ x ∈ Subgroup.closure (h '' {l | l < ng}), ∀ y ∈ f '' {i | i < m},
      y * x ∈ f '' {i | i < m} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hcl i hi l hl
      exact ⟨j, hj, e.symm⟩
    | one =>
      intro y hy
      rwa [mul_one]
    | mul x y _ _ hx hy =>
      intro z hz
      rw [← mul_assoc]
      exact hy _ (hx z hz)
    | inv x _ hx =>
      intro y hy
      have hmaps : Set.MapsTo (fun z => z * x) (f '' {i | i < m}) (f '' {i | i < m}) :=
        fun z hz => hx z hz
      have hinj : Set.InjOn (fun z => z * x) (f '' {i | i < m}) := fun a _ b _ e =>
        mul_right_cancel e
      obtain ⟨z, hz, e⟩ := ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn hy
      rw [← e, mul_inv_cancel_right]
      exact hz
  intro x hx
  have h1 : (1 : M) ∈ f '' {i | i < m} := ⟨0, hm, h0⟩
  simpa using key x hx 1 h1

theorem closure_eq_of_tree {m ng : Nat} {f h : Nat → M} (h0 : f 0 = 1) (hm : 0 < m)
    (htree : ∀ i < m, i ≠ 0 → ∃ p < i, ∃ l < ng, f i = f p * h l)
    (hcl : ∀ i < m, ∀ l < ng, ∃ j < m, f i * h l = f j) :
    (Subgroup.closure (h '' {l | l < ng}) : Set M) = f '' {i | i < m} := by
  ext x
  constructor
  · exact closure_subset_of_closed h0 hm hcl x
  · rintro ⟨i, hi, rfl⟩
    exact mem_closure_of_tree h0 htree i hi

theorem card_eq_cntK {α : Type*} {S : Set α} {f : Nat → α} {m : Nat} (hS : S = f '' {i | i < m})
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) (p : α → Prop) (b : Nat → Bool)
    (hb : ∀ i < m, b i = true ↔ p (f i)) :
    Nat.card {y // y ∈ S ∧ p y} = cntK m b := by
  classical
  have e : {y | y ∈ S ∧ p y} = f '' ↑((List.range m).filter b).toFinset := by
    ext y
    simp only [Set.mem_setOf_eq, hS, Set.mem_image, Finset.mem_coe, List.mem_toFinset,
      List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hp⟩
      exact ⟨i, ⟨hi, (hb i hi).2 hp⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hbi⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (hb i hi).1 hbi⟩
  have hi : Set.InjOn f ↑((List.range m).filter b).toFinset := by
    intro i hi j hj h
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hi hj
    exact hinj i hi.1 j hj.1 h
  change Nat.card ↥{y | y ∈ S ∧ p y} = _
  rw [Nat.card_coe_set_eq, e, hi.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (List.nodup_range.filter _), cntK_eq]

end Closure

end CFSG.KC.PosWalk

end
