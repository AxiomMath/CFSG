module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStab
import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

variable {n : ℕ} {s : Setoid (Fin n)}

private abbrev yPlus (s : Setoid (Fin n)) : Subgroup (Perm (Fin n)) :=
  partStab s ⊓ alternatingGroup (Fin n)

open Classical in
private noncomputable def cls (s : Setoid (Fin n)) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun y => s.r x y

private theorem mem_cls {x y : Fin n} : y ∈ cls s x ↔ s.r x y := by simp [cls]

private theorem natCard_eq_card_cls (s : Setoid (Fin n)) (x : Fin n) :
    Nat.card {y // s.r x y} = (cls s x).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_cls.symm)

private theorem swap_rel {a a' : Fin n} (h : s.r a a') (x : Fin n) : s.r (swap a a' x) x := by
  by_cases hxa : x = a
  · subst hxa
    simpa using s.iseqv.symm h
  by_cases hxa' : x = a'
  · subst hxa'
    simpa using h
  rw [swap_apply_of_ne_of_ne hxa hxa']

private theorem mem_partStab_of_rel {g : Perm (Fin n)} (h : ∀ x, s.r (g x) x) :
    g ∈ partStab s :=
  mem_partStab_iff.2 fun x y =>
    ⟨fun hxy => s.iseqv.trans (s.iseqv.symm (h x)) (s.iseqv.trans hxy (h y)),
     fun hxy => s.iseqv.trans (h x) (s.iseqv.trans hxy (s.iseqv.symm (h y)))⟩

private theorem swap_mul_swap_mem {a a' l l' : Fin n} (haa : a ≠ a') (hll : l ≠ l')
    (h1 : s.r a a') (h2 : s.r l l') : swap a a' * swap l l' ∈ yPlus s := by
  refine ⟨mem_partStab_of_rel fun x => ?_, ?_⟩
  · rw [Perm.mul_apply]
    exact s.iseqv.trans (swap_rel h1 _) (swap_rel h2 x)
  · simp [mem_alternatingGroup, sign_swap haa, sign_swap hll]

private theorem inv_rel {g h : Perm (Fin n)} (hg : g ∈ normalizer (yPlus s : Set (Perm (Fin n))))
    (hh : h ∈ yPlus s) (z w : Fin n) : s.r (g (h z)) (g (h w)) ↔ s.r (g z) (g w) := by
  have h1 : g * h * g⁻¹ ∈ partStab s := ((mem_normalizer_iff.1 hg h).1 hh).1
  simpa using h1 (g z) (g w)

private theorem move_core {g : Perm (Fin n)} (hg : g ∈ normalizer (yPlus s : Set (Perm (Fin n))))
    {a a' l l' y : Fin n} (haa : a ≠ a') (hll : l ≠ l') (hal : a ≠ l) (hal' : a ≠ l')
    (h1 : s.r a a') (h2 : s.r l l') (hya : y ≠ a) (hya' : y ≠ a') (hyl : y ≠ l) (hyl' : y ≠ l') :
    s.r (g a) (g y) → s.r (g a') (g y) := by
  intro h
  have key := (inv_rel hg (swap_mul_swap_mem haa hll h1 h2) a y).2 h
  have e1 : (swap a a' * swap l l') a = a' := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hal hal', swap_apply_left]
  have e2 : (swap a a' * swap l l') y = y := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hyl hyl', swap_apply_of_ne_of_ne hya hya']
  rwa [e1, e2] at key

private theorem move_cls {g : Perm (Fin n)} (hg : g ∈ normalizer (yPlus s : Set (Perm (Fin n))))
    {a a' l l' y : Fin n} (haa : a ≠ a') (hll : l ≠ l') (h1 : s.r a a') (h2 : s.r l l')
    (hal : ¬ s.r a l) (hay : ¬ s.r a y) (hly : ¬ s.r l y) :
    s.r (g a) (g y) → s.r (g a') (g y) := by
  refine move_core hg haa hll ?_ ?_ h1 h2 ?_ ?_ ?_ ?_
  · rintro rfl
    exact hal (s.iseqv.refl _)
  · rintro rfl
    exact hal (s.iseqv.symm h2)
  · rintro rfl
    exact hay (s.iseqv.refl _)
  · rintro rfl
    exact hay h1
  · rintro rfl
    exact hly (s.iseqv.refl _)
  · rintro rfl
    exact hly h2

private theorem length_le_card {S : Finset (Fin n)} {l : List (Fin n)} (hl : l.Nodup)
    (h : ∀ p ∈ l, p ∈ S) : l.length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup hl]
  exact Finset.card_le_card fun p hp => h p (List.mem_toFinset.1 hp)

private theorem mem_partStab_of_imp {g : Perm (Fin n)}
    (h : ∀ x y, s.r (g x) (g y) → s.r x y) : g ∈ partStab s := by
  have hT : ∀ x y, y ∈ (cls s (g x)).map g.symm.toEmbedding ↔ s.r (g x) (g y) := by
    intro x y
    simp [Finset.mem_map_equiv, mem_cls]
  have hsub : ∀ x, (cls s (g x)).map g.symm.toEmbedding ⊆ cls s x := fun x y hy =>
    mem_cls.2 (h x y ((hT x y).1 hy))
  have hle : ∀ x, (cls s (g x)).card ≤ (cls s x).card := fun x => by
    simpa using Finset.card_le_card (hsub x)
  have heq := (Finset.sum_eq_sum_iff_of_le fun x _ => hle x).1
    (Equiv.sum_comp g fun x => (cls s x).card)
  refine mem_partStab_iff.2 fun x y => ⟨h x y, fun hxy => ?_⟩
  have hx : (cls s (g x)).map g.symm.toEmbedding = cls s x :=
    Finset.eq_of_subset_of_card_le (hsub x) (by simp [heq x (Finset.mem_univ x)])
  exact (hT x y).1 (hx ▸ mem_cls.2 hxy)

private theorem le_normalizer_inf_alt (Y : Subgroup (Perm (Fin n))) :
    Y ≤ normalizer ((Y ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) := by
  intro g hg
  refine mem_normalizer_iff.2 fun h => ?_
  simp only [mem_inf, mem_alternatingGroup, map_mul, map_inv, mul_inv_cancel_comm,
    Y.mul_mem_cancel_right (Y.inv_mem hg), Y.mul_mem_cancel_left hg]

private theorem normalizer_eq_of_key
    (key : ∀ g ∈ normalizer (yPlus s : Set (Perm (Fin n))), ∀ x y, s.r (g x) (g y) → s.r x y) :
    normalizer (yPlus s : Set (Perm (Fin n))) = partStab s :=
  le_antisymm (fun g hg => mem_partStab_of_imp (key g hg)) (le_normalizer_inf_alt _)

private theorem cls_eq_of_rel {x y : Fin n} (h : s.r x y) : cls s x = cls s y := by
  ext z
  simp only [mem_cls]
  exact ⟨fun hz => s.iseqv.trans (s.iseqv.symm h) hz, fun hz => s.iseqv.trans h hz⟩

private theorem exists_notMem_of_card_lt {E : Finset (Fin n)} (h : E.card < n) :
    ∃ l, l ∉ E := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := E) (t := Finset.univ)
    (by simpa using h)
  exact ⟨l, hl⟩

private theorem exists_out {x y : Fin n} (h : (cls s x).card + (cls s y).card < n) :
    ∃ l, ¬ s.r x l ∧ ¬ s.r y l := by
  obtain ⟨l, hl⟩ := exists_notMem_of_card_lt (E := cls s x ∪ cls s y)
    (lt_of_le_of_lt (Finset.card_union_le _ _) h)
  exact ⟨l, fun h' => hl (Finset.mem_union_left _ (mem_cls.2 h')),
    fun h' => hl (Finset.mem_union_right _ (mem_cls.2 h'))⟩

private theorem exists_out3 {x y z : Fin n}
    (h : (cls s x).card + (cls s y).card + (cls s z).card < n) :
    ∃ l, ¬ s.r x l ∧ ¬ s.r y l ∧ ¬ s.r z l := by
  obtain ⟨l, hl⟩ := exists_notMem_of_card_lt (E := cls s x ∪ cls s y ∪ cls s z)
    (lt_of_le_of_lt ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)) h)
  simp only [Finset.mem_union, mem_cls, not_or] at hl
  exact ⟨l, hl.1.1, hl.1.2, hl.2⟩

private theorem three_le_card {g : Perm (Fin n)}
    (hg : g ∈ normalizer (yPlus s : Set (Perm (Fin n)))) {x x' y l l' : Fin n}
    (hxx : x ≠ x') (hll : l ≠ l') (h1 : s.r x x') (h2 : s.r l l') (hxl : ¬ s.r x l)
    (hxy : ¬ s.r x y) (hly : ¬ s.r l y) (h : s.r (g x) (g y)) : 3 ≤ (cls s (g x)).card := by
  have h' := move_cls hg hxx hll h1 h2 hxl hxy hly h
  have hx'y : x' ≠ y := fun e => hxy (e ▸ h1)
  have hxy' : x ≠ y := fun e => hxy (e ▸ s.iseqv.refl x)
  have hnd : [g x, g x', g y].Nodup := by
    simp [g.injective.eq_iff, hxx, hxy', hx'y]
  have := length_le_card hnd (S := cls s (g x)) ?_
  · simpa using this
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact mem_cls.2 (s.iseqv.refl _)
    · exact mem_cls.2 (s.iseqv.trans h (s.iseqv.symm h'))
    · exact mem_cls.2 h

private theorem key_three {g : Perm (Fin n)} (hg : g ∈ normalizer (yPlus s : Set (Perm (Fin n))))
    (hle : ∀ w, (cls s w).card ≤ 2)
    (hout : ∀ x y, ∃ l, ¬ s.r x l ∧ ¬ s.r y l ∧ 2 ≤ (cls s l).card)
    {x y : Fin n} (hx : 2 ≤ (cls s x).card) (hxy : ¬ s.r x y) : ¬ s.r (g x) (g y) := by
  intro h
  obtain ⟨x', hx', hxx'⟩ := Finset.exists_mem_ne (s := cls s x) (by omega) x
  obtain ⟨l, hxl, hyl, hl2⟩ := hout x y
  obtain ⟨l', hl', hll'⟩ := Finset.exists_mem_ne (s := cls s l) (by omega) l
  have h3 := three_le_card hg hxx'.symm hll'.symm (mem_cls.1 hx') (mem_cls.1 hl') hxl hxy
    (fun e => hyl (s.iseqv.symm e)) h
  have := hle (g x)
  omega

private theorem key_three'
    (hle : ∀ w, (cls s w).card ≤ 2)
    (hout : ∀ x y, ∃ l, ¬ s.r x l ∧ ¬ s.r y l ∧ 2 ≤ (cls s l).card)
    (hcase : ∀ x y, ¬ s.r x y → 2 ≤ (cls s x).card ∨ 2 ≤ (cls s y).card) :
    ∀ g ∈ normalizer (yPlus s : Set (Perm (Fin n))), ∀ x y, s.r (g x) (g y) → s.r x y := by
  intro g hg x y h
  by_contra hxy
  rcases hcase x y hxy with hx | hy
  · exact key_three hg hle hout hx hxy h
  · exact key_three hg hle hout hy (fun h' => hxy (s.iseqv.symm h')) (s.iseqv.symm h)

private theorem five_le_card {g : Perm (Fin n)}
    (hg : g ∈ normalizer (yPlus s : Set (Perm (Fin n)))) {x y : Fin n}
    (hx : (cls s x).card = 4) (hxy : ¬ s.r x y) (h : s.r (g x) (g y)) :
    5 ≤ (cls s (g x)).card := by
  obtain ⟨x₁, x₂, x₃, h12, h13, h23, hE⟩ := Finset.card_eq_three.1
    (show ((cls s x).erase x).card = 3 by
      rw [Finset.card_erase_of_mem (mem_cls.2 (s.iseqv.refl x)), hx])
  have hm : ∀ z, z ∈ ({x₁, x₂, x₃} : Finset (Fin n)) → z ≠ x ∧ s.r x z := fun z hz => by
    rw [← hE, Finset.mem_erase, mem_cls] at hz
    exact hz
  obtain ⟨n1, r1⟩ := hm x₁ (by simp)
  obtain ⟨n2, r2⟩ := hm x₂ (by simp)
  obtain ⟨n3, r3⟩ := hm x₃ (by simp)
  have hy : ∀ z, s.r x z → y ≠ z := fun z hz e => hxy (e ▸ hz)
  have r12 := s.iseqv.trans (s.iseqv.symm r1) r2
  have r13 := s.iseqv.trans (s.iseqv.symm r1) r3
  have r23 := s.iseqv.trans (s.iseqv.symm r2) r3
  have m1 := move_core hg n1.symm h23 n2.symm n3.symm r1 r23 (hy x (s.iseqv.refl x)) (hy _ r1)
    (hy _ r2) (hy _ r3) h
  have m2 := move_core hg n2.symm h13 n1.symm n3.symm r2 r13 (hy x (s.iseqv.refl x)) (hy _ r2)
    (hy _ r1) (hy _ r3) h
  have m3 := move_core hg n3.symm h12 n1.symm n2.symm r3 r12 (hy x (s.iseqv.refl x)) (hy _ r3)
    (hy _ r1) (hy _ r2) h
  have hnd : [g x, g x₁, g x₂, g x₃, g y].Nodup := by
    simp [g.injective.eq_iff, h12, h13, h23, (hy x (s.iseqv.refl x)).symm,
      (hy _ r1).symm, (hy _ r2).symm, (hy _ r3).symm, n1.symm, n2.symm, n3.symm]
  have := length_le_card hnd (S := cls s (g x)) ?_
  · simpa using this
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem_cls.2 (s.iseqv.refl _)
    · exact mem_cls.2 (s.iseqv.trans h (s.iseqv.symm m1))
    · exact mem_cls.2 (s.iseqv.trans h (s.iseqv.symm m2))
    · exact mem_cls.2 (s.iseqv.trans h (s.iseqv.symm m3))
    · exact mem_cls.2 h

private theorem key_four (hle : ∀ w, (cls s w).card ≤ 4)
    (hcase : ∀ x y, ¬ s.r x y → (cls s x).card = 4 ∨ (cls s y).card = 4) :
    ∀ g ∈ normalizer (yPlus s : Set (Perm (Fin n))), ∀ x y, s.r (g x) (g y) → s.r x y := by
  intro g hg x y h
  by_contra hxy
  rcases hcase x y hxy with hx | hy
  · have := five_le_card hg hx hxy h
    have := hle (g x)
    omega
  · have := five_le_card hg hy (fun h' => hxy (s.iseqv.symm h')) (s.iseqv.symm h)
    have := hle (g y)
    omega

private theorem key_four_special {b : Fin n} (hb : (cls s b).card ≤ 4)
    (hs : ∀ x, ¬ s.r b x → (cls s x).card = 4) :
    ∀ g ∈ normalizer (yPlus s : Set (Perm (Fin n))), ∀ x y, s.r (g x) (g y) → s.r x y := by
  refine key_four (fun w => ?_) fun x y hxy => ?_
  · by_cases hbw : s.r b w
    · rw [← cls_eq_of_rel hbw]
      exact hb
    · exact (hs w hbw).le
  · by_cases hbx : s.r b x
    · exact Or.inr (hs y fun hby => hxy (s.iseqv.trans (s.iseqv.symm hbx) hby))
    · exact Or.inl (hs x hbx)

theorem normalizer_partStab_inf_pairs (hn : 6 ≤ n) (hs : ∀ x, Nat.card {y // s.r x y} = 2) :
    normalizer ((partStab s ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) = partStab s := by
  simp only [natCard_eq_card_cls] at hs
  refine normalizer_eq_of_key (key_three' (fun w => (hs w).le) (fun x y => ?_)
    fun x y _ => Or.inl (hs x).ge)
  obtain ⟨l, hxl, hyl⟩ := exists_out (s := s) (x := x) (y := y) (by rw [hs x, hs y]; omega)
  exact ⟨l, hxl, hyl, (hs l).ge⟩

theorem normalizer_partStab_inf_quads (hn : 8 ≤ n) (hs : ∀ x, Nat.card {y // s.r x y} = 4) :
    normalizer ((partStab s ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) = partStab s := by
  simp only [natCard_eq_card_cls] at hs
  exact normalizer_eq_of_key (key_four_special (b := ⟨0, by omega⟩) (hs _).le fun x _ => hs x)

theorem normalizer_partStab_inf_quadsPair (hn : 10 ≤ n) {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 2) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) :
    normalizer ((partStab s ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) = partStab s := by
  have _ := hn
  simp only [natCard_eq_card_cls] at hb hs
  exact normalizer_eq_of_key (key_four_special (by omega) hs)

theorem normalizer_partStab_inf_pairsPoint (hn : 7 ≤ n) {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 1) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 2) :
    normalizer ((partStab s ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) = partStab s := by
  simp only [natCard_eq_card_cls] at hb hs
  have hle : ∀ w, (cls s w).card ≤ 2 := by
    intro w
    by_cases hbw : s.r b w
    · rw [← cls_eq_of_rel hbw, hb]
      omega
    · exact (hs w hbw).le
  refine normalizer_eq_of_key (key_three' hle (fun x y => ?_) fun x y hxy => ?_)
  · obtain ⟨l, hxl, hyl, hbl⟩ := exists_out3 (s := s) (x := x) (y := y) (z := b)
      (by have := hle x; have := hle y; omega)
    exact ⟨l, hxl, hyl, (hs l hbl).ge⟩
  · by_cases hbx : s.r b x
    · exact Or.inr (hs y fun hby => hxy (s.iseqv.trans (s.iseqv.symm hbx) hby)).ge
    · exact Or.inl (hs x hbx).ge

theorem normalizer_partStab_inf_quadsTriple (hn : 7 ≤ n) {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 3) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) :
    normalizer ((partStab s ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) = partStab s := by
  have _ := hn
  simp only [natCard_eq_card_cls] at hb hs
  exact normalizer_eq_of_key (key_four_special (by omega) hs)

private abbrev stabSet (Γ : Finset (Fin n)) : Subgroup (Perm (Fin n)) :=
  MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n))

private theorem mem_stabSet_iff {Γ : Finset (Fin n)} {g : Perm (Fin n)} :
    g ∈ stabSet Γ ↔ ∀ x, g x ∈ Γ ↔ x ∈ Γ := by
  rw [stabSet, MulAction.mem_stabilizer_set]
  simp only [Perm.smul_def, Finset.mem_coe]

private theorem swap_mem_stabSet {Γ : Finset (Fin n)} {a b : Fin n} (h : a ∈ Γ ↔ b ∈ Γ) :
    swap a b ∈ stabSet Γ := by
  rw [mem_stabSet_iff]
  intro x
  by_cases hxa : x = a
  · subst hxa
    simpa using h.symm
  by_cases hxb : x = b
  · subst hxb
    simpa using h
  rw [swap_apply_of_ne_of_ne hxa hxb]

private theorem exists_mem_stabSet_inf {Γ D : Finset (Fin n)} (hD : D.card = 1 ∨ 3 ≤ D.card)
    (hsame : ∀ a ∈ D, ∀ b ∈ D, (a ∈ Γ ↔ b ∈ Γ)) {x y : Fin n} (hx : x ∈ D) (hy : y ∈ D) :
    ∃ h ∈ stabSet Γ ⊓ alternatingGroup (Fin n), h x = y := by
  by_cases hxy : x = y
  · exact ⟨1, one_mem _, by simp [hxy]⟩
  have h3 : 3 ≤ D.card := by
    rcases hD with hD | hD
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hD
      simp only [Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · exact hD
  obtain ⟨z, hz, hzxy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x, y}) (t := D)
    (lt_of_le_of_lt Finset.card_le_two h3)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzxy
  refine ⟨swap x z * swap x y, ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (swap_mem_stabSet (hsame x hx z hz)) (swap_mem_stabSet (hsame x hx y hy))
  · simp [mem_alternatingGroup, sign_swap (Ne.symm hzxy.1), sign_swap hxy]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxy) (Ne.symm hzxy.2)]

private theorem eq_of_card_of_invariant {Γ Q : Finset (Fin n)} (hΓ : Γ.card = 1 ∨ 3 ≤ Γ.card)
    (hΓc : Γ.card + 3 ≤ n) (hne : 2 * Γ.card ≠ n) (hQc : Q.card = Γ.card)
    (hinv : ∀ h ∈ stabSet Γ ⊓ alternatingGroup (Fin n), ∀ w, h w ∈ Q ↔ w ∈ Q) : Q = Γ := by
  by_cases hA : ∃ x ∈ Q, x ∈ Γ
  · obtain ⟨x, hxQ, hxΓ⟩ := hA
    have hsub : Γ ⊆ Q := fun y hy => by
      obtain ⟨h, hh, hxy⟩ := exists_mem_stabSet_inf hΓ (fun a ha b hb => iff_of_true ha hb) hxΓ hy
      exact hxy ▸ (hinv h hh x).2 hxQ
    exact (Finset.eq_of_subset_of_card_le hsub hQc.le).symm
  · replace hA : ∀ x ∈ Q, x ∉ Γ := fun x hx hxΓ => hA ⟨x, hx, hxΓ⟩
    obtain ⟨x, hxQ⟩ : Q.Nonempty := Finset.card_pos.1 (by rcases hΓ with h | h <;> omega)
    have hc := Finset.card_compl Γ
    rw [Fintype.card_fin] at hc
    have hsub : Γᶜ ⊆ Q := fun y hy => by
      obtain ⟨h, hh, hxy⟩ := exists_mem_stabSet_inf (D := Γᶜ) (Or.inr (by omega))
        (fun a ha b hb => iff_of_false (Finset.mem_compl.1 ha) (Finset.mem_compl.1 hb))
        (Finset.mem_compl.2 (hA x hxQ)) hy
      exact hxy ▸ (hinv h hh x).2 hxQ
    have heq : Q = Γᶜ :=
      Finset.Subset.antisymm (fun w hw => Finset.mem_compl.2 (hA w hw)) hsub
    rw [heq] at hQc
    omega

theorem normalizer_stabilizer_finset_inf {Γ : Finset (Fin n)} (hΓ : Γ.card = 1 ∨ 3 ≤ Γ.card)
    (hΓc : Γ.card + 3 ≤ n) (hne : 2 * Γ.card ≠ n) :
    normalizer ((MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n)) ⊓
      alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) =
      MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n)) := by
  refine le_antisymm (fun g hg => ?_) (le_normalizer_inf_alt _)
  have hQ : ∀ w, w ∈ Γ.map g.symm.toEmbedding ↔ g w ∈ Γ := fun w => by
    simp [Finset.mem_map_equiv]
  have hQe := eq_of_card_of_invariant (Q := Γ.map g.symm.toEmbedding) hΓ hΓc hne (by simp)
    fun h hh w => by
    have h1 : g * h * g⁻¹ ∈ stabSet Γ := ((mem_normalizer_iff.1 hg h).1 hh).1
    simpa [hQ] using mem_stabSet_iff.1 h1 (g w)
  rw [mem_stabSet_iff]
  intro x
  rw [← hQ, hQe]

end CFSG.GroupTheory.AltCore
