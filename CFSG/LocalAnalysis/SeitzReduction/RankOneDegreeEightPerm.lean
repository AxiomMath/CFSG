module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.SeitzReduction.RankOne.DegreeEight

open Equiv
open scoped LinearAlgebra.Projectivization MatrixGroups

@[expose] def invol (f : Option (ZMod 7) → Option (ZMod 7)) (hf : ∀ x, f (f x) = x) :
    Perm (Option (ZMod 7)) :=
  ⟨f, f, hf, hf⟩

@[expose] def shift : Perm (Option (ZMod 7)) :=
  ⟨Option.map (· + 1), Option.map (· + 6), by intro x; revert x; decide,
    by intro x; revert x; decide⟩

@[expose] def dbl : Perm (Option (ZMod 7)) :=
  ⟨Option.map (2 * ·), Option.map (4 * ·), by intro x; revert x; decide,
    by intro x; revert x; decide⟩

theorem shift_none : shift none = none := rfl

theorem shift_some (z : ZMod 7) : shift (some z) = some (z + 1) := rfl

theorem dbl_none : dbl none = none := rfl

theorem dbl_some (z : ZMod 7) : dbl (some z) = some (2 * z) := rfl

@[expose] def IsAffine (σ : Perm (Option (ZMod 7))) : Prop :=
  σ none = none ∧ ∃ c d : ZMod 7, c ^ 3 = 1 ∧ ∀ z : ZMod 7, σ (some z) = some (c * z + d)

instance (σ : Perm (Option (ZMod 7))) : Decidable (IsAffine σ) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[expose] def mulF (c : ZMod 7) : Option (ZMod 7) → Option (ZMod 7) :=
  Option.map (c * ·)

theorem shift_pow_seven : shift ^ 7 = 1 := by decide

theorem dbl_pow_three : dbl ^ 3 = 1 := by decide

theorem isAffine_shift_pow_mul_dbl_pow_lt :
    ∀ m < 7, ∀ j < 3, IsAffine (shift ^ m * dbl ^ j) := by decide

theorem isAffine_shift_pow_mul_dbl_pow (m j : ℕ) : IsAffine (shift ^ m * dbl ^ j) := by
  rw [pow_eq_pow_mod m shift_pow_seven, pow_eq_pow_mod j dbl_pow_three]
  exact isAffine_shift_pow_mul_dbl_pow_lt _ (Nat.mod_lt _ (by norm_num)) _
    (Nat.mod_lt _ (by norm_num))

theorem exists_shift_pow_mul_dbl_pow :
    ∀ c d : ZMod 7, c ^ 3 = 1 → ∃ m < 7, ∃ j < 3,
      ∀ z : ZMod 7, (shift ^ m * dbl ^ j) (some z) = some (c * z + d) := by decide

theorem eq_shift_pow_mul_dbl_pow_of_isAffine {σ : Perm (Option (ZMod 7))} (hσ : IsAffine σ) :
    ∃ m < 7, ∃ j < 3, σ = shift ^ m * dbl ^ j := by
  obtain ⟨hinf, c, d, hc, hσz⟩ := hσ
  obtain ⟨m, hm, j, hj, hmj⟩ := exists_shift_pow_mul_dbl_pow c d hc
  refine ⟨m, hm, j, hj, Equiv.ext fun x => ?_⟩
  cases x with
  | none => rw [hinf, (isAffine_shift_pow_mul_dbl_pow m j).1]
  | some z => rw [hσz, hmj]

theorem affine_involution_cases :
    ∀ c d : ZMod 7, c ^ 3 = 1 → (∀ z : ZMod 7, c * (c * z + d) + d = z) → c = 1 ∧ d = 0 := by
  decide

theorem eq_one_of_isAffine_of_mul_self {σ : Perm (Option (ZMod 7))} (hσ : IsAffine σ)
    (h2 : σ * σ = 1) : σ = 1 := by
  obtain ⟨hinf, c, d, hc, hσz⟩ := hσ
  have hcd := affine_involution_cases c d hc fun z => by
    have h1 : (σ * σ) (some z) = some z := by rw [h2]; rfl
    rw [Perm.mul_apply, hσz, hσz] at h1
    exact Option.some.inj h1
  refine Equiv.ext fun x => ?_
  cases x with
  | none => exact hinf
  | some z => rw [hσz, hcd.1, hcd.2, one_mul, add_zero]; rfl

theorem exists_mulF_of_isAffine {σ : Perm (Option (ZMod 7))} (hσ : IsAffine σ)
    (h0 : σ (some 0) = some 0) : ∃ c : ZMod 7, c ^ 3 = 1 ∧ ∀ x, σ x = mulF c x := by
  obtain ⟨hinf, c, d, hc, hσz⟩ := hσ
  have hd : d = 0 := by
    have h1 := h0
    rw [hσz, mul_zero, zero_add] at h1
    exact Option.some.inj h1
  refine ⟨c, hc, fun x => ?_⟩
  cases x with
  | none => exact hinf
  | some z => rw [hσz, hd, add_zero]; rfl

theorem mulF_pow_three {c : ZMod 7} (hc : c ^ 3 = 1) (x : Option (ZMod 7)) :
    mulF c (mulF c (mulF c x)) = x := by
  cases x with
  | none => rfl
  | some z =>
    change some (c * (c * (c * z))) = some z
    rw [← mul_assoc, ← mul_assoc, ← pow_three', hc, one_mul]

theorem cube_root_cases : ∀ c : ZMod 7, c ^ 3 = 1 → c ≠ 1 → c = 2 ∨ c = 4 := by decide

theorem dbl_ne_one : dbl ≠ 1 := by decide

theorem shift_pow_some (m : ℕ) (z : ZMod 7) : (shift ^ m) (some z) = some (z + m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', Perm.mul_apply, ih, shift_some, Nat.cast_succ, add_assoc]

section Group

variable {N : Subgroup (Perm (Option (ZMod 7)))}

theorem exists_swap_involution (hstab : ∀ σ ∈ N, σ none = none → IsAffine σ)
    {s : Perm (Option (ZMod 7))} (hs : s ∈ N) (hsinf : s none = some 0)
    (hs0 : s (some 0) = none) :
    ∃ t ∈ N, t * t = 1 ∧ t none = some 0 ∧ t (some 0) = none := by
  have hu : s * s ∈ N := mul_mem hs hs
  have huinf : (s * s) none = none := by rw [Perm.mul_apply, hsinf, hs0]
  have hu0 : (s * s) (some 0) = some 0 := by rw [Perm.mul_apply, hs0, hsinf]
  obtain ⟨c, hc, hcx⟩ := exists_mulF_of_isAffine (hstab _ hu huinf) hu0
  have hcx' : ∀ x, s (s x) = mulF c x := fun x => hcx x
  refine ⟨s * (s * s), mul_mem hs hu, ?_, ?_, ?_⟩
  · refine Equiv.ext fun x => ?_
    simp only [Perm.mul_apply, Perm.one_apply]
    rw [hcx', hcx', hcx', mulF_pow_three hc]
  · rw [Perm.mul_apply, huinf, hsinf]
  · rw [Perm.mul_apply, hu0, hs0]

theorem exists_conj_dbl (hstab : ∀ σ ∈ N, σ none = none → IsAffine σ) (hdbl : dbl ∈ N)
    {t : Perm (Option (ZMod 7))} (ht : t ∈ N) (htt : t * t = 1) (htinf : t none = some 0)
    (ht0 : t (some 0) = none) :
    ∃ c : ZMod 7, (c = 2 ∨ c = 4) ∧ ∀ x, t (dbl x) = mulF c (t x) := by
  have hv : t * dbl * t ∈ N := mul_mem (mul_mem ht hdbl) ht
  have hvinf : (t * dbl * t) none = none := by
    rw [Perm.mul_apply, Perm.mul_apply, htinf, dbl_some, mul_zero, ht0]
  have hv0 : (t * dbl * t) (some 0) = some 0 := by
    rw [Perm.mul_apply, Perm.mul_apply, ht0, dbl_none, htinf]
  obtain ⟨c, hc, hcx⟩ := exists_mulF_of_isAffine (hstab _ hv hvinf) hv0
  have htx : ∀ x, t (t x) = x := fun x => by rw [← Perm.mul_apply, htt]; rfl
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply dbl_ne_one
    refine Equiv.ext fun x => ?_
    have h1 := hcx (t x)
    rw [Perm.mul_apply, Perm.mul_apply, htx] at h1
    have h2 : mulF 1 (t x) = t x := by
      cases t x with
      | none => rfl
      | some z => change some (1 * z) = some z; rw [one_mul]
    rw [h2] at h1
    have h3 := congrArg t h1
    rwa [htx, htx] at h3
  refine ⟨c, cube_root_cases c hc hc1, fun x => ?_⟩
  have h1 := hcx (t x)
  rwa [Perm.mul_apply, Perm.mul_apply, htx] at h1

theorem swap_ne_self (hstab : ∀ σ ∈ N, σ none = none → IsAffine σ) (hshift : shift ∈ N)
    {t : Perm (Option (ZMod 7))} (ht : t ∈ N) (htt : t * t = 1) (htinf : t none = some 0)
    (x : Option (ZMod 7)) : t x ≠ x := by
  intro htx
  cases x with
  | none => rw [htinf] at htx; exact Option.some_ne_none _ htx
  | some k =>
    set g : Perm (Option (ZMod 7)) := shift ^ k.val * t with hg
    have hgN : g ∈ N := mul_mem (pow_mem hshift _) ht
    have hginf : g none = some k := by
      rw [hg, Perm.mul_apply, htinf, shift_pow_some, ZMod.natCast_zmod_val, zero_add]
    have hw : g⁻¹ * t * g ∈ N := mul_mem (mul_mem (inv_mem hgN) ht) hgN
    have hwinf : (g⁻¹ * t * g) none = none := by
      rw [Perm.mul_apply, Perm.mul_apply, hginf, htx, Perm.inv_eq_iff_eq, hginf]
    have hw1 := eq_one_of_isAffine_of_mul_self (hstab _ hw hwinf) (by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt, mul_one, inv_mul_cancel])
    have ht1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [hw1, mul_one, mul_inv_cancel]
    rw [ht1] at htinf
    simp at htinf

end Group

@[expose] def tDet (c₁ c₃ : Option (ZMod 7)) (c : ZMod 7) :
    Option (ZMod 7) → Option (ZMod 7)
  | none => some 0
  | some z =>
    if z = 0 then none
    else if z = 1 then c₁ else if z = 2 then mulF c c₁ else if z = 4 then mulF c (mulF c c₁)
    else if z = 3 then c₃ else if z = 6 then mulF c c₃ else mulF c (mulF c c₃)

theorem zmod_seven_cases : ∀ z : ZMod 7,
    z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 := by decide

theorem eq_tDet {t : Perm (Option (ZMod 7))} {c : ZMod 7} (htinf : t none = some 0)
    (ht0 : t (some 0) = none) (hcomm : ∀ x, t (dbl x) = mulF c (t x)) (x : Option (ZMod 7)) :
    t x = tDet (t (some 1)) (t (some 3)) c x := by
  have h2 : t (some 2) = mulF c (t (some 1)) := hcomm (some 1)
  have h4 : t (some 4) = mulF c (t (some 2)) := hcomm (some 2)
  have h6 : t (some 6) = mulF c (t (some 3)) := hcomm (some 3)
  have h5 : t (some 5) = mulF c (t (some 6)) := hcomm (some 6)
  cases x with
  | none => exact htinf
  | some z =>
    rcases zmod_seven_cases z with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht0
    · rfl
    · exact h2
    · rfl
    · rw [h4, h2]; rfl
    · rw [h5, h6]; rfl
    · exact h6

set_option synthInstance.maxSize 1000 in
theorem tDet_cases : ∀ c₁ c₃ : Option (ZMod 7), ∀ c : ZMod 7, c = 2 ∨ c = 4 →
    (∀ x, tDet c₁ c₃ c (tDet c₁ c₃ c x) = x) → (∀ x, tDet c₁ c₃ c x ≠ x) →
    (c = 2 ∧ c₁ = some 3 ∧ c₃ = some 1) ∨ (c = 2 ∧ c₁ = some 5 ∧ c₃ = some 2) ∨
    (c = 2 ∧ c₁ = some 6 ∧ c₃ = some 4) ∨ (c = 4 ∧ c₁ = some 3 ∧ c₃ = some 1) ∨
    (c = 4 ∧ c₁ = some 5 ∧ c₃ = some 4) ∨ (c = 4 ∧ c₁ = some 6 ∧ c₃ = some 2) := by
  decide +kernel

@[expose] def tAff3 : Perm (Option (ZMod 7)) := invol (tDet (some 3) (some 1) 2) (by decide)

@[expose] def tAff5 : Perm (Option (ZMod 7)) := invol (tDet (some 5) (some 2) 2) (by decide)

@[expose] def tBad : Perm (Option (ZMod 7)) := invol (tDet (some 6) (some 4) 2) (by decide)

@[expose] def tPro3 : Perm (Option (ZMod 7)) := invol (tDet (some 3) (some 1) 4) (by decide)

@[expose] def tPro5 : Perm (Option (ZMod 7)) := invol (tDet (some 5) (some 4) 4) (by decide)

@[expose] def tPro6 : Perm (Option (ZMod 7)) := invol (tDet (some 6) (some 2) 4) (by decide)

section Group

variable {N : Subgroup (Perm (Option (ZMod 7)))}

theorem swap_cases (hstab : ∀ σ ∈ N, σ none = none → IsAffine σ) (hshift : shift ∈ N)
    (hdbl : dbl ∈ N) {t : Perm (Option (ZMod 7))} (ht : t ∈ N) (htt : t * t = 1)
    (htinf : t none = some 0) (ht0 : t (some 0) = none) :
    t = tAff3 ∨ t = tAff5 ∨ t = tBad ∨ t = tPro3 ∨ t = tPro5 ∨ t = tPro6 := by
  obtain ⟨c, hc, hcomm⟩ := exists_conj_dbl hstab hdbl ht htt htinf ht0
  have hdet := eq_tDet htinf ht0 hcomm
  have htx : ∀ x, t (t x) = x := fun x => by rw [← Perm.mul_apply, htt]; rfl
  have hcases := tDet_cases (t (some 1)) (t (some 3)) c hc (fun x => by rw [← hdet, ← hdet, htx])
    (fun x => by rw [← hdet]; exact swap_ne_self hstab hshift ht htt htinf x)
  have key : ∀ {c₁ c₃ : Option (ZMod 7)} {c' : ZMod 7} {τ : Perm (Option (ZMod 7))},
      (∀ x, τ x = tDet c₁ c₃ c' x) → c = c' → t (some 1) = c₁ → t (some 3) = c₃ → t = τ := by
    intro c₁ c₃ c' τ hτ hcc h1 h3
    refine Equiv.ext fun x => ?_
    rw [hdet, hτ, hcc, h1, h3]
  rcases hcases with ⟨h, h1, h3⟩ | ⟨h, h1, h3⟩ | ⟨h, h1, h3⟩ | ⟨h, h1, h3⟩ | ⟨h, h1, h3⟩ |
    ⟨h, h1, h3⟩
  · exact Or.inl (key (fun _ => rfl) h h1 h3)
  · exact Or.inr (Or.inl (key (fun _ => rfl) h h1 h3))
  · exact Or.inr (Or.inr (Or.inl (key (fun _ => rfl) h h1 h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key (fun _ => rfl) h h1 h3))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key (fun _ => rfl) h h1 h3)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key (fun _ => rfl) h h1 h3)))))

theorem le_closure (hstab : ∀ σ ∈ N, σ none = none → IsAffine σ) (hshift : shift ∈ N)
    {t : Perm (Option (ZMod 7))} (ht : t ∈ N) (htinf : t none = some 0) :
    N ≤ Subgroup.closure {shift, dbl, t} := by
  intro σ hσ
  have hsc : shift ∈ Subgroup.closure {shift, dbl, t} := Subgroup.subset_closure (by simp)
  have hdc : dbl ∈ Subgroup.closure {shift, dbl, t} := Subgroup.subset_closure (by simp)
  have htc : t ∈ Subgroup.closure {shift, dbl, t} := Subgroup.subset_closure (by simp)
  have hH : ∀ τ ∈ N, τ none = none → τ ∈ Subgroup.closure {shift, dbl, t} := by
    intro τ hτ hτinf
    obtain ⟨m, -, j, -, rfl⟩ := eq_shift_pow_mul_dbl_pow_of_isAffine (hstab τ hτ hτinf)
    exact mul_mem (pow_mem hsc m) (pow_mem hdc j)
  cases hσinf : σ none with
  | none => exact hH σ hσ hσinf
  | some k =>
    set g : Perm (Option (ZMod 7)) := shift ^ k.val * t with hg
    have hginf : g none = some k := by
      rw [hg, Perm.mul_apply, htinf, shift_pow_some, ZMod.natCast_zmod_val, zero_add]
    have hgN : g ∈ N := mul_mem (pow_mem hshift _) ht
    have h1 : g⁻¹ * σ ∈ Subgroup.closure {shift, dbl, t} :=
      hH _ (mul_mem (inv_mem hgN) hσ) (by rw [Perm.mul_apply, hσinf, Perm.inv_eq_iff_eq, hginf])
    have h2 : σ = g * (g⁻¹ * σ) := by group
    rw [h2]
    exact mul_mem (mul_mem (pow_mem hsc _) htc) h1

end Group

theorem tBad_word : (tBad * shift * tBad * shift * tBad) none = none ∧
    ¬ IsAffine (tBad * shift * tBad * shift * tBad) := by
  decide +kernel

@[expose] def affList (t : Perm (Option (ZMod 7))) : List (Perm (Option (ZMod 7))) :=
  1 :: (List.range 7).map (fun j => shift ^ j * t * (shift ^ j)⁻¹)

@[expose] def pts : List (Option (ZMod 7)) :=
  [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6]

theorem mem_pts : ∀ p : Option (ZMod 7), p ∈ pts := by decide

@[expose] def affCheck (t : Perm (Option (ZMod 7))) : Bool :=
  ((affList t).all fun x =>
    ((affList t).all fun y => (affList t).contains (x * y)) &&
    (affList t).contains x⁻¹ &&
    (affList t).contains (shift * x * shift⁻¹) && (affList t).contains (shift⁻¹ * x * shift) &&
    (affList t).contains (dbl * x * dbl⁻¹) && (affList t).contains (dbl⁻¹ * x * dbl) &&
    (affList t).contains (t * x * t⁻¹) && (affList t).contains (t⁻¹ * x * t)) &&
  (pts.all fun p => pts.all fun q =>
    ((affList t).any fun x => x p == q) &&
    ((affList t).all fun x => (affList t).all fun y => !(x p == y p) || x == y))

theorem affCheck_tAff3 : affCheck tAff3 = true := by decide +kernel

theorem affCheck_tAff5 : affCheck tAff5 = true := by decide +kernel

theorem affList_facts {t : Perm (Option (ZMod 7))} (ht : affCheck t = true) :
    (∀ x ∈ affList t, ∀ y ∈ affList t, x * y ∈ affList t) ∧
    (∀ x ∈ affList t, x⁻¹ ∈ affList t) ∧
    (∀ x ∈ affList t,
      (shift * x * shift⁻¹ ∈ affList t ∧ shift⁻¹ * x * shift ∈ affList t) ∧
      (dbl * x * dbl⁻¹ ∈ affList t ∧ dbl⁻¹ * x * dbl ∈ affList t) ∧
      (t * x * t⁻¹ ∈ affList t ∧ t⁻¹ * x * t ∈ affList t)) ∧
    (∀ p q : Option (ZMod 7), (∃ x ∈ affList t, x p = q) ∧
      ∀ x ∈ affList t, ∀ y ∈ affList t, x p = y p → x = y) := by
  simp only [affCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at ht
  obtain ⟨h1, h2⟩ := ht
  refine ⟨fun x hx y hy => (h1 x hx).1.1.1.1.1.1.1 y hy, fun x hx => (h1 x hx).1.1.1.1.1.1.2,
    fun x hx => ⟨⟨(h1 x hx).1.1.1.1.1.2, (h1 x hx).1.1.1.1.2⟩,
      ⟨(h1 x hx).1.1.1.2, (h1 x hx).1.1.2⟩, ⟨(h1 x hx).1.2, (h1 x hx).2⟩⟩,
    fun p q => ⟨(h2 p (mem_pts p) q (mem_pts q)).1, fun x hx y hy hxy => ?_⟩⟩
  rcases (h2 p (mem_pts p) q (mem_pts q)).2 x hx y hy with h | h
  · exact absurd hxy h
  · exact h

@[expose] def affE (t : Perm (Option (ZMod 7))) (ht : affCheck t = true) :
    Subgroup (Perm (Option (ZMod 7))) where
  carrier := {x | x ∈ affList t}
  one_mem' := List.mem_cons_self
  mul_mem' hx hy := (affList_facts ht).1 _ hx _ hy
  inv_mem' hx := (affList_facts ht).2.1 _ hx

theorem mem_affE {t : Perm (Option (ZMod 7))} {ht : affCheck t = true}
    {x : Perm (Option (ZMod 7))} : x ∈ affE t ht ↔ x ∈ affList t :=
  Iff.rfl

theorem mem_normalizer_of_conj {E : Subgroup (Perm (Option (ZMod 7)))}
    {g : Perm (Option (ZMod 7))} (h1 : ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (h2 : ∀ x ∈ E, g⁻¹ * x * g ∈ E) :
    g ∈ Subgroup.normalizer (E : Set (Perm (Option (ZMod 7)))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have h3 := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h3

theorem affine_case {N : Subgroup (Perm (Option (ZMod 7)))} {t : Perm (Option (ZMod 7))}
    (htA : affCheck t = true) (hshift : shift ∈ N) (ht : t ∈ N)
    (hcl : N ≤ Subgroup.closure {shift, dbl, t}) :
    ∃ E : Subgroup (Perm (Option (ZMod 7))), E ≤ N ∧ (E.subgroupOf N).Normal ∧
      ∀ p q : Option (ZMod 7), ∃! e : E, (e : Perm (Option (ZMod 7))) p = q := by
  have hEN : affE t htA ≤ N := by
    intro x hx
    rw [mem_affE, affList, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨j, -, rfl⟩
    · exact one_mem N
    · exact mul_mem (mul_mem (pow_mem hshift j) ht) (inv_mem (pow_mem hshift j))
  have hconj := (affList_facts htA).2.2.1
  have hnorm :
      N ≤ Subgroup.normalizer ((affE t htA : Subgroup _) : Set (Perm (Option (ZMod 7)))) := by
    refine hcl.trans ((Subgroup.closure_le _).2 ?_)
    rintro g (rfl | rfl | rfl)
    · exact mem_normalizer_of_conj (fun x hx => (hconj x hx).1.1) (fun x hx => (hconj x hx).1.2)
    · exact mem_normalizer_of_conj (fun x hx => (hconj x hx).2.1.1)
        (fun x hx => (hconj x hx).2.1.2)
    · exact mem_normalizer_of_conj (fun x hx => (hconj x hx).2.2.1)
        (fun x hx => (hconj x hx).2.2.2)
  refine ⟨affE t htA, hEN, (Subgroup.normal_subgroupOf_iff_le_normalizer hEN).2 hnorm,
    fun p q => ?_⟩
  obtain ⟨⟨x, hx, hxp⟩, huniq⟩ := (affList_facts htA).2.2.2 p q
  refine ⟨⟨x, hx⟩, hxp, fun y hy => Subtype.ext (huniq y.1 y.2 x hx (by rw [hxp]; exact hy))⟩

@[expose] def mob (a b c d : ZMod 7) : Option (ZMod 7) → Option (ZMod 7)
  | none => if c = 0 then none else some (c ^ 5 * a)
  | some k => if c * k + d = 0 then none else some ((c * k + d) ^ 5 * (a * k + b))

theorem zmod_seven_mul_pow_five : ∀ x : ZMod 7, x ≠ 0 → x * x ^ 5 = 1 := by decide

theorem shift_eq_mob : ∀ z, shift z = mob 1 1 0 1 z := by decide

theorem dbl_eq_mob : ∀ z, dbl z = mob 3 0 0 5 z := by decide

theorem tPro3_eq_mob : ∀ z, tPro3 z = mob 0 2 3 0 z := by decide

theorem tPro5_eq_mob : ∀ z, tPro5 z = mob 0 3 2 0 z := by decide

theorem tPro6_eq_mob : ∀ z, tPro6 z = mob 0 1 6 0 z := by decide

scoped instance fact_prime_seven : Fact (Nat.Prime 7) :=
  ⟨Nat.prime_seven⟩

theorem zmod_seven_inv_eq_pow_five (x : ZMod 7) : x⁻¹ = x ^ 5 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact inv_eq_of_mul_eq_one_right (zmod_seven_mul_pow_five x hx)

@[expose] def projEquiv : Option (ZMod 7) ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7) :=
  OnePoint.equivProjectivization (ZMod 7)

theorem projEquiv_symm_mk (v : Fin 2 → ZMod 7) (hv : v ≠ 0) :
    projEquiv.symm (Projectivization.mk (ZMod 7) v hv) =
      if v 1 = 0 then none else some (v 1 ^ 5 * v 0) := by
  rw [← zmod_seven_inv_eq_pow_five]
  exact OnePoint.equivProjectivization_symm_apply_mk (ZMod 7) v hv

theorem sl_smul_projEquiv (M : SL(2, ZMod 7)) (z : Option (ZMod 7)) :
    M • projEquiv z = projEquiv (mob (M 0 0) (M 0 1) (M 1 0) (M 1 1) z) := by
  apply projEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  cases z with
  | none =>
    change projEquiv.symm (M • (Projectivization.mk _ ![1, 0] _)) = _
    rw [Projectivization.smul_mk, projEquiv_symm_mk]
    simp [Matrix.SpecialLinearGroup.smul_def, mob]
  | some k =>
    change projEquiv.symm (M • (Projectivization.mk _ ![k, 1] _)) = _
    rw [Projectivization.smul_mk, projEquiv_symm_mk]
    simp [Matrix.SpecialLinearGroup.smul_def, mob]

@[expose] def natPSL : Subgroup (Perm (Option (ZMod 7))) :=
  (projEquiv.symm.permCongrHom.toMonoidHom.comp Projectivization.PSLAction.toPermHom).range

theorem mem_natPSL_iff {σ : Perm (Option (ZMod 7))} :
    σ ∈ natPSL ↔ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7),
      ∀ z, projEquiv (σ z) = g • projEquiv z := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g, fun z => ?_⟩
    change projEquiv (projEquiv.symm _) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · rintro ⟨g, hg⟩
    refine ⟨g, Equiv.ext fun z => ?_⟩
    change projEquiv.symm (g • projEquiv.symm.symm z) = σ z
    rw [Equiv.symm_symm, ← hg, Equiv.symm_apply_apply]

theorem mem_natPSL_of_mob {σ : Perm (Option (ZMod 7))} (a b c d : ZMod 7)
    (hdet : a * d - b * c = 1) (h : ∀ z, σ z = mob a b c d z) : σ ∈ natPSL := by
  set M : SL(2, ZMod 7) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine mem_natPSL_iff.2 ⟨M, fun z => ?_⟩
  rw [h]
  exact (sl_smul_projEquiv M z).symm

theorem shift_mem_natPSL : shift ∈ natPSL :=
  mem_natPSL_of_mob 1 1 0 1 (by decide) shift_eq_mob

theorem dbl_mem_natPSL : dbl ∈ natPSL :=
  mem_natPSL_of_mob 3 0 0 5 (by decide) dbl_eq_mob

theorem tPro3_mem_natPSL : tPro3 ∈ natPSL :=
  mem_natPSL_of_mob 0 2 3 0 (by decide) tPro3_eq_mob

theorem tPro5_mem_natPSL : tPro5 ∈ natPSL :=
  mem_natPSL_of_mob 0 3 2 0 (by decide) tPro5_eq_mob

theorem tPro6_mem_natPSL : tPro6 ∈ natPSL :=
  mem_natPSL_of_mob 0 1 6 0 (by decide) tPro6_eq_mob

theorem degreeEight_classification {N : Subgroup (Perm (Option (ZMod 7)))}
    (hshift : shift ∈ N) (hdbl : dbl ∈ N) (hstab : ∀ σ ∈ N, σ none = none → IsAffine σ)
    (hswap : ∃ s ∈ N, s none = some 0 ∧ s (some 0) = none) :
    (∃ E : Subgroup (Perm (Option (ZMod 7))), E ≤ N ∧ (E.subgroupOf N).Normal ∧
      ∀ p q : Option (ZMod 7), ∃! e : E, (e : Perm (Option (ZMod 7))) p = q) ∨
    N ≤ natPSL := by
  obtain ⟨s, hs, hs1, hs2⟩ := hswap
  obtain ⟨t, ht, htt, htinf, ht0⟩ := exists_swap_involution hstab hs hs1 hs2
  have hcl := le_closure hstab hshift ht htinf
  have hpro : t ∈ natPSL → N ≤ natPSL := fun htP => hcl.trans ((Subgroup.closure_le _).2 (by
    rintro g (rfl | rfl | rfl)
    · exact shift_mem_natPSL
    · exact dbl_mem_natPSL
    · exact htP))
  rcases swap_cases hstab hshift hdbl ht htt htinf ht0 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (affine_case affCheck_tAff3 hshift ht hcl)
  · exact Or.inl (affine_case affCheck_tAff5 hshift ht hcl)
  · exfalso
    have hw : tBad * shift * tBad * shift * tBad ∈ N :=
      mul_mem (mul_mem (mul_mem (mul_mem ht hshift) ht) hshift) ht
    exact tBad_word.2 (hstab _ hw tBad_word.1)
  · exact Or.inr (hpro tPro3_mem_natPSL)
  · exact Or.inr (hpro tPro5_mem_natPSL)
  · exact Or.inr (hpro tPro6_mem_natPSL)

end CFSG.SeitzReduction.RankOne.DegreeEight
