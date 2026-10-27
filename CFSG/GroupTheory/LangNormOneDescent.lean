module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

@[expose] def iterateFixedSubgroup (S : G →* G) (m : ℕ) : Subgroup G where
  carrier := {g | (⇑S)^[m] g = g}
  mul_mem' {a b} ha hb := by
    change (⇑S)^[m] (a * b) = a * b
    rw [iterate_map_mul, ha, hb]
  one_mem' := iterate_map_one S m
  inv_mem' {a} ha := by
    change (⇑S)^[m] a⁻¹ = a⁻¹
    rw [iterate_map_inv, ha]

theorem mem_iterateFixedSubgroup {S : G →* G} {m : ℕ} {g : G} :
    g ∈ iterateFixedSubgroup S m ↔ (⇑S)^[m] g = g := Iff.rfl

theorem lang_norm_telescope (S : G →* G) (h : G) (n : ℕ) :
    ((List.range n).map fun i => (⇑S)^[i] (h⁻¹ * S h)).prod = h⁻¹ * (⇑S)^[n] h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply]
    group

theorem exceptional_Lang_norm_one_descent (S : G →* G) {m : ℕ} (hm : 1 ≤ m)
    (hLang : ∀ x : G, ∃ h : G, x = h⁻¹ * S h) (x : G)
    (hnorm : ((List.range m).map fun i => (⇑S)^[i] x).prod = 1) :
    ∃ h : G, ∃ hR : h ∈ iterateFixedSubgroup S m, x = h⁻¹ * S h ∧
      ∃ hx : x ∈ iterateFixedSubgroup S m,
        ∃ SR : iterateFixedSubgroup S m ≃* iterateFixedSubgroup S m,
          (∀ r, (SR r : G) = S r) ∧
          MulAut.conj (⟨h, hR⟩ : iterateFixedSubgroup S m) *
              (MulAut.conj (⟨x, hx⟩ : iterateFixedSubgroup S m) * SR) *
            (MulAut.conj (⟨h, hR⟩ : iterateFixedSubgroup S m))⁻¹ = SR := by
  obtain ⟨h, rfl⟩ := hLang x
  rw [lang_norm_telescope] at hnorm
  have hR : h ∈ iterateFixedSubgroup S m := by
    rw [mem_iterateFixedSubgroup]
    rw [inv_mul_eq_one] at hnorm
    exact hnorm.symm
  have hcomm : ∀ g, (⇑S)^[m] (S g) = S ((⇑S)^[m] g) := fun g => by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  have hSR : ∀ r : iterateFixedSubgroup S m, S r ∈ iterateFixedSubgroup S m := fun r => by
    rw [mem_iterateFixedSubgroup, hcomm, r.2]
  have hx : h⁻¹ * S h ∈ iterateFixedSubgroup S m :=
    mul_mem (inv_mem hR) (hSR ⟨h, hR⟩)
  let f : iterateFixedSubgroup S m →* iterateFixedSubgroup S m :=
    (S.comp (iterateFixedSubgroup S m).subtype).codRestrict _ hSR
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro r s hrs
      have h1 : S r = S s := congrArg Subtype.val hrs
      apply Subtype.ext
      rw [← r.2, ← s.2, Function.iterate_succ_apply, Function.iterate_succ_apply, h1]
    · intro r
      refine ⟨⟨(⇑S)^[k] r, ?_⟩, ?_⟩
      · rw [mem_iterateFixedSubgroup, ← Function.iterate_add_apply, add_comm,
          Function.iterate_add_apply, r.2]
      · apply Subtype.ext
        change S ((⇑S)^[k] r) = r
        rw [← Function.iterate_succ_apply' (⇑S) k r]
        exact r.2
  refine ⟨h, hR, rfl, hx, MulEquiv.ofBijective f hbij, fun r => rfl, ?_⟩
  ext v
  change h * (h⁻¹ * S h * S (h⁻¹ * v * h) * (h⁻¹ * S h)⁻¹) * h⁻¹ = S v
  rw [map_mul, map_mul, map_inv]
  group

end CFSG.GroupTheory
