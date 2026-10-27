module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21DS
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.QuasithinUnique.Out21

open DS

section Transport

variable {P P' : Type*} [Group P] [Group P']

theorem dsData_map_equiv (e : P ≃* P') {R : Subgroup P} (h : DSData R) :
    DSData (R.map e.toMonoidHom) where
  two := h.two.of_equiv e
  cyclic := by
    have := h.cyclic
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective)).mp this
  index_two := (Subgroup.index_map_equiv R e).trans h.index_two
  four_le := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact h.four_le
  cent := by
    intro g hg r hr hgr
    obtain ⟨r0, hr0, rfl⟩ := Subgroup.mem_map.mp hr
    have hg' : e.symm g ∉ R := by
      intro hmem
      exact hg (Subgroup.mem_map.mpr ⟨e.symm g, hmem, by simp⟩)
    have hc : e.symm g * r0 = r0 * e.symm g := by
      apply e.injective
      simpa using hgr
    have := h.cent (e.symm g) hg' r0 hr0 hc
    show e r0 * e r0 = 1
    rw [← map_mul, this, map_one]

theorem hasDS_of_mulEquiv (e : P ≃* P') (h : ∃ R : Subgroup P, DSData R) :
    ∃ R' : Subgroup P', DSData R' := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R.map e.toMonoidHom, dsData_map_equiv e hR⟩

end Transport

section Cyclic

theorem not_isCyclic_of_klein {X : Type*} [Group X] [Finite X] {a b : X} (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (ha2 : a * a = 1) (hb2 : b * b = 1) : ¬ IsCyclic X := by
  intro hc
  classical
  have := Fintype.ofFinite X
  have hle := IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset X) ⊆ Finset.univ.filter fun x : X => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact ha2
    · rw [pow_two]; exact hb2
  have h3 : ({1, a, b} : Finset X).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have := Finset.card_le_card hsub
  omega

end Cyclic

section Dihedral

open DihedralGroup

@[expose] def rotSub (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {x | ∃ j, x = r j}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by simp⟩

theorem mem_rotSub_iff {n : ℕ} {x : DihedralGroup n} : x ∈ rotSub n ↔ ∃ j, x = r j := Iff.rfl

theorem sr_not_mem_rotSub {n : ℕ} (i : ZMod n) : sr i ∉ rotSub n := by
  rintro ⟨j, h⟩
  cases h

theorem r_mem_rotSub {n : ℕ} (i : ZMod n) : r i ∈ rotSub n := ⟨i, rfl⟩

theorem mul_mem_rotSub_of_not_mem {n : ℕ} {x y : DihedralGroup n} (hx : x ∉ rotSub n)
    (hy : y ∉ rotSub n) : x * y ∈ rotSub n := by
  rcases x with i | i
  · exact absurd (r_mem_rotSub i) hx
  rcases y with j | j
  · exact absurd (r_mem_rotSub j) hy
  exact ⟨j - i, by simp⟩

theorem mul_not_mem_rotSub_of_mem_of_not_mem {n : ℕ} {x y : DihedralGroup n} (hx : x ∈ rotSub n)
    (hy : y ∉ rotSub n) : x * y ∉ rotSub n := by
  obtain ⟨i, rfl⟩ := hx
  rcases y with j | j
  · exact absurd (r_mem_rotSub j) hy
  · simpa using sr_not_mem_rotSub (n := n) (j - i)

theorem isCyclic_rotSub (n : ℕ) : IsCyclic ↥(rotSub n) := by
  let f : Multiplicative (ZMod n) →* ↥(rotSub n) :=
    { toFun := fun a => ⟨r (Multiplicative.toAdd a), r_mem_rotSub _⟩
      map_one' := by
        apply Subtype.ext
        show r (Multiplicative.toAdd (1 : Multiplicative (ZMod n))) = 1
        rw [toAdd_one]
        exact r_zero
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  refine isCyclic_of_surjective f ?_
  rintro ⟨_, j, rfl⟩
  exact ⟨Multiplicative.ofAdd j, by simp [f]⟩

theorem sq_eq_one_of_commute {n : ℕ} {x y : DihedralGroup n} (hx : x ∉ rotSub n)
    (hy : y ∈ rotSub n) (h : x * y = y * x) : y * y = 1 := by
  obtain ⟨j, rfl⟩ := hy
  rcases x with i | i
  · exact absurd (r_mem_rotSub i) hx
  · have h1 : sr (i + j) = sr (i - j) := by simpa using h
    have h2 : i + j = i - j := sr.inj h1
    have h3 : j + j = 0 := by
      have : j + j = (i + j) - (i - j) := by ring
      rw [this, h2, sub_self]
    rw [r_mul_r, h3, r_zero]

theorem hasDS_of_injective_dihedral {P : Type*} [Group P] [Finite P] {m : ℕ}
    (f : P →* DihedralGroup (2 ^ m)) (hf : Function.Injective f) (h8 : 8 ≤ Nat.card P)
    (hnc : ¬ IsCyclic P) : ∃ R : Subgroup P, DSData R := by
  set R : Subgroup P := (rotSub (2 ^ m)).comap f with hR
  have hmemR : ∀ x : P, x ∈ R ↔ f x ∈ rotSub (2 ^ m) := fun x => Iff.rfl
  have hD2 : IsPGroup 2 (DihedralGroup (2 ^ m)) :=
    IsPGroup.of_card (n := m + 1) (by rw [DihedralGroup.nat_card, pow_succ]; ring)
  have hout : ∃ g : P, g ∉ R := by
    by_contra hall
    push Not at hall
    apply hnc
    let g : P →* ↥(rotSub (2 ^ m)) := f.codRestrict (rotSub (2 ^ m)) fun x => (hmemR x).mp (hall x)
    have := isCyclic_rotSub (2 ^ m)
    exact isCyclic_of_injective g fun a b h => hf (congrArg Subtype.val h)
  obtain ⟨g₀, hg₀⟩ := hout
  have hidx : R.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨g₀, fun b => ?_⟩
    by_cases hb : b ∈ R
    · right
      refine ⟨hb, ?_⟩
      intro hbg
      exact mul_not_mem_rotSub_of_mem_of_not_mem ((hmemR b).mp hb) (fun h => hg₀ ((hmemR g₀).mpr h))
        (by rw [← map_mul]; exact (hmemR _).mp hbg)
    · left
      refine ⟨?_, hb⟩
      rw [hmemR, map_mul]
      exact mul_mem_rotSub_of_not_mem (fun h => hb ((hmemR b).mpr h))
        (fun h => hg₀ ((hmemR g₀).mpr h))
  refine ⟨R, ?_, ?_, hidx, ?_, ?_⟩
  · exact hD2.of_injective f hf
  · let g : ↥R →* ↥(rotSub (2 ^ m)) :=
      (f.comp R.subtype).codRestrict (rotSub (2 ^ m)) fun x => (hmemR x).mp x.2
    have := isCyclic_rotSub (2 ^ m)
    exact isCyclic_of_injective g fun a b h => Subtype.ext (hf (congrArg Subtype.val h))
  · have h1 := Subgroup.card_mul_index R
    rw [hidx] at h1
    omega
  · intro g hg r hr hgr
    apply hf
    rw [map_mul, map_one]
    refine sq_eq_one_of_commute (x := f g) (fun h => hg ((hmemR g).mpr h)) ((hmemR r).mp hr) ?_
    rw [← map_mul, ← map_mul, hgr]

end Dihedral

end CFSG.QuasithinUnique.Out21
