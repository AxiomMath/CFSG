module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private lemma fzrAux_inv_self {G : Type} [Group G] {a : G} (ha2 : a * a = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right ha2

private lemma fzrAux_mul_mem {G : Type} [Group G] {X : Subgroup G} {a : G}
    (ha2 : a * a = 1) (hax : ∀ x ∈ X, a * x = x * a) {g h : G}
    (hg : ∃ x ∈ X, g = x ∨ g = x * a) (hh : ∃ y ∈ X, h = y ∨ h = y * a) :
    ∃ z ∈ X, g * h = z ∨ g * h = z * a := by
  obtain ⟨x, hx, hgx | hgx⟩ := hg
  · obtain ⟨y, hy, hhy | hhy⟩ := hh
    · exact ⟨x * y, X.mul_mem hx hy, Or.inl (by rw [hgx, hhy])⟩
    · exact ⟨x * y, X.mul_mem hx hy, Or.inr (by rw [hgx, hhy, mul_assoc])⟩
  · obtain ⟨y, hy, hhy | hhy⟩ := hh
    · exact ⟨x * y, X.mul_mem hx hy,
        Or.inr (by rw [hgx, hhy, mul_assoc, hax y hy, ← mul_assoc])⟩
    · refine ⟨x * y, X.mul_mem hx hy, Or.inl ?_⟩
      have h : a * (y * a) = (a * y) * a := (mul_assoc a y a).symm
      rw [hgx, hhy, mul_assoc x a (y * a), h, hax y hy, mul_assoc, ha2, mul_one]

private lemma fzrAux_inv_mem {G : Type} [Group G] {X : Subgroup G} {a : G}
    (ha2 : a * a = 1) (hax : ∀ x ∈ X, a * x = x * a) {g : G}
    (hg : ∃ x ∈ X, g = x ∨ g = x * a) : ∃ z ∈ X, g⁻¹ = z ∨ g⁻¹ = z * a := by
  obtain ⟨x, hx, hgx | hgx⟩ := hg
  · exact ⟨x⁻¹, X.inv_mem hx, Or.inl (by rw [hgx])⟩
  · refine ⟨x⁻¹, X.inv_mem hx, Or.inr ?_⟩
    rw [hgx, mul_inv_rev, fzrAux_inv_self ha2, hax x⁻¹ (X.inv_mem hx)]

private lemma fzrAux_comm {G : Type} [Group G] {X : Subgroup G} {a : G}
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (ha2 : a * a = 1)
    (hax : ∀ x ∈ X, a * x = x * a) {g h : G}
    (hg : ∃ x ∈ X, g = x ∨ g = x * a) (hh : ∃ y ∈ X, h = y ∨ h = y * a) :
    g * h = h * g := by
  obtain ⟨x, hx, hgx | hgx⟩ := hg
  · obtain ⟨y, hy, hhy | hhy⟩ := hh
    · exact (by rw [hgx, hhy]; exact hXc x hx y hy)
    · rw [hgx, hhy]
      calc x * (y * a) = (x * y) * a := by rw [mul_assoc]
        _ = (y * x) * a := by rw [hXc x hx y hy]
        _ = y * (x * a) := by rw [mul_assoc]
        _ = y * (a * x) := by rw [hax x hx]
        _ = (y * a) * x := by rw [← mul_assoc]
  · obtain ⟨y, hy, hhy | hhy⟩ := hh
    · rw [hgx, hhy]
      calc (x * a) * y = x * (a * y) := by rw [mul_assoc]
        _ = x * (y * a) := by rw [hax y hy]
        _ = (x * y) * a := by rw [← mul_assoc]
        _ = (y * x) * a := by rw [hXc x hx y hy]
        _ = y * (x * a) := by rw [← mul_assoc]
    · rw [hgx, hhy]
      have h1 : (x * a) * (y * a) = x * y := by
        have h : a * (y * a) = (a * y) * a := (mul_assoc a y a).symm
        rw [mul_assoc x a (y * a), h, hax y hy, mul_assoc, ha2, mul_one]
      have h2 : (y * a) * (x * a) = y * x := by
        have h : a * (x * a) = (a * x) * a := (mul_assoc a x a).symm
        rw [mul_assoc y a (x * a), h, hax x hx, mul_assoc, ha2, mul_one]
      rw [h1, h2, hXc x hx y hy]

private lemma fzrAux_sq {G : Type} [Group G] {X : Subgroup G} {a : G}
    (hXsq : ∀ x ∈ X, x * x = 1) (ha2 : a * a = 1) (hax : ∀ x ∈ X, a * x = x * a)
    {g : G} (hg : ∃ x ∈ X, g = x ∨ g = x * a) : g * g = 1 := by
  obtain ⟨x, hx, hgx | hgx⟩ := hg
  · rw [hgx, hXsq x hx]
  · have h : a * (x * a) = (a * x) * a := (mul_assoc a x a).symm
    rw [hgx, mul_assoc x a (x * a), h, hax x hx, mul_assoc, ha2, mul_one, hXsq x hx]

private lemma fzrAux_card {G : Type} [Group G] {X : Subgroup G} {a : G} (haX : a ∉ X)
    (E : Subgroup G) (hmem : ∀ g : G, g ∈ E ↔ ∃ x ∈ X, g = x ∨ g = x * a) :
    Nat.card E = Nat.card X * 2 := by
  let f : X × Bool → E := fun p =>
    match p.2 with
    | false => ⟨p.1, (hmem _).mpr ⟨p.1, p.1.2, Or.inl rfl⟩⟩
    | true => ⟨p.1 * a, (hmem _).mpr ⟨p.1, p.1.2, Or.inr rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, b⟩ ⟨y, c⟩ h
      have hval : ((f (x, b) : E) : G) = ((f (y, c) : E) : G) :=
        congrArg (fun z : E => (z : G)) h
      cases b <;> cases c
      · have hxy : x = y := Subtype.ext (by simpa [f] using hval)
        rw [hxy]
      · have hxy : (x : G) = (y : G) * a := by simpa [f] using hval
        have haX' : a ∈ X := by
          have hay : a = (y : G)⁻¹ * x := by rw [hxy, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [hay]
          exact X.mul_mem (X.inv_mem y.2) x.2
        exact absurd haX' haX
      · have hxy : (x : G) * a = (y : G) := by simpa [f] using hval
        have haX' : a ∈ X := by
          have hay : a = (x : G)⁻¹ * y := by rw [← hxy, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [hay]
          exact X.mul_mem (X.inv_mem x.2) y.2
        exact absurd haX' haX
      · have hxy : (x : G) * a = (y : G) * a := by simpa [f] using hval
        have hxy' : x = y := Subtype.ext (mul_right_cancel hxy)
        rw [hxy']
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx, h | h⟩ := (hmem g).mp hg
      · exact ⟨(⟨x, hx⟩, false), Subtype.ext (by simpa [f] using h.symm)⟩
      · exact ⟨(⟨x, hx⟩, true), Subtype.ext (by simpa [f] using h.symm)⟩
  have hb : Nat.card Bool = 2 := by simp
  calc Nat.card E = Nat.card (X × Bool) := (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card X * 2 := by rw [Nat.card_prod, hb]

theorem fzr_E32 {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x * x = 1)
    (hX16 : Nat.card X = 16) {a : G} (ha2 : a * a = 1) (hax : ∀ x ∈ X, a * x = x * a)
    (haX : a ∉ X) :
    ∃ E : Subgroup G, X ≤ E ∧ a ∈ E ∧ (∀ g ∈ E, ∃ x ∈ X, g = x ∨ g = x * a) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 32 := by
  classical
  let E : Subgroup G :=
    { carrier := {g | ∃ x ∈ X, g = x ∨ g = x * a}
      one_mem' := ⟨1, X.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro p q hp hq
        exact fzrAux_mul_mem ha2 hax hp hq
      inv_mem' := by
        rintro p hp
        exact fzrAux_inv_mem ha2 hax hp }
  have hmem : ∀ g : G, g ∈ E ↔ ∃ x ∈ X, g = x ∨ g = x * a := fun g => Iff.rfl
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hx, Or.inl rfl⟩
  · exact ⟨1, X.one_mem, Or.inr (one_mul a).symm⟩
  · intro g hg
    exact (hmem g).mp hg
  · intro g hg h hh
    exact fzrAux_comm hXc ha2 hax ((hmem g).mp hg) ((hmem h).mp hh)
  · intro g hg
    exact fzrAux_sq hXsq ha2 hax ((hmem g).mp hg)
  · rw [fzrAux_card haX E hmem, hX16]

end CFSG.OddStandard.SmallF3.FritzII
