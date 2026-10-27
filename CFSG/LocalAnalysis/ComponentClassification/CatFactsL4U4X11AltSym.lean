module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11AltOrd

public section

namespace CFSG.ComponentClassification.GSThmB.X11.Sym

open Equiv Subgroup

variable {α : Type} {β : Perm α}

theorem apply_comm {c : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α))) (x : α) :
    c (β x) = β (c x) := by
  have h := congrArg (fun f : Perm α => f x) (mem_centralizer_singleton_iff.mp hc)
  simpa [Perm.mul_apply] using h

theorem fix_iff {c : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α))) (x : α) :
    β (c x) = c x ↔ β x = x := by
  rw [← apply_comm hc]
  exact c.injective.eq_iff

@[expose] def rho1 (β : Perm α) : ↥(centralizer ({β} : Set (Perm α))) →* Perm {x // β x = x} where
  toFun c := (c : Perm α).subtypePerm (fix_iff c.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ofSubtype_mem [DecidableEq α] (π : Perm {x // β x = x}) :
    (Perm.ofSubtype π : Perm α) ∈ centralizer ({β} : Set (Perm α)) := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : β x = x
  · rw [hx, Perm.ofSubtype_apply_of_mem π hx]
    exact ((π ⟨x, hx⟩).2).symm
  · have hbx : β (β x) ≠ β x := fun h => hx (β.injective h)
    rw [Perm.ofSubtype_apply_of_not_mem π hx, Perm.ofSubtype_apply_of_not_mem π hbx]

theorem rho1_surjective [DecidableEq α] : Function.Surjective (rho1 β) := fun π =>
  ⟨⟨Perm.ofSubtype π, ofSubtype_mem π⟩, Equiv.ext fun x =>
    Subtype.ext (Perm.ofSubtype_apply_coe π x)⟩

variable [LinearOrder α] (hβ : ∀ x, β (β x) = x)
include hβ

abbrev lo (β : Perm α) (x : α) : α := min x (β x)

omit hβ in
theorem lo_beta (h2 : ∀ x, β (β x) = x) (x : α) : lo β (β x) = lo β x := by
  rw [lo, lo, h2, min_comm]

theorem lo_lt {x : α} (hx : β x ≠ x) : lo β x < β (lo β x) := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [lo, min_eq_right h.le, hβ]
    exact h
  · rw [lo, min_eq_left h.le]
    exact h

omit hβ in
theorem lo_eq {x : α} (hx : x < β x) : lo β x = x := min_eq_left hx.le

omit hβ in
theorem lo_mem (x : α) : lo β x = x ∨ lo β x = β x := min_choice x (β x)

theorem lo_comm_lo {c : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α))) (y : α) :
    lo β (c (lo β y)) = lo β (c y) := by
  rcases lo_mem (β := β) y with h | h <;> rw [h]
  rw [apply_comm hc, lo_beta hβ]

theorem eq_or_eq_of_lo {a b : α} (h : lo β a = lo β b) : a = b ∨ a = β b := by
  rcases lo_mem (β := β) a with ha | ha <;> rcases lo_mem (β := β) b with hb | hb
  · exact Or.inl (ha.symm.trans (h.trans hb))
  · exact Or.inr (ha.symm.trans (h.trans hb))
  · right
    have := ha.symm.trans (h.trans hb)
    rw [← this, hβ]
  · left
    have := ha.symm.trans (h.trans hb)
    exact β.injective this

@[expose] def pairFun {c : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α)))
    (p : {x // x < β x}) : {x // x < β x} :=
  ⟨lo β (c p), lo_lt hβ (fun h => (ne_of_lt p.2).symm ((fix_iff hc p).mp h))⟩

theorem pairFun_comp {c d : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α)))
    (hd : d ∈ centralizer ({β} : Set (Perm α))) (p : {x // x < β x}) :
    pairFun hβ hc (pairFun hβ hd p) = pairFun hβ (mul_mem hc hd) p :=
  Subtype.ext (lo_comm_lo hβ hc (d p))

theorem pairFun_one (p : {x // x < β x}) :
    pairFun hβ (one_mem (centralizer ({β} : Set (Perm α)))) p = p :=
  Subtype.ext (lo_eq p.2)

theorem pairFun_congr {c d : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α)))
    (hd : d ∈ centralizer ({β} : Set (Perm α))) (h : c = d) (p : {x // x < β x}) :
    pairFun hβ hc p = pairFun hβ hd p := by
  subst h
  rfl

@[expose] def rho2 : ↥(centralizer ({β} : Set (Perm α))) →* Perm {x // x < β x} where
  toFun c := {
    toFun := pairFun hβ c.2
    invFun := pairFun hβ (inv_mem c.2)
    left_inv := fun p => by
      rw [pairFun_comp, pairFun_congr hβ _ (one_mem _) (inv_mul_cancel (c : Perm α)),
        pairFun_one]
    right_inv := fun p => by
      rw [pairFun_comp, pairFun_congr hβ _ (one_mem _) (mul_inv_cancel (c : Perm α)),
        pairFun_one] }
  map_one' := Equiv.ext fun p => pairFun_one hβ p
  map_mul' c d := Equiv.ext fun p => (pairFun_comp hβ c.2 d.2 p).symm

theorem rho2_apply (c : ↥(centralizer ({β} : Set (Perm α)))) (p : {x // x < β x}) :
    ((rho2 hβ c p : {x // x < β x}) : α) = lo β ((c : Perm α) p) := rfl

theorem apply_eq_or_of_mem_ker {c : ↥(centralizer ({β} : Set (Perm α)))}
    (h1 : rho1 β c = 1) (h2 : rho2 hβ c = 1) (x : α) :
    (c : Perm α) x = x ∨ (c : Perm α) x = β x := by
  by_cases hx : β x = x
  · left
    have := congrArg (fun π : Perm {x // β x = x} => ((π ⟨x, hx⟩ : {x // β x = x}) : α)) h1
    exact this
  · have hl := congrArg (fun π : Perm {x // x < β x} =>
      ((π ⟨lo β x, lo_lt hβ hx⟩ : {x // x < β x}) : α)) h2
    simp only [rho2_apply, Perm.one_apply] at hl
    rw [lo_comm_lo hβ c.2] at hl
    exact eq_or_eq_of_lo hβ hl

omit [LinearOrder α] hβ in
theorem commute_of_orbitwise {c d : Perm α} (hc : c ∈ centralizer ({β} : Set (Perm α)))
    (hd : d ∈ centralizer ({β} : Set (Perm α))) (hc' : ∀ x, c x = x ∨ c x = β x)
    (hd' : ∀ x, d x = x ∨ d x = β x) : c * d = d * c := by
  ext x
  simp only [Perm.mul_apply]
  rcases hd' x with h1 | h1 <;> rcases hc' x with h2 | h2
  · rw [h1, h2, h1]
  · rw [h1, h2, apply_comm hd, h1]
  · rw [h1, apply_comm hc, h2, h1]
  · rw [h1, apply_comm hc, h2, apply_comm hd, h1]

theorem beta_lt_of_not_lt {x : α} (hx : β x ≠ x) (h : ¬ x < β x) : β x < β (β x) := by
  rw [hβ]
  exact lt_of_le_of_ne (not_lt.mp h) hx

@[expose] noncomputable def liftFun (π : Perm {x // x < β x}) (x : α) : α :=
  if hx : β x = x then x
  else if h : x < β x then (π ⟨x, h⟩ : α) else β (π ⟨β x, beta_lt_of_not_lt hβ hx h⟩ : α)

theorem liftFun_fix (π : Perm {x // x < β x}) {x : α} (hx : β x = x) :
    liftFun hβ π x = x := by
  simp [liftFun, hx]

theorem liftFun_lt (π : Perm {x // x < β x}) {x : α} (hx : x < β x) :
    liftFun hβ π x = (π ⟨x, hx⟩ : α) := by
  simp [liftFun, (ne_of_lt hx).symm, hx]

theorem liftFun_gt (π : Perm {x // x < β x}) {x : α} (hx : β x < x) :
    liftFun hβ π x = β (π ⟨β x, by rw [hβ]; exact hx⟩ : α) := by
  simp [liftFun, ne_of_lt hx, not_lt.mpr hx.le]

theorem liftFun_beta (π : Perm {x // x < β x}) (x : α) :
    liftFun hβ π (β x) = β (liftFun hβ π x) := by
  by_cases hx : β x = x
  · rw [hx, liftFun_fix hβ π hx, hx]
  · rcases lt_or_gt_of_ne (Ne.symm hx) with h | h
    · rw [liftFun_gt hβ π (by rw [hβ]; exact h), liftFun_lt hβ π h]
      congr 3
      exact Subtype.ext (hβ x)
    · rw [liftFun_lt hβ π (by rw [hβ]; exact h), liftFun_gt hβ π h]
      exact (hβ _).symm

theorem liftFun_inv (π : Perm {x // x < β x}) (x : α) :
    liftFun hβ π⁻¹ (liftFun hβ π x) = x := by
  by_cases hx : β x = x
  · rw [liftFun_fix hβ π hx, liftFun_fix hβ _ hx]
  · rcases lt_or_gt_of_ne (Ne.symm hx) with h | h
    · rw [liftFun_lt hβ π h, liftFun_lt hβ _ (π ⟨x, h⟩).2]
      simp
    · rw [liftFun_gt hβ π h, liftFun_beta hβ, liftFun_lt hβ _ (π ⟨β x, _⟩).2]
      simp [hβ]

@[expose] noncomputable def lift (π : Perm {x // x < β x}) : Perm α where
  toFun := liftFun hβ π
  invFun := liftFun hβ π⁻¹
  left_inv := liftFun_inv hβ π
  right_inv x := by
    have := liftFun_inv hβ π⁻¹ x
    rwa [inv_inv] at this

theorem lift_mem (π : Perm {x // x < β x}) :
    lift hβ π ∈ centralizer ({β} : Set (Perm α)) := by
  rw [mem_centralizer_singleton_iff]
  ext x
  exact liftFun_beta hβ π x

theorem rho2_surjective : Function.Surjective (rho2 hβ) := fun π =>
  ⟨⟨lift hβ π, lift_mem hβ π⟩, Equiv.ext fun p => Subtype.ext (by
    rw [rho2_apply]
    show lo β (liftFun hβ π p) = _
    rw [liftFun_lt hβ π p.2]
    exact lo_eq (π p).2)⟩

end CFSG.ComponentClassification.GSThmB.X11.Sym
