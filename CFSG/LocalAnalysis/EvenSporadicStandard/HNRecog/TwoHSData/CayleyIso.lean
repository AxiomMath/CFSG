module

public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem nonempty_mulEquiv_of_cayley {G T : Type*} [Group G] [Group T] (X : Subgroup G)
    (gS : List G) (gT : List T) (hlen : gS.length = gT.length)
    (hX : X = closure {x | x ∈ gS}) (f : G → T) (h1 : f 1 = 1)
    (hstep : ∀ x ∈ X, ∀ i : Fin gS.length, f (x * gS.get i) = f x * gT.get (Fin.cast hlen i))
    (hinj : Set.InjOn f X) (hsurj : ∀ t : T, ∃ x ∈ X, f x = t) :
    Nonempty (↥X ≃* T) := by
  have hXmem : ∀ {z : G}, z ∈ closure {x | x ∈ gS} → z ∈ X := fun hz => by
    rw [hX]
    exact hz
  have main : ∀ y ∈ X, ∀ x ∈ X, f (x * y) = f x * f y := by
    intro y hy
    rw [hX] at hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        intro x hx
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
        rw [← hi]
        have hf : f (gS.get i) = gT.get (Fin.cast hlen i) := by
          have := hstep 1 X.one_mem i
          simpa [h1] using this
        rw [hstep x hx i, hf]
    | one =>
        intro x hx
        simp [h1]
    | mul a b ha hb iha ihb =>
        intro x hx
        have haX : a ∈ X := hXmem ha
        calc f (x * (a * b)) = f ((x * a) * b) := by rw [mul_assoc]
          _ = f (x * a) * f b := ihb (x * a) (X.mul_mem hx haX)
          _ = (f x * f a) * f b := by rw [iha x hx]
          _ = f x * (f a * f b) := by rw [mul_assoc]
          _ = f x * f (a * b) := by rw [← ihb a haX]
    | inv a ha iha =>
        intro x hx
        have haX : a ∈ X := hXmem ha
        have hxa : x * a⁻¹ ∈ X := X.mul_mem hx (X.inv_mem haX)
        have hxa' : f (x * a⁻¹) = f x * (f a)⁻¹ := by
          have h := iha (x * a⁻¹) hxa
          have h' : f x = f (x * a⁻¹) * f a := by simpa using h
          exact eq_mul_inv_of_mul_eq h'.symm
        have hainv : f (a⁻¹) = (f a)⁻¹ := by
          have h := iha (a⁻¹) (X.inv_mem haX)
          have h' : f (a⁻¹) * f a = 1 := by
            have h'' : f (a⁻¹ * a) = f (a⁻¹) * f a := h
            rw [inv_mul_cancel, h1] at h''
            exact h''.symm
          simpa using eq_mul_inv_of_mul_eq h'
        rw [hxa', hainv]
  let φ : ↥X →* T := MonoidHom.mk' (fun x : ↥X => f x) (fun a b : ↥X => by
    simpa using main (b : G) b.2 (a : G) a.2)
  have hinj' : Function.Injective (fun x : ↥X => f x) := by
    intro a b hab
    apply Subtype.ext
    exact hinj a.2 b.2 hab
  have hsurj' : Function.Surjective (fun x : ↥X => f x) := by
    intro t
    obtain ⟨x, hx, hfx⟩ := hsurj t
    exact ⟨⟨x, hx⟩, hfx⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj', hsurj'⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
