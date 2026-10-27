module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15

section Odd

variable {S H P : Type} [Group S] [Group H] [Group P]

theorem eq_one_of_odd_of_autSq [Group.IsPerfect S] (ψ : S →* H)
    (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) {R R' : Subgroup S}
    (hsq : ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
      φ * φ = 1)
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * innerHom ψ r = innerHom ψ r * v)
    (hodd : Odd (orderOf v)) : v = 1 := by
  have hfix : ∀ r : S, v * innerHom ψ r = innerHom ψ r * v →
      outerAction ψ hψ π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hψ π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have h1 : outerAction ψ hψ π hπ hπk v * outerAction ψ hψ π hπ hπk v = 1 :=
    hsq _ (fun r hr => hfix r (hvR r hr)) (fun r hr => hfix r (hvR' r hr))
  have h2 : v * v = 1 := by
    apply eq_one_of_outerAction_eq_one ψ hψ π hπ hπk
    rw [map_mul, h1]
  have h3 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

end Odd

end CFSG.ClassicalInvolution.Q3.Q3OCL
