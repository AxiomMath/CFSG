module

public import CFSG.ClassicalInvolution.Asc77.AscC25X12
public import CFSG.ClassicalInvolution.Asc77.AscT7U12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace C25X

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_11Typed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
          (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
            ¬ (LayerOrthType p f Ω a 5 true ∨ LayerOrthType p f Ω a 6 (!piSign p f))

end Residual

section Reduction

variable {p f : ℕ} [Fact p.Prime]


theorem c25_11E4_of_typed (h : C25_11Typed p f) : T7U.C25_11E4 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj
  by_contra hz
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx =>
    (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx =>
    (hcent x (Subgroup.mem_sup_right hx)).symm
  have hty := layer_a_typed_proved hyp ha2 ha1 haR haR'
  exact h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj (hty.resolve_left hz)

theorem c25_11_of_typed (h : C25_11Typed p f) : C25_11 p f :=
  T7U.c25_11_of_E4 (c25_11E4_of_typed h)

end Reduction

section Wiring

variable {p f : ℕ} [Fact p.Prime]


theorem thm7A_of_inputs₁₃_typed
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : C25_11Typed p f) (h16 : Even f → T7U.C25_16inv p f) : Thm7A p f :=
  thm7A_of_inputs₁₃_E4 hconn hres h4 hF hgen22 hZ hchain22 hchain23 hcore hbig hpair
    (c25_11E4_of_typed h11) h16

end Wiring

end C25X

end CFSG.ClassicalInvolution.Asc77
