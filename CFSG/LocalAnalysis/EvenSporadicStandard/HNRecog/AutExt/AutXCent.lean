module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCentG

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G}

theorem aut_X_cent (h : F5Std a z) {b t : G} (hb : b ∈ orb2B a z a)
    (ht : t ∈ orb2A a a ∧ (t ∈ orb2A a b ∨ t ∈ orb2B a z b)) {η : G → G}
    (hη : IsIsoOn (Gxy a b) (Gxy a b) η) (hfix : ∀ x ∈ Gxyz a b t, η x = x) :
    (∀ x ∈ Gxy a b, η x = x) ∨ ∀ x ∈ Gxy a b, η x = t * x * t⁻¹ :=
  aut_X_cent_of_facts h.inp.x_cent h.toF5Base hb ht hη hfix

theorem aut_X_cent_iso (h : F5Std a z) {b t : G} (hb : b ∈ orb2B a z a)
    (ht : t ∈ orb2A a a ∧ (t ∈ orb2A a b ∨ t ∈ orb2B a z b)) {K' : Subgroup G'}
    {φ₁ φ₂ : G → G'} (h₁ : IsIsoOn (Gxy a b) K' φ₁) (h₂ : IsIsoOn (Gxy a b) K' φ₂)
    (hS : ∀ x ∈ Gxyz a b t, φ₁ x = φ₂ x) :
    (∀ x ∈ Gxy a b, φ₁ x = φ₂ x) ∨ ∀ x ∈ Gxy a b, φ₁ x = φ₂ (t * x * t⁻¹) :=
  iso_dichotomy_of_aut
    (fun x hx => by
      rw [Gxyz_eq_inf] at hx
      exact (Subgroup.mem_inf.mp hx).1)
    (fun _ hη hfix => aut_X_cent h hb ht hη hfix) h₁ h₂ hS

end CFSG.EvenSporadicStandard.HNRecog.Section4
