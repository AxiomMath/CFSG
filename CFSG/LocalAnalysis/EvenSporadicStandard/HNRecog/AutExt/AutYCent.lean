module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.YCent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G}

theorem aut_Y_cent (h : F5Std a z) {b w t : G} (hb : IsConj a b) (hw : w ∈ orb2BB a z b)
    (ht : t ∈ Gxy b w ∧ t ∈ orb2A a b) {η : G → G}
    (hη : IsIsoOn (Gxy b w) (Gxy b w) η) (hfix : ∀ x ∈ Gxyz b w t, η x = x) :
    (∀ x ∈ Gxy b w, η x = x) ∨ ∀ x ∈ Gxy b w, η x = t * x * t⁻¹ :=
  aut_Y_cent_of_base h.toF5Base hb hw ht hη hfix

theorem aut_Y_cent_iso (h : F5Std a z) {b w t : G} (hb : IsConj a b) (hw : w ∈ orb2BB a z b)
    (ht : t ∈ Gxy b w ∧ t ∈ orb2A a b) {K' : Subgroup G'}
    {φ₁ φ₂ : G → G'} (h₁ : IsIsoOn (Gxy b w) K' φ₁) (h₂ : IsIsoOn (Gxy b w) K' φ₂)
    (hS : ∀ x ∈ Gxyz b w t, φ₁ x = φ₂ x) :
    (∀ x ∈ Gxy b w, φ₁ x = φ₂ x) ∨ ∀ x ∈ Gxy b w, φ₁ x = φ₂ (t * x * t⁻¹) :=
  iso_dichotomy_of_aut
    (fun x hx => by
      rw [Gxyz_eq_inf] at hx
      exact (Subgroup.mem_inf.mp hx).1)
    (fun _ hη hfix => aut_Y_cent h hb hw ht hη hfix) h₁ h₂ hS

end CFSG.EvenSporadicStandard.HNRecog.Section4
