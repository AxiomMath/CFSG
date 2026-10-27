module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddA6Small_of_no_shape {t : StatedLieTag} (h : ∀ n f : ℕ, ¬ A6Shape t n f) :
    OddA6Small t := by
  intro S _ _ n p f hp hp2 hadm hm hp3 hs
  exact absurd hs (h n f)

theorem not_a6Shape_of_ne {t : StatedLieTag} (ht : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧
    t ≠ .POmegaOdd ∧ t ≠ .POmegaMinus) (n f : ℕ) : ¬ A6Shape t n f := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  unfold A6Shape
  rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
  exacts [h1 h, h1 h, h1 h, h2 h, h2 h, h3 h, h3 h, h4 h, h5 h]

theorem oddA6Small_G2 : OddA6Small .G2 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_F4 : OddA6Small .F4 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_E6 : OddA6Small .E6 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_E7 : OddA6Small .E7 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_E8 : OddA6Small .E8 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_twistedE6 : OddA6Small .twistedE6 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_trialityD4 : OddA6Small .trialityD4 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_twistedG2 : OddA6Small .twistedG2 :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))
theorem oddA6Small_POmegaPlus : OddA6Small .POmegaPlus :=
  oddA6Small_of_no_shape (not_a6Shape_of_ne (by decide))

end CFSG.ComponentClassification.CatFC
