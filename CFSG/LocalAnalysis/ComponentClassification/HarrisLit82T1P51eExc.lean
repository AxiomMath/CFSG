module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eSpCover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Typed

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem not_pomegaOdd_three_of_excCompTag {τ : StatedLieTag} {n : ℕ}
    (h : Burgoyne.X10.ExcCompTag τ n) : ¬ (τ = .POmegaOdd ∧ n = 3) := by
  rintro ⟨rfl, rfl⟩
  simp [Burgoyne.X10.ExcCompTag] at h

theorem famNoSpin7_of_excFamilyModel (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (h : Burgoyne.X10.ExcFamilyModel t) : FamNoSpin7 t := by
  intro X _ n p f hp hp2 hadm hX g hg L hL
  have : Finite X := (hO X t n p f hadm hX).1
  have : Group.IsPerfect L := hL.1.1
  rcases h X n p f hp hp2 hadm hX (MulAut.conj g) hg L hL with
    ⟨τ', n', f', ht, hadm', hLM⟩ | ⟨-, -, hn, -⟩
  · exact noSpin7_of_lieModel_ne hO hp2 hadm' hLM (not_pomegaOdd_three_of_excCompTag ht)
  · exact absurd (MonoidHom.mem_range.2 ⟨g, rfl⟩) hn

end CFSG.ComponentClassification.HarrisLit.T1.P51e
