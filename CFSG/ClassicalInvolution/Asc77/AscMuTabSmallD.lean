module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBigTenU
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallA
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank

namespace MuTab

variable {p f : ℕ} [Fact p.Prime]

theorem smallShape_psl5 : SmallShape p f .PSL 5 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  cases hπ : piSign p f
  · rw [muKind_psl_five_false]
    exact shapeE4_psl5 M hS.hyp hp2 hq hne (pow_mod_four_of_piSign_false hp2 hπ)
  · rw [muKind_psl_five_true]
    exact shapeBig10_psl5 M hS.hyp hp2 hq hne (piSign_true_iff.mp hπ)

theorem smallShape_psu5 : SmallShape p f .PSU 5 := by
  intro hp2 hq X _ _ Φ hS hne htop hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
  cases hπ : piSign p f
  · rw [muKind_psu_five_false]
    exact shapeBig10_psu5 M hS.hyp hp2 hq hne (pow_mod_four_of_piSign_false hp2 hπ)
  · rw [muKind_psu_five_true]
    exact shapeE4_psu5 M hS.hyp hp2 hq hne (piSign_true_iff.mp hπ)

end MuTab

end CFSG.ClassicalInvolution.Asc77
