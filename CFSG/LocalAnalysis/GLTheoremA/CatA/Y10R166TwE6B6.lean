module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open CFSG.HardMathSupport.Lang.E6Descent

section Certs


variable {Ω : Type} [Field Ω] [CharP Ω 2]

namespace TwE6B

theorem twE6Block_le_centralizer_pair {Fr : Ω →+* Ω} {ω : Ωˣ} :
    twE6Block Fr ≤ Subgroup.centralizer
      ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro y (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (twE6Block_le_centralizer_eBar (ω := ω) hx)).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (twE6Block_le_centralizer_fBar (ω := ω) hx)).symm

end TwE6B

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
