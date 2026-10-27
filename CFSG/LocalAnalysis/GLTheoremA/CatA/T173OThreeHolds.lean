module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X

section Assembly


theorem i173OOn_famThree_of_modelFactExcThree (hF4 : ModelFactExcThree .F4)
    (hE6 : ModelFactExcThree .E6) (hE7 : ModelFactExcThree .E7)
    (hE8 : ModelFactExcThree .E8) : I173OOn famThree := by
  intro p Ω _ _ S B N D K x lab hcfg hlab hfam hmark
  obtain ⟨htag, hn, hp⟩ := hfam
  subst p
  have hE6n : lab.tag = .E6 → 3 ≠ 3 ∨ lab.n = 1 := fun _ => Or.inr hn
  rcases htag with ⟨htagBC, hrank⟩ | hExc
  · obtain ⟨F, hF, hFin, hcard, hZ, ⟨M⟩⟩ := exists_model_sp hcfg hlab htagBC hrank hmark
    letI : Field F := hF
    letI : Finite F := hFin
    have hcard2 : Nat.card F = 2 := by rw [hcard, hn]; norm_num
    exact concl_of_modelFactO hcfg M hZ (modelFactSpThree F lab.rank hrank hcard2)
  · obtain ⟨τ, F, hF, hFin, hFinAdj, hτlab, hcard, hZ, ⟨M⟩⟩ :=
      exists_model_exc hcfg hlab hExc hE6n hmark
    letI : Field F := hF
    letI : Finite F := hFin
    letI : Finite ↥(adjointGroup τ F) := hFinAdj
    have hcard2 : Nat.card F = 2 := by rw [hcard, hn]; norm_num
    rcases hτlab with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact concl_of_modelFactO hcfg M hZ (hF4 F hcard2)
    · exact concl_of_modelFactO hcfg M hZ (hE6 F hcard2)
    · exact concl_of_modelFactO hcfg M hZ (hE7 F hcard2)
    · exact concl_of_modelFactO hcfg M hZ (hE8 F hcard2)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
