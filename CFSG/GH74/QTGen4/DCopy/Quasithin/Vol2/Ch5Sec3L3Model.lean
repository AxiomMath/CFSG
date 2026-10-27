module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3Model
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.H13.F431.L3 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

section Transport

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2]

namespace L3Model

theorem pCoreOf_inf_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    pCoreOf 2 (sec53G1 M L H B ⊓ sec53G2 M L H D) = sec53S T L := by
  obtain ⟨-, ⟨e1, e2, -, hST, -, hO2⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [sec53G1, sec53G2, e1, e2, ← hO2, hST]

omit [Finite F] in

theorem mem_S_iff_F4 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (x : ↥(sec53G1 M L H B ⊓ sec53G2 M L H D)) :
    (x : G) ∈ sec53S T L ↔
      ((isoφ12 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
        Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) : projectiveSL 3 F) ∈
        projUnitriangular 3 F := by
  rw [← pCoreOf_inf_F4 h527 hyp, mem_pCoreOf_iff_of_equiv (isoφ12 Mo.iso) x,
    pCoreOf_normalizer_inf Mo.data]

end L3Model

end Transport

end CFSG.Quasithin.H13.Sec53L3
