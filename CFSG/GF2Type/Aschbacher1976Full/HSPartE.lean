module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartEF
public import CFSG.GF2Type.Aschbacher1976Full.HSPartEW

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG.GF2Type.Aschbacher1976Full.HS.PartE

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem hsTwo_of_hsV (hset : HSSetting G z) (hs5 : HSS5 z) (hV : HSV z T V) :
    CFSG.Quasithin.HSType.HSTwo z V where
  le := by
    rw [show Subgroup.centralizer ({z} : Set G) = Hz z from rfl, quasithinGenFitting_Hz]
    exact hV.le_F
  fstar := by
    rw [quasithinGenFitting_normalizer_eq hset hV, centralizer_eq_WT hset hs5 hV]
    exact isZ4Cube_WT hset hV
  quot := by
    obtain ⟨θ, hθs, hθk⟩ := hsAut_exists_SL gl3Stmt_holds hset hV
    refine ⟨θ, hθs, ?_⟩
    rw [quasithinGenFitting_normalizer_eq hset hV]
    exact hθk

theorem hsPartE_holds : HSPartE := by
  intro G _ _ z hset hti hwide hs5
  obtain ⟨T, hTH, hE, hW⟩ := hwide
  have hV := hsV_of_wide hset hti T hTH hE hW
  exact ⟨z, ET (T : Subgroup G) z, hset.1.2.2.1, hV.isElem, hV.card_eq,
    hs1Stmt_holds hset hs5, hsTwo_of_hsV hset hs5 hV⟩

end CFSG.GF2Type.Aschbacher1976Full.HS
