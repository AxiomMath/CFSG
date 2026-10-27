module

public import CFSG.Quasithin.H13.A5Z1367a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem pCoreOf_Gv_le_centralizer_Uv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) ≤ Subgroup.centralizer (S.Uv : Set G) := by
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  obtain ⟨hUc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv
  rw [Subgroup.le_centralizer_iff]
  exact hUc.trans inf_le_right

theorem Tv_le_normalizer_of_autOn_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple ↥(autOn K S.Uv))
    (hT : autOn S.Tv S.Uv ≤
      Subgroup.normalizer ((autOn K S.Uv : Subgroup (MulAut ↥S.Uv)) : Set (MulAut ↥S.Uv))) :
    S.Tv ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hO2 := S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := le_of_mem_cComp hK
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) := hKG.trans S.Gv_le_normalizer_Uv
  intro t ht
  have htG : t ∈ Subgroup.centralizer ({S.v12} : Set G) := S.Tv_le_Gv ht
  have htU : t ∈ Subgroup.normalizer (S.Uv : Set G) := S.Gv_le_normalizer_Uv htG
  set K' : Subgroup G := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : K' ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) := by
    have h := cComp_map_mulEquiv (MulAut.conj t) hK
    have hGv : (Subgroup.centralizer ({S.v12} : Set G)).map (MulAut.conj t).toMonoidHom =
        Subgroup.centralizer ({S.v12} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htG)
    rwa [hGv] at h
  have hK'U : K' ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (le_of_mem_cComp hK'c).trans S.Gv_le_normalizer_Uv
  have hstar : autOn K' S.Uv = autOn K S.Uv := by
    rw [hK', autOn_map_conj hKU ⟨t, htU⟩]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hT (Setup.mem_autOn_iff.2 ⟨⟨t, htU⟩, ht, rfl⟩))
  by_contra hne
  have hne' : K ≠ K' := fun h => hne (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  obtain ⟨h1, h2⟩ := Vol2Native.lemma_1_2_1_two hloc h37 hO2 hK hK'c hne'
  have hcomm : ⁅K, K'⁆ ≤ Subgroup.centralizer (S.Uv : Set G) :=
    (h1.trans h2).trans (S.pCoreOf_Gv_le_centralizer_Uv_F4 h1222 h517 hF)
  have hbot : ⁅autOn K S.Uv, autOn K S.Uv⁆ = ⊥ := by
    conv_lhs => rhs; rw [← hstar]
    rw [← autOn_commutator hKU hK'U]
    exact autOn_eq_bot_of_le_centralizer hcomm
  rw [S153L.comp_perfect_of_isQuasisimple hq] at hbot
  exact SBc3.ne_bot_of_isQuasisimple hq hbot

end Setting

end CFSG.Quasithin.H13.A5
