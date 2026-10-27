module

public import CFSG.Quasithin.H13.L32NLem14331d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open Ctx
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem rho_a_mem_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4) {e : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (he1 : e ≠ 1)
    (hN : l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨l⁻¹ * e * l, hN⟩ ∈ D.img (l32nH T V) ∧ D.ρ ⟨l⁻¹ * e * l, hN⟩ ≠ 1 := by
  have ha := C.conj_mem_zIl_F4 he
  have haH : l⁻¹ * e * l ∈ l32nH T V := L14332.conj_zU_le_F4 h12813 C.setting C.gP C.gN ha.1
  have ha1 : l⁻¹ * e * l ≠ 1 := fun h => he1 (by
    calc e = l * (l⁻¹ * e * l) * l⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨hN', hρ1, -⟩ := C.rho_eq_of_ne_F4 D h14325 h1222 h12213 h12810 h12813 ha ha1
  exact ⟨L128A.HatU.rho_mem_img D haH hN, hρ1⟩

theorem false_of_case_iii_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4)
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    (hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(l32nH T V)) ≤ 2) {e : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (he1 : e ≠ 1)
    (hiii : Case14323iii T V g D) : False := by
  refine C.false_of_closure_F4 D h14325 h1222 h12813 hQ hm3 he he1 fun hN => ?_
  obtain ⟨hmem, hρ1⟩ := C.rho_a_mem_F4 D h14325 h1222 h12213 h12810 h12813 he he1 hN
  rcases hiii.iso with h | h
  · obtain ⟨φ⟩ := h
    exact closureProp_of_alt hmem hρ1 φ
  · obtain ⟨φ⟩ := h
    exact closureProp_of_perm hmem hρ1 φ

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
