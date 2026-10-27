module

public import CFSG.Quasithin.H13.A6S1373
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1514

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem rho_UH_F4 {u : G} (hu : u ∈ conjClosure S.V3 H) :
    ∃ huN : u ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨u, huN⟩ = 1 ∨ S.frame.ρ ⟨u, huN⟩ = swap 4 5 := by
  have huT : u ∈ T := S.UH_le_T_F4 hNS h1356two h13315 hH hu
  have huN : u ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le huT
  have huC : u ∈ Subgroup.centralizer (S.V3 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val
      (hab.1.is_comm.comm ⟨x, le_conjClosure _ _ hx⟩ ⟨u, hu⟩)
  exact ⟨huN, fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨u, huN⟩) huC)⟩

theorem V_le_QH_F4 : V ≤ pCoreOf 2 H := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  rw [hF.le_pCoreOf_iff_le_centralizerMod]
  intro v hv
  refine ⟨hF.V_le_H hv, hF.V_le_normalizer_V₁ hv, fun u hu => ?_⟩
  obtain ⟨huN, hρ⟩ := S.rho_UH_F4 hNS h13315 h1356two hH hab hu
  have h := S.comm_mem_V1_of_rho (u := ⟨u, huN⟩) hρ hv
  have e : v * u * v⁻¹ * u⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  rw [e]
  exact (fsuV1 T V).inv_mem h

theorem conjSub_le_centralizer_UH_F4 {h : G} (hh : h ∈ H) :
    conjSub h V ≤ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hV := hF.le_pCoreOf_iff_le_centralizer.1 (S.V_le_QH_F4 hNS h13315 h1356two hH hab)
  intro w hw
  rw [mem_conjSub] at hw
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : h⁻¹ * u * h⁻¹⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (H.inv_mem hh)) u).mp hu
  have hc := Subgroup.mem_centralizer_iff.mp (hV hw).2 _ hu'
  calc u * w = h * ((h⁻¹ * u * h⁻¹⁻¹) * (h⁻¹ * w * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * w * h) * (h⁻¹ * u * h⁻¹⁻¹)) * h⁻¹ := by rw [hc]
    _ = w * u := by group

theorem conjSub_le_T_F4 {h : G} (hh : h ∈ H) : conjSub h V ≤ T := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  exact (hF.conjSub_le_pCoreOf (S.V_le_QH_F4 hNS h13315 h1356two hH hab) hh).trans
    (pCoreOf_le_of_sylow S.h13.sylow hF.T_le_H)

theorem rho_conjSub_V_F4 {h : G} (hh : h ∈ H) {w : G}
    (hw : w ∈ conjSub h V) :
    ∃ hwN : w ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨w, hwN⟩ = 1 ∨ S.frame.ρ ⟨w, hwN⟩ = swap 4 5 := by
  have hwN : w ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.T_le (S.conjSub_le_T_F4 hNS h13315 h1356two hH hab hh hw)
  have hwC : w ∈ Subgroup.centralizer (S.V3 : Set G) :=
    Subgroup.centralizer_le (le_conjClosure S.V3 H)
      (S.conjSub_le_centralizer_UH_F4 hNS h13315 h1356two hH hab hh hw)
  exact ⟨hwN, fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨w, hwN⟩) hwC)⟩

end Abelian

end Setting4

end CFSG.Quasithin.H13.A6
