module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Struct

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

theorem n24_dg_mem_MS (A : GL (Fin 3) (ZMod 2)) : dg A ∈ MS :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨A, rfl⟩)

theorem n24_z0_mem_MS : z₀ ∈ MS :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀))

theorem n24_dg_mem_MG (A : GL (Fin 3) (ZMod 2)) : dg A ∈ MG :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨A, rfl⟩)

theorem n24_z0_mem_MG : z₀ ∈ MG :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀))

theorem n24_cGL_mem_MS : cGL ∈ MS := by
  let A0 : GL (Fin 3) (ZMod 2) :=
    ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩
  let A1 : GL (Fin 3) (ZMod 2) :=
    ⟨!![1, 1, 0; 0, 1, 0; 0, 1, 1], !![1, 1, 0; 0, 1, 0; 0, 1, 1], by decide, by decide⟩
  have e : cGL = (dg A0 * z₀) * gS * (dg A1 * z₀) * gS * dg A0 := by
    refine Units.ext ?_
    decide
  rw [e]
  have hS : gS ∈ MS := Subgroup.mem_sup_right (Subgroup.mem_zpowers gS)
  exact MS.mul_mem (MS.mul_mem (MS.mul_mem (MS.mul_mem (MS.mul_mem (n24_dg_mem_MS A0)
    n24_z0_mem_MS) hS) (MS.mul_mem (n24_dg_mem_MS A1) n24_z0_mem_MS)) hS) (n24_dg_mem_MS A0)

theorem n24_cGL_mem_MG : cGL ∈ MG := by
  let A0 : GL (Fin 3) (ZMod 2) :=
    ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩
  let A1 : GL (Fin 3) (ZMod 2) :=
    ⟨!![1, 0, 0; 1, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 1, 1, 0], by decide, by decide⟩
  let A2 : GL (Fin 3) (ZMod 2) :=
    ⟨!![1, 1, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 1; 0, 0, 1; 0, 1, 0], by decide, by decide⟩
  let A3 : GL (Fin 3) (ZMod 2) :=
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩
  have e : cGL = dg A0 * gG * (dg A1 * z₀) * gG * (dg A2 * z₀) * gG * (dg A3 * z₀) := by
    refine Units.ext ?_
    decide
  rw [e]
  have hG : gG ∈ MG := Subgroup.mem_sup_right (Subgroup.mem_zpowers gG)
  exact MG.mul_mem (MG.mul_mem (MG.mul_mem (MG.mul_mem (MG.mul_mem (MG.mul_mem
    (n24_dg_mem_MG A0) hG) (MG.mul_mem (n24_dg_mem_MG A1) n24_z0_mem_MG)) hG)
    (MG.mul_mem (n24_dg_mem_MG A2) n24_z0_mem_MG)) hG)
    (MG.mul_mem (n24_dg_mem_MG A3) n24_z0_mem_MG)

end CFSG.OddStandard.HigherRank.YamadaG23
