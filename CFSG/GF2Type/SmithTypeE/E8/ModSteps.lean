module

public import CFSG.GF2Type.SmithTypeE.E8.ModAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt)


theorem smithE8E34Q_of (hF : E8ModelFacts) (hM : SmithE8Module) : SmithE8E34Q := by
  intro G _ _ _ S hw hU h b haQ hb hbQ _ hbQa habz
  obtain ⟨φ, h2a, -, h3, -⟩ := hM G S hw hU
  by_cases haz : h * S.z * h⁻¹ = S.z
  · exact hbQa (by rw [S.Qa_eq_QG_of_conj_eq haz]; exact hbQ)
  have hzQa : S.z ∈ S.Qa h := S.z_mem_Qa_of_mem_QG rfl haQ haz
  have haQa : h * S.z * h⁻¹ ∈ S.Qa h := (S.conjBy h).z_mem_QG
  have hbz : b ≠ S.z := fun e => hbQa (e ▸ hzQa)
  have ha1 := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) haQ haz
  have hb1 := h2a b hb hbQ hbz
  have hncol : φ (S.cl b) ∉ collSpace (φ (S.cl (h * S.z * h⁻¹))) := fun hc =>
    hbQa ((h3 h b haQ haz hb hbQ hbz).mpr hc)
  have habne : h * S.z * h⁻¹ * b ≠ S.z := by
    intro e
    apply hbQa
    have hb' : b = (h * S.z * h⁻¹)⁻¹ * S.z := by
      calc b = (h * S.z * h⁻¹)⁻¹ * (h * S.z * h⁻¹ * b) := by group
        _ = (h * S.z * h⁻¹)⁻¹ * S.z := by rw [e]
    rw [hb']
    exact (S.Qa h).mul_mem ((S.Qa h).inv_mem haQa) hzQa
  have hab1 := h2a _ habz (S.QG.mul_mem haQ hbQ) habne
  rw [S.cl_mul haQ hbQ, map_add] at hab1
  exact hF.wt_ne_add _ ha1 _ hb1 hncol hab1

theorem smithE8E24Line_of (hF : E8ModelFacts) (hM : SmithE8Module) : SmithE8E24Line := by
  intro G _ _ _ S hw hU h hbQ hbz
  obtain ⟨φ, h2a, h2b, h3, -⟩ := hM G S hw hU
  have hb1 := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) hbQ hbz
  obtain ⟨w', hw'W, hw'col, hne⟩ := hF.exists_adj _ hb1
  obtain ⟨c, hc, hcQ, hcj⟩ := h2b w' hw'W
  have hcz : c ≠ S.z := by
    rintro rfl
    rw [S.cl_z, map_zero] at hcj
    exact hF.wt_ne_zero w' hw'W hcj.symm
  refine ⟨c, hc, hcQ, (h3 h c hbQ hbz hc hcQ hcz).mpr (by rw [hcj]; exact hw'col), hcz, ?_, ?_⟩
  · intro e
    apply hne
    rw [← hcj, e]
  · intro e
    apply hne
    rw [← hcj, e, S.cl_mul S.z_mem_QG hbQ, S.cl_z, zero_add]

theorem smithE8E24_of (hF : E8ModelFacts) (hM : SmithE8Module) : SmithE8E24 := by
  intro G _ _ _ S hw hU x h hx hxM hxQ hyQ
  obtain ⟨φ, h2a, -, h3, h4⟩ := hM G S hw hU
  by_cases hyz : h * S.z * h⁻¹ = S.z
  · rw [S.Qa_eq_QG_of_conj_eq hyz, hyz]
    have e : x * S.z * x⁻¹ = S.z := by
      rw [S.z_comm hxM]
      group
    rw [e]
    exact S.z_mem_QG
  have hy1 := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) hyQ hyz
  obtain ⟨r, hr, hA⟩ := h4 x hx hxM hxQ
  change Acts S φ x r at hA
  have hc : IsConj S.z (x * (h * S.z * h⁻¹) * x⁻¹) := isConj_iff.mpr ⟨x * h, by group⟩
  have hcz : x * (h * S.z * h⁻¹) * x⁻¹ ≠ S.z := by
    intro e
    apply hyz
    calc h * S.z * h⁻¹ = x⁻¹ * (x * (h * S.z * h⁻¹) * x⁻¹) * x := by group
      _ = x⁻¹ * (S.z * x) := by rw [e, mul_assoc]
      _ = x⁻¹ * (x * S.z) := by rw [S.z_comm hxM]
      _ = S.z := by group
  obtain ⟨-, hrcol⟩ := hF.tv_wt r hr _ hy1
  have hcj : φ (S.cl (x * (h * S.z * h⁻¹) * x⁻¹)) =
      e7Rep56 (ZMod 2) r (φ (S.cl (h * S.z * h⁻¹))) := hA _ hyQ
  exact (h3 h _ hyQ hyz hc (S.conj_mem_QG hxM hyQ) hcz).mpr (by rw [hcj]; exact hrcol)

end CFSG.GF2Type.SmithTypeE.E8
