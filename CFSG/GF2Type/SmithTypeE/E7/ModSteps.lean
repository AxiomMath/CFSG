module

public import CFSG.GF2Type.SmithTypeE.E7.ModAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.LargeExtraspecial
open CFSG.SmithD6 (wt adjW)
open CFSG.GF2Type.SmithTypeE.DMod (code32)

theorem smithE7E34Q_of (hF : E7ModelFacts) (hM : SmithE7Module) : SmithE7E34Q := by
  intro G _ _ _ S hw hU h b haQ hb hbQ _ hbQa habz
  obtain ⟨φ, h2a, -, h3, -⟩ := hM G S hw hU
  by_cases haz : h * S.z * h⁻¹ = S.z
  · exact hbQa (by rw [S.Qa_eq_QG_of_conj_eq haz]; exact hbQ)
  have hzQa : S.z ∈ S.Qa h := S.z_mem_Qa_of_mem_QG rfl haQ haz
  have haQa : h * S.z * h⁻¹ ∈ S.Qa h := (S.conjBy h).z_mem_QG
  have hbz : b ≠ S.z := fun e => hbQa (e ▸ hzQa)
  obtain ⟨i, hi, hai⟩ := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) haQ haz
  obtain ⟨j, hj, hbj⟩ := h2a b hb hbQ hbz
  have hadj : adjW i j = false := by
    cases e : adjW i j
    · rfl
    · exact absurd ((h3 h b haQ haz hb hbQ hbz i j hi hj hai hbj).mpr e) hbQa
  have habne : h * S.z * h⁻¹ * b ≠ S.z := by
    intro e
    apply hbQa
    have hb' : b = (h * S.z * h⁻¹)⁻¹ * S.z := by
      calc b = (h * S.z * h⁻¹)⁻¹ * (h * S.z * h⁻¹ * b) := by group
        _ = (h * S.z * h⁻¹)⁻¹ * S.z := by rw [e]
    rw [hb']
    exact (S.Qa h).mul_mem ((S.Qa h).inv_mem haQa) hzQa
  obtain ⟨k, hk, habk⟩ := h2a _ habz (S.QG.mul_mem haQ hbQ) habne
  rw [S.cl_mul haQ hbQ, psi_add, hai, hbj] at habk
  exact hF.wt_ne_xor hi hj hadj k hk habk.symm

theorem smithE7E24Line_of (hF : E7ModelFacts) (hM : SmithE7Module) : SmithE7E24Line := by
  intro G _ _ _ S hw hU h hbQ hbz
  obtain ⟨φ, h2a, h2b, h3, -⟩ := hM G S hw hU
  obtain ⟨i, hi, hbi⟩ := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) hbQ hbz
  obtain ⟨j, hj, hadj, hne⟩ := hF.exists_adj hi
  obtain ⟨c, hc, hcQ, hcj⟩ := h2b j hj
  have hcz : c ≠ S.z := by
    rintro rfl
    rw [S.cl_z, psi_zero] at hcj
    exact hF.wt_ne_zero hj hcj.symm
  refine ⟨c, hc, hcQ, (h3 h c hbQ hbz hc hcQ hcz i j hi hj hbi hcj).mpr hadj, hcz, ?_, ?_⟩
  · rintro rfl
    exact hne (hcj.symm.trans hbi)
  · intro e
    apply hne
    rw [← hcj, ← hbi, e, S.cl_mul S.z_mem_QG hbQ, S.cl_z, zero_add]

theorem smithE7E24_of (hF : E7ModelFacts) (hM : SmithE7Module) : SmithE7E24 := by
  intro G _ _ _ S hw hU x h hx hxM hxQ hyQ
  obtain ⟨φ, h2a, -, h3, h4⟩ := hM G S hw hU
  by_cases hyz : h * S.z * h⁻¹ = S.z
  · rw [S.Qa_eq_QG_of_conj_eq hyz, hyz]
    have e : x * S.z * x⁻¹ = S.z := by
      rw [S.z_comm hxM]
      group
    rw [e]
    exact S.z_mem_QG
  obtain ⟨i, hi, hyi⟩ := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) hyQ hyz
  obtain ⟨k, hk, hkx⟩ := h4 x hx hxM hxQ
  obtain ⟨j, hj, hji, hadj⟩ := hF.tv_wt hk hi
  have hc : IsConj S.z (x * (h * S.z * h⁻¹) * x⁻¹) := isConj_iff.mpr ⟨x * h, by group⟩
  have hcz : x * (h * S.z * h⁻¹) * x⁻¹ ≠ S.z := by
    intro e
    apply hyz
    calc h * S.z * h⁻¹ = x⁻¹ * (x * (h * S.z * h⁻¹) * x⁻¹) * x := by group
      _ = x⁻¹ * (S.z * x) := by rw [e, mul_assoc]
      _ = x⁻¹ * (x * S.z) := by rw [S.z_comm hxM]
      _ = S.z := by group
  have hcj : code32 (φ (S.cl (x * (h * S.z * h⁻¹) * x⁻¹))) = wt j := by
    rw [hkx _ hyQ, hyi, hji]
  exact (h3 h _ hyQ hyz hc (S.conj_mem_QG hxM hyQ) hcz i j hi hj hyi hcj).mpr hadj

end CFSG.GF2Type.SmithTypeE.E7
