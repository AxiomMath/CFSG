module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec74_conj_i4_identity {l t z : G} (hlt : l * t = t * l)
    (hzt : z * t = t * z) (hlinvt : l⁻¹ * t = t * l⁻¹) :
    l * (t * z) * l⁻¹ = (l * z * l⁻¹) * t := by
  have htcentral : t * (l * z * l⁻¹) = (l * z * l⁻¹) * t := by
    calc t * (l * z * l⁻¹)
        = l * t * z * l⁻¹ := by rw [hlt]; group
      _ = l * (t * z) * l⁻¹ := by group
      _ = l * (z * t) * l⁻¹ := by rw [hzt]
      _ = l * z * (t * l⁻¹) := by group
      _ = l * z * (l⁻¹ * t) := by rw [← hlinvt]
      _ = (l * z * l⁻¹) * t := by group
  calc l * (t * z) * l⁻¹
      = (l * t * l⁻¹) * (l * z * l⁻¹) := conj_mul.symm
    _ = t * (l * z * l⁻¹) := by rw [show l * t * l⁻¹ = t by rw [hlt]; group]
    _ = (l * z * l⁻¹) * t := htcentral

theorem sec74_I4_decomp [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) {t : G} {L S : Subgroup G} {z g : G}
    (hA : Sec74Ass G t L S z g) (hs : InducesTypeSome L (g⁻¹ * t * g) 6 1 4 1) :
    ∃ l ∈ L, ∃ c : G, (c = 1 ∨ c = t) ∧ g⁻¹ * t * g = (l * z * l⁻¹) * c := by
  have hLP : IsOm6P L := hA.ctx.isOm6P
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  obtain ⟨hin, -⟩ := (hP.inner_iff G L hLP (g⁻¹ * t * g) hs2 hsN).mpr (Or.inl hs)
  obtain ⟨v, hvL, c, hcC, hv2, hc1t, hsv⟩ :=
    sec7_inner_decomp h72 hP hA.ctx hs2 hA.comm hA.ne hin
  have hvc : g⁻¹ * t * g * c⁻¹ = v := by rw [hsv]; group
  have hv4 : InducesTypeSome L v 6 1 4 1 := by
    rw [← hvc]
    exact inducesTypeSome_mul_centralizer ((centralizer (L : Set G)).inv_mem hcC) hs
  obtain ⟨hz2, hz4⟩ := sec7_z_type hF hA.ctx
  have hvl : v ∈ conjClassIn L z :=
    hP.i4_one_class G L hLP z v hA.ctx.z_mem_L hvL hz2 hv2 hz4 hv4
  simp only [conjClassIn, Set.mem_setOf_eq] at hvl
  obtain ⟨l, hlL, rfl⟩ := hvl
  exact ⟨l, hlL, c, hc1t, by rw [hsv]⟩

theorem sec74NotI4_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) : Sec74NotI4 := by
  intro G _ _ t L S z g hA hs
  obtain ⟨l, hlL, c, hc1t, hsv⟩ := sec74_I4_decomp h36 h72 hP hF hA hs
  have hts : IsConj t (g⁻¹ * t * g) := isConj_iff_inv_mul.mpr ⟨g, rfl⟩
  rcases hc1t with hc1 | hct
  · have hz_conj : IsConj z (g⁻¹ * t * g) := by
      refine isConj_iff.mpr ⟨l, ?_⟩
      rw [hsv, hc1, mul_one]
    exact sec7_not_isConj_z h73 hP hA.ctx (hts.trans hz_conj.symm)
  · have hlt : l * t = t * l :=
      (Subgroup.mem_centralizer_iff.mp hA.ctx.t_mem_centralizer) l hlL
    have hzt : z * t = t * z :=
      (Subgroup.mem_centralizer_iff.mp hA.ctx.t_mem_centralizer) z hA.ctx.z_mem_L
    have hlinvt : l⁻¹ * t = t * l⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp hA.ctx.t_mem_centralizer) l⁻¹ (L.inv_mem hlL)
    have htz_conj : IsConj (t * z) (g⁻¹ * t * g) := by
      refine isConj_iff.mpr ⟨l, ?_⟩
      rw [hsv, hct]
      exact sec74_conj_i4_identity hlt hzt hlinvt
    exact hA.not1 (hts.trans htz_conj.symm)

end CFSG.OddStandard.SmallF3.Omega
