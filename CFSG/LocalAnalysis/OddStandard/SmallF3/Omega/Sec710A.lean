module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem asc82Lemma710a_of (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (h79a : Asc82Lemma79a) :
    Asc82Lemma710a := by
  intro G _ _ t L S z g B hc
  rcases hc.choice with h | ⟨_, _, ⟨α, hα⟩, _⟩
  · exact h
  · exfalso
    have hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := hc.ctx.sylow.1 hc.s_mem
    have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
      hc.ctx.cent_le_normalizer h36 _ hsC
    have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
      have h_eq : g⁻¹ * t * g = (MulAut.conj g⁻¹) t := by simp [MulAut.conj_apply]
      rw [h_eq, MulEquiv.orderOf_eq, hc.ctx.involution]
    exact sec79_hyp62_no_i1 hP hc.ctx.isOm6P (h79a G t L S z g B hc) hs2 hsN ⟨α, hα⟩

theorem sec710_conj_z_mem [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72)
    (h73 : Asc82Lemma73) (hP : Asc82Tab6P) (hF : Asc82AutFacts) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) (hH : Hyp62At L)
    (hs : g⁻¹ * t * g = t * z) {x : G} (hx : IsConj z x) (hxC : x ∈ centralizer ({t} : Set G)) :
    x ∈ conjClassIn L z := by
  obtain ⟨c, hc_eq⟩ := isConj_iff.mp hx
  have hres := h73 G t L S z hc.ctx c⁻¹ (by rw [inv_inv, hc_eq]; exact hxC)
  rw [inv_inv, hc_eq] at hres
  have hz_type := sec7_z_type hF hc.ctx
  have hx2 : orderOf x = 2 := by
    have h_eq : x = (MulAut.conj c) z := by
      rw [← hc_eq]
      simp [MulAut.conj_apply]
    rw [h_eq, MulEquiv.orderOf_eq, hz_type.1]
  have hxN : x ∈ normalizer (L : Set G) := hc.ctx.cent_le_normalizer h36 x hxC
  rcases hres with hx3 | hx4
  · exact absurd hx3 (sec79_hyp62_no_i3 hP hc.ctx.isOm6P hH hx2 hxN)
  · have hinner := (hP.inner_iff G L hc.ctx.isOm6P x hx2 hxN).mpr (Or.inl hx4)
    have hxt : x ≠ t := by
      intro hxt
      exact hinner.2 (hxt ▸ hc.ctx.t_mem_centralizer)
    obtain ⟨v, hvL, c₀, hc₀C, hv2, hc₀, hx_eq⟩ :=
      sec7_inner_decomp h72 hP hc.ctx hx2 hxC hxt hinner.1
    rcases hc₀ with hc₀ | hc₀
    · have hxL : x ∈ L := by rw [hx_eq, hc₀, mul_one]; exact hvL
      exact hP.i4_one_class G L hc.ctx.isOm6P z x hc.ctx.z_mem_L hxL hz_type.1 hx2
        hz_type.2 hx4
    · exfalso
      have hv_eq : v = x * t⁻¹ := by rw [hx_eq, hc₀]; group
      have hv4 : InducesTypeSome L v 6 1 4 1 := by
        rw [hv_eq]
        exact inducesTypeSome_mul_centralizer
          ((centralizer (L : Set G)).inv_mem hc.ctx.t_mem_centralizer) hx4
      obtain ⟨h, hhL, hvh⟩ := hP.i4_one_class G L hc.ctx.isOm6P z v hc.ctx.z_mem_L hvL
        hz_type.1 hv2 hz_type.2 hv4
      have hthinv : t * h⁻¹ = h⁻¹ * t :=
        (Subgroup.mem_centralizer_singleton_iff.mp
          ((centralizer ({t} : Set G)).inv_mem (hc.ctx.le_centralizer hhL))).symm
      have hzt : z * t = t * z :=
        Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.le_centralizer hc.ctx.z_mem_L)
      have hconjzt : IsConj (z * t) x := by
        refine isConj_iff.mpr ⟨h, ?_⟩
        rw [hx_eq, hc₀, hvh]
        calc h * (z * t) * h⁻¹ = h * z * (t * h⁻¹) := by group
          _ = h * z * (h⁻¹ * t) := by rw [hthinv]
          _ = (h * z * h⁻¹) * t := by group
      have hzzt : IsConj z (z * t) := hx.trans (IsConj.symm hconjzt)
      have httz : IsConj t (t * z) := isConj_iff_inv_mul.mpr ⟨g, hs⟩
      have htz : IsConj t (z * t) := by rw [hzt]; exact httz
      exact (sec7_not_isConj_z h73 hP hc.ctx) (htz.trans (IsConj.symm hzzt))

theorem asc82Lemma710b_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) (h79a : Asc82Lemma79a) (h710a : Asc82Lemma710a) :
    Asc82Lemma710b := by
  intro G _ _ t L S z g B hc
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    exact sec710_conj_z_mem h36 h72 h73 hP hF hc (h79a G t L S z g B hc)
      (h710a G t L S z g B hc) hx hxC
  · rintro ⟨h, hhL, rfl⟩
    refine ⟨isConj_iff.mpr ⟨h, rfl⟩, ?_⟩
    exact hc.ctx.le_centralizer
      (L.mul_mem (L.mul_mem hhL hc.ctx.z_mem_L) (L.inv_mem hhL))

end CFSG.OddStandard.SmallF3.Omega
