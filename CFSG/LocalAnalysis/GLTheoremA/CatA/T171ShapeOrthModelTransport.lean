module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Ind
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom onCenterQuotient_apply_mk)
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr inner
  congr_mem_inner_iff)

theorem indAut_mem_innAutDerived_iff_centerQuotientHom {Γ : Type} [Group Γ] [Finite Γ]
    {p : ℕ} (hp : p.Prime) {J : Subgroup Γ} (hq : CFSG.Open.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card ↥J) {y : Γ} (hN : y ∈ Subgroup.normalizer (J : Set Γ)) :
    MI.indAut p J y hN ∈ innAutDerived (PSimple p J) ↔
      centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩) ∈
        innAutDerived (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨e, he⟩ := exists_pSimpleEquivCenterQuot_mk hp hq hdvd
  have hkey : MulAut.congr (e.symm) (MI.indAut p J y hN) =
      (centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩))⁻¹ := by
    ext z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
    change e.symm (MI.indAut p J y hN (e (QuotientGroup.mk q))) = _
    rw [he q]
    rw [show MI.indAut p J y hN = CFSG.LocalAnalysis.GLTheoremA.chevAut p J
        ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ from rfl]
    change e.symm (CFSG.LocalAnalysis.GLTheoremA.chevAut p J
      ⟨y⁻¹, Subgroup.inv_mem _ hN⟩
      (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J q)) = _
    rw [CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom]
    change e.symm (QuotientGroup.mk (QuotientGroup.mk
      (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ q))) = _
    rw [show e.symm (QuotientGroup.mk (QuotientGroup.mk
        (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ q))) =
        QuotientGroup.mk (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ q) from by
      rw [← he, MulEquiv.symm_apply_apply]]
    have hR : ((centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩))⁻¹)
        (QuotientGroup.mk q) =
        QuotientGroup.mk ((CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹ q) := by
      rw [show (centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩))⁻¹ =
          centerQuotientHom ↥J ((CFSG.GroupActions.subgroupStabRestrict J
            ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) from
        (map_inv _ _).symm]
      exact onCenterQuotient_apply_mk _ q
    rw [hR]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hinv_apply : (((CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ) =
        y⁻¹ * (q : Γ) * y := by
      have h2 : (CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)
          (((CFSG.GroupActions.subgroupStabRestrict J
            ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q) = q :=
        MulEquiv.apply_symm_apply _ q
      have h3 := congrArg (fun z : ↥J => (z : Γ)) h2
      rw [CFSG.GroupActions.subgroupStabRestrict_apply] at h3
      have h4 : y * (((CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ) * y⁻¹ =
          (q : Γ) := by
        simpa [MulAut.conj_apply] using h3
      calc (((CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ)
          = y⁻¹ * (y * (((CFSG.GroupActions.subgroupStabRestrict J
              ⟨MulAut.conj y, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ) *
              y⁻¹) * y := by group
        _ = y⁻¹ * (q : Γ) * y := by rw [h4]
    rw [hinv_apply]
    simp only [Subtype.coe_mk, inv_inv]
  rw [(mem_innAutDerived_congr e.symm).symm, hkey, inv_mem_iff]

theorem indAut_mem_inner_iff_centerQuotientHom {Γ : Type} [Group Γ] [Finite Γ]
    {p : ℕ} (hp : p.Prime) {J : Subgroup Γ} (hq : CFSG.Open.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card ↥J) {y : Γ} (hN : y ∈ Subgroup.normalizer (J : Set Γ)) :
    MI.indAut p J y hN ∈ inner (PSimple p J) ↔
      centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩) ∈
        inner (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨e, he⟩ := exists_pSimpleEquivCenterQuot_mk hp hq hdvd
  have hkey : MulAut.congr (e.symm) (MI.indAut p J y hN) =
      (centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩))⁻¹ := by
    ext z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
    change e.symm (MI.indAut p J y hN (e (QuotientGroup.mk q))) = _
    rw [he q]
    rw [show MI.indAut p J y hN = CFSG.LocalAnalysis.GLTheoremA.chevAut p J
        ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ from rfl]
    change e.symm (CFSG.LocalAnalysis.GLTheoremA.chevAut p J
      ⟨y⁻¹, Subgroup.inv_mem _ hN⟩
      (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J q)) = _
    rw [CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom]
    change e.symm (QuotientGroup.mk (QuotientGroup.mk
      (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ q))) = _
    rw [show e.symm (QuotientGroup.mk (QuotientGroup.mk
        (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ q))) =
        QuotientGroup.mk (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hN⟩ q) from by
      rw [← he, MulEquiv.symm_apply_apply]]
    have hR : ((centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩))⁻¹)
        (QuotientGroup.mk q) =
        QuotientGroup.mk ((CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹ q) := by
      rw [show (centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩))⁻¹ =
          centerQuotientHom ↥J ((CFSG.GroupActions.subgroupStabRestrict J
            ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) from
        (map_inv _ _).symm]
      exact onCenterQuotient_apply_mk _ q
    rw [hR]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hinv_apply : (((CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ) =
        y⁻¹ * (q : Γ) * y := by
      have h2 : (CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)
          (((CFSG.GroupActions.subgroupStabRestrict J
            ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q) = q :=
        MulEquiv.apply_symm_apply _ q
      have h3 := congrArg (fun z : ↥J => (z : Γ)) h2
      rw [CFSG.GroupActions.subgroupStabRestrict_apply] at h3
      have h4 : y * (((CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ) * y⁻¹ =
          (q : Γ) := by
        simpa [MulAut.conj_apply] using h3
      calc (((CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ)
          = y⁻¹ * (y * (((CFSG.GroupActions.subgroupStabRestrict J
              ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩)⁻¹) q : Γ) *
              y⁻¹) * y := by group
        _ = y⁻¹ * (q : Γ) * y := by rw [h4]
    rw [hinv_apply]
    simp only [Subtype.coe_mk, inv_inv]
  have hinner_iff : MulAut.congr e.symm (MI.indAut p J y hN) ∈
      inner (↥J ⧸ Subgroup.center ↥J) ↔ MI.indAut p J y hN ∈ inner (PSimple p J) :=
    congr_mem_inner_iff e.symm (MI.indAut p J y hN)
  rw [← hinner_iff, hkey]
  exact inv_mem_iff

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
