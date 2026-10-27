module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Recog1


public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Two

variable {G : Type*} [Group G] [Finite G] {t v : G} {J S₁ : Subgroup G}

private lemma recog2_derived_map_conj_eq {y : G}
    (hy : y ∈ centralizer ((⁅J, J⁆ : Subgroup G) : Set G)) :
    (⁅J, J⁆).map (MulAut.conj y).toMonoidHom = ⁅J, J⁆ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hcomm : b * y = y * b := Subgroup.mem_centralizer_iff.mp hy b hb
    have hfix : (MulAut.conj y).toMonoidHom b = b := by
      change (MulAut.conj y) b = b
      rw [MulAut.conj_apply, hcomm.symm]
      group
    rw [hfix]
    exact hb
  · intro b hb
    refine Subgroup.mem_map.mpr ⟨b, hb, ?_⟩
    have hcomm : b * y = y * b := Subgroup.mem_centralizer_iff.mp hy b hb
    change (MulAut.conj y) b = b
    rw [MulAut.conj_apply, hcomm.symm]
    group

theorem mem_sup_of_mem_normalizer (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) {g : G}
    (hg : g ∈ normalizer (S₁ : Set G)) : ∃ s ∈ S₁, ∃ j ∈ jOne t S₁, g = s * j := by
  have ht : t ∈ S₁ := hs.V_le cfg.t_mem_kleinV
  have ht' : g * t * g⁻¹ ∈ S₁ := (Subgroup.mem_normalizer_iff.mp hg t).mp ht
  have ht'_ne : g * t * g⁻¹ ≠ 1 := by
    intro h1
    apply cfg.t_ne_one
    have h2 : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    have h3 := congrArg (fun z => g⁻¹ * z * g) h1
    rw [h2] at h3
    simpa using h3
  have ht'_sq : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [cfg.t_sq]; group
  obtain ⟨s, hs_mem, hs_conj⟩ :=
    exists_conj_of_involutions φ ht ht' cfg.t_ne_one ht'_ne cfg.t_sq ht'_sq
  have hc : s⁻¹ * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hct : t * (s⁻¹ * g) = (s⁻¹ * g) * t := by
      calc t * (s⁻¹ * g) = s⁻¹ * (s * t * s⁻¹) * g := by group
        _ = s⁻¹ * (g * t * g⁻¹) * g := by rw [hs_conj]
        _ = (s⁻¹ * g) * t := by group
    exact hct.symm
  obtain ⟨x, hxV, j, hj, hc_eq⟩ := exists_mul_of_mem_centralizer cfg hF hs φ hc
  refine ⟨s * x, S₁.mul_mem hs_mem (hs.V_le hxV), j, hj, ?_⟩
  have hg_eq : g = s * (s⁻¹ * g) := by group
  rw [hg_eq, hc_eq, mul_assoc]

theorem centralizer_derived_le (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) :
    centralizer ((⁅J, J⁆ : Subgroup G) : Set G) ≤ S₁ := by
  intro y hy
  have hy_norm : y ∈ normalizer (S₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases hs.comps (S₁.map (MulAut.conj y).toMonoidHom) (isComponent_conj hs.comp₁ y) with
      h | h
    · exact h
    · exfalso
      have hJ0 : (⁅J, J⁆).map (MulAut.conj y).toMonoidHom = ⁅J, J⁆ :=
        recog2_derived_map_conj_eq hy
      have hEq : S₁.map (MulAut.conj y).toMonoidHom
          = (⁅J, J⁆).map (MulAut.conj y).toMonoidHom := by rw [hJ0, h]
      have hinj : Function.Injective ((MulAut.conj y).toMonoidHom) := (MulAut.conj y).injective
      exact hs.ne (Subgroup.map_injective hinj hEq)
  obtain ⟨s, hs_mem, j, hj, hy_eq⟩ := mem_sup_of_mem_normalizer cfg hF hs φ hy_norm
  have hj_comm : ∀ b ∈ ⁅J, J⁆, j * b = b * j := by
    intro b hb
    have hj_eq : j = s⁻¹ * y := by rw [hy_eq]; group
    have hsb : s⁻¹ * b = b * s⁻¹ :=
      component_commute hs.comp₁ hs.comp₀ hs.ne s⁻¹ (S₁.inv_mem hs_mem) b hb
    have hyb : y * b = b * y := (Subgroup.mem_centralizer_iff.mp hy b hb).symm
    rw [hj_eq]
    calc s⁻¹ * y * b = s⁻¹ * (y * b) := by rw [mul_assoc]
      _ = s⁻¹ * (b * y) := by rw [hyb]
      _ = (s⁻¹ * b) * y := by rw [← mul_assoc]
      _ = (b * s⁻¹) * y := by rw [hsb]
      _ = b * (s⁻¹ * y) := by rw [mul_assoc]
  have hj_one : j = 1 := eq_one_of_mem_jOne cfg hF hs hj hj_comm
  rw [hy_eq, hj_one, mul_one]
  exact hs_mem

end H2Two

end CFSG.EvenSporadicStandard.HSStd.InvCent
