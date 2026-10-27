module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

section Assembly

theorem ff_k4iv_comm4 {G : Type*} [Group G] {a b c d : G} (hab : Commute a b)
    (hac : Commute a c) (had : Commute a d) (hcd : Commute c d) :
    b * d * c * a = a * b * c * d := by
  have h : Commute a (b * d * c) := (hab.mul_right had).mul_right hac
  calc b * d * c * a = a * (b * d * c) := h.symm.eq
    _ = a * b * (d * c) := by group
    _ = a * b * (c * d) := by rw [hcd.eq]
    _ = a * b * c * d := by group

theorem ff_k4iv_krefl_fixed {ρ : ↥(simGroup Q)} (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) {u : V} (hu : Q u ≠ 0)
    (hup : polar Q u ((ρ : V ≃ₗ[ZMod 3] V) u) = 0) :
    simAct Q ρ (reflTot Q u * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u)) =
      reflTot Q u * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u) := by
  have hRu : Q ((ρ : V ≃ₗ[ZMod 3] V) u) ≠ 0 := by
    rw [ff_k4iv_map_sim hρ]; exact neg_ne_zero.mpr hu
  rw [map_mul, simAct_reflTot hρ, simAct_reflTot hρ, hρρ, reflTot_neg]
  exact (reflTot_comm hu hRu hup).symm

theorem ff_mem_X_of_simple_hom {G : Type} [Group G] (C : Subgroup G) {S : Type} [Group S]
    [Finite S] (f : S →* G) (hf : Function.Injective f) (hfC : ∀ s, f s ∈ C)
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {w : G} (hw : w ∈ f.range)
    (hw2 : w * w = 1) : w ∈ twoPrimeRes (twoRes C) := by
  haveI := hS
  haveI : IsSimpleGroup ↥f.range := (MonoidHom.ofInjective hf).symm.isSimpleGroup
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨a, b, hab⟩ := hnc
  refine ff_mem_X_of_simple C f.range (fun x ⟨s, hs⟩ => hs ▸ hfC s) inferInstance
    ⟨⟨f a, a, rfl⟩, ⟨f b, b, rfl⟩, fun h => hab (hf ?_)⟩ hw hw2
  rw [map_mul, map_mul]
  exact congrArg Subtype.val h

theorem ff_K4IV_cover_of_data (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) {u₁ u₂ : V}
    (hu₁ : Q u₁ = 1) (hu₂ : Q u₂ = 1) (h12 : polar Q u₁ u₂ = 0)
    (h1R1 : polar Q u₁ ((ρ : V ≃ₗ[ZMod 3] V) u₁) = 0)
    (h2R2 : polar Q u₂ ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0)
    (h1R2 : polar Q u₁ ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0)
    (h2R1 : polar Q u₂ ((ρ : V ≃ₗ[ZMod 3] V) u₁) = 0) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))) ∧
      w * w = 1 ∧ KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) a * a⁻¹ = w := by
  have h2dim : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hQ₁ : Q u₁ ≠ 0 := by rw [hu₁]; decide
  have hQ₂ : Q u₂ ≠ 0 := by rw [hu₂]; decide
  have hQR₁ : Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) = -1 := by rw [ff_k4iv_map_sim hρ, hu₁]
  have hQR₂ : Q ((ρ : V ≃ₗ[ZMod 3] V) u₂) = -1 := by rw [ff_k4iv_map_sim hρ, hu₂]
  have hQR₁' : Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) ≠ 0 := by rw [hQR₁]; decide
  have hQR₂' : Q ((ρ : V ≃ₗ[ZMod 3] V) u₂) ≠ 0 := by rw [hQR₂]; decide
  have hRR : polar Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0 := by
    rw [ff_k4iv_polar_sim hρ, h12, neg_zero]
  have h2R1' : polar Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) u₂ = 0 :=
    (QuadraticMap.polar_comm Q _ _).trans h2R1
  have c12 := reflTot_comm hQ₁ hQ₂ h12
  have c1R1 := reflTot_comm hQ₁ hQR₁' h1R1
  have c1R2 := reflTot_comm hQ₁ hQR₂' h1R2
  have c2R2 := reflTot_comm hQ₂ hQR₂' h2R2
  have cR12 := reflTot_comm hQR₁' hQ₂ h2R1'
  have cR1R2 := reflTot_comm hQR₁' hQR₂' hRR
  obtain ⟨a, ha_def⟩ : ∃ a : OGroup Q, a = reflTot Q u₁ * reflTot Q u₂ := ⟨_, rfl⟩
  have ht_eq : simAct Q ρ a * a⁻¹ =
      (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
        (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) := by
    rw [ha_def, map_mul, simAct_reflTot hρ, simAct_reflTot hρ, mul_inv_rev, reflTot_inv,
      reflTot_inv]
    simpa only [mul_assoc] using ff_k4iv_comm4 c1R1 c12 c1R2 c2R2
  have hd1_fix := ff_k4iv_krefl_fixed hρ hρρ hQ₁ h1R1
  have hv_ne : Q (u₁ - u₂) ≠ 0 := by rw [ff_k4iv_Q_diff hu₁ hu₂ h12]; decide
  have hv_pol : polar Q (u₁ - u₂) ((ρ : V ≃ₗ[ZMod 3] V) (u₁ - u₂)) = 0 := by
    rw [map_sub, ff_polar_sub_sub, h1R1, h1R2, h2R1, h2R2]; simp
  have hσ_fix := ff_k4iv_krefl_fixed hρ hρρ hv_ne hv_pol
  obtain ⟨-, G1, hG1comm, hG1le, hG1Lie⟩ := ff_aux_layerModel_core' hQ hdim hsgn hρ hρρ
  have hd12 : Commute (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁))
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) :=
    Commute.mul_right (Commute.mul_left c12 cR12) (Commute.mul_left c1R2 cR1R2)
  have ht_G1 : (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) ∈ G1 := by
    have h := hG1comm _ _ hσ_fix hd1_fix
    rw [ff_k4iv_conj_d hu₁ hu₂ h12 hρ h1R1 h1R2 h2R2, ff_k4iv_dinv hρ hQ₁ h1R1] at h
    rw [hd12.eq]
    exact h
  have hgg₁ : (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) = 1 := by
    calc _ = (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
          (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁))⁻¹ := by
          rw [ff_k4iv_dinv hρ hQ₁ h1R1]
      _ = 1 := mul_inv_cancel _
  have hgg₂ : (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) = 1 := by
    calc _ = (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) *
          (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂))⁻¹ := by
          rw [ff_k4iv_dinv hρ hQ₂ h2R2]
      _ = 1 := mul_inv_cancel _
  have htype₁ : invType (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) = (2, 1) := by
    rw [reflTot_of_ne hQ₁, reflTot_of_ne hQR₁']
    exact ff_invType_reflPair hQ hQ₁ hQR₁' h1R1 hu₁ hQR₁
  have htype₂ : invType (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) = (2, 1) := by
    rw [reflTot_of_ne hQ₂, reflTot_of_ne hQR₂']
    exact ff_invType_reflPair hQ hQ₂ hQR₂' h2R2 hu₂ hQR₂
  have horth : ∀ x ∈ commSp (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)),
      ∀ y ∈ commSp (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)),
        polar Q x y = 0 := by
    intro x hx y hy
    rw [reflTot_of_ne hQ₁, reflTot_of_ne hQR₁',
      commSp_reflOf_mul_reflOf_of_orth hQ u₁ _ hQ₁ hQR₁' h1R1] at hx
    rw [reflTot_of_ne hQ₂, reflTot_of_ne hQR₂',
      commSp_reflOf_mul_reflOf_of_orth hQ u₂ _ hQ₂ hQR₂' h2R2] at hy
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    rw [h12, h1R2, h2R1', hRR]
    ring
  have ht_type : invType ((reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂))) = (4, 1) :=
    ff_invType_reflQuad hQ hgg₁ hgg₂ htype₁ htype₂ horth
  have ht_self : ((reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂))) *
      ((reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂))) = 1 :=
    mul_mul_self_of_orth hQ hgg₁ hgg₂ horth
  generalize ht_def : (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) = t at ht_G1 ht_type ht_self ht_eq
  have ha_mem : a ∈ omegaGroup hQ := by
    rw [ha_def, reflTot_of_ne hQ₁, reflTot_of_ne hQ₂]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u₁ u₂ hQ₁ hQ₂ (by rw [hu₁, hu₂])
  have ht_Ω : t ∈ omegaGroup hQ := (hG1le ht_G1).1
  have ht_ne : toProj Q t ≠ 1 := by
    intro h1
    have hker : t ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk' (piGroup Q)] at hker
    rcases mem_piGroup_iff.mp hker with ht1 | htpi
    · rw [ht1, invType_one] at ht_type
      exact absurd ht_type (by decide)
    · rw [htpi, invType_piOrth hQ, hdim, hsgn] at ht_type
      exact absurd ht_type (by decide)
  obtain ⟨e, he⟩ := ff_fixEquiv_sim hQ hdim hsgn ρ
  let f : ↥G1 →* ↥(omegaProj hQ) :=
    (ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)).subtype.comp
      (e.toMonoidHom.comp (Subgroup.inclusion hG1le))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e.injective.comp (Subgroup.inclusion_injective hG1le))
  have hfC : ∀ s : ↥G1, f s ∈ ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q) :=
    fun s => (e _).2
  obtain ⟨hGfin, hGsimple⟩ := ff_fin_simple_psl2 hG1Lie
  haveI := hGfin
  obtain ⟨-, hnc⟩ := ff_simple_of_lieModel_psl2 hG1Lie
  let w : ↥(omegaProj hQ) := ⟨toProj Q t, (mem_omegaProj_iff hQ).mpr ⟨t, ht_Ω, rfl⟩⟩
  have hw_self : w * w = 1 := by
    apply Subtype.ext
    change toProj Q t * toProj Q t = 1
    rw [← map_mul, ht_self, map_one]
  have hw_range : w ∈ f.range := ⟨⟨t, ht_G1⟩, Subtype.ext (he ⟨t, hG1le ht_G1⟩)⟩
  have hw_X : w ∈ twoPrimeRes (twoRes (ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q))) :=
    ff_mem_X_of_simple_hom _ f hf hfC hGsimple hnc hw_range hw_self
  have hKM0 : KM0 (projOrthToProjSim Q (w : ProjOrth Q)) :=
    ⟨toProj Q t, rfl, ht_ne, t, ht_self, ht_type, rfl⟩
  refine ⟨w, hw_X, hw_self, hKM0,
    ⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ((ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)
    (⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩ : ↥(omegaProj hQ)) :
      ↥(omegaProj hQ)) : ProjOrth Q) *
    ((⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩ : ↥(omegaProj hQ))⁻¹ :
      ↥(omegaProj hQ)) = (w : ↥(omegaProj hQ))
  rw [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj]
  change toProj Q (simAct Q ρ a) * (toProj Q a)⁻¹ = toProj Q t
  rw [← ht_eq, map_mul, map_inv]

end Assembly

end CFSG.OddStandard.SmallF3.Omega
