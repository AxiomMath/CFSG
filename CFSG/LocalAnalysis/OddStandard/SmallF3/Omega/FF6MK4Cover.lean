module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Pi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4CoverAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap
open CFSG.Blueprint
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_K4_cover_expl (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∃ t a : OGroup Q, a ∈ omegaGroup hQ ∧
      t ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ∧ t * t = 1 ∧ invType t = (4, 1) ∧
        simAct Q ρ a * a⁻¹ = t := by
  obtain ⟨u₁, u₂, hu₁, hu₂, h12, h1R1, h2R2, h1R2, h2R1⟩ :=
    ff6m_K4_pair_facts hQ hdim hρ hρρ
  simp only [QuadraticMap.polarBilin_apply_apply] at h12 h1R1 h2R2 h1R2 h2R1
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
  let C : Subgroup (OGroup Q) := fixSub (simAct Q ρ)
  let G1 : Subgroup (OGroup Q) := ⁅C, C⁆
  have hσ_mem : reflTot Q (u₁ - u₂) *
      reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) (u₁ - u₂)) ∈ C := mem_fixSub_iff.mpr hσ_fix
  have hd1_mem : reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) ∈ C :=
    mem_fixSub_iff.mpr hd1_fix
  have hd12 : Commute (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁))
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) :=
    Commute.mul_right (Commute.mul_left c12 cR12) (Commute.mul_left c1R2 cR1R2)
  have ht_G1 : (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₂)) ∈ G1 := by
    have hmem : ⁅reflTot Q (u₁ - u₂) * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) (u₁ - u₂)),
        reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)⁆ ∈ G1 :=
      Subgroup.commutator_mem_commutator hσ_mem hd1_mem
    rw [commutatorElement_def, ff_k4iv_conj_d hu₁ hu₂ h12 hρ h1R1 h1R2 h2R2,
      ff_k4iv_dinv hρ hQ₁ h1R1] at hmem
    rw [hd12.eq]
    exact hmem
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
  have ha_mem : a ∈ omegaGroup hQ := by
    rw [ha_def, reflTot_of_ne hQ₁, reflTot_of_ne hQ₂]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u₁ u₂ hQ₁ hQ₂ (by rw [hu₁, hu₂])
  exact ⟨_, a, ha_mem, ht_G1, ht_self, ht_type, ht_eq⟩

theorem ff6m_K4_cover_of_rho (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoRes (ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) a * a⁻¹ = w := by
  have h2dim : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨t, a, ha_mem, ht_G1, ht_self, ht_type, ht_eq⟩ :=
    ff6m_K4_cover_expl hQ hdim hsgn hρ hρρ
  let C : Subgroup (OGroup Q) := fixSub (simAct Q ρ)
  let G1 : Subgroup (OGroup Q) := ⁅C, C⁆
  obtain ⟨hLie0, hG1le0, -⟩ := ff6m_K4_core hQ hdim hρ hρρ
  have hLie : LieModel ↥G1 .PSL 2 3 2 := by simpa only [G1, C] using hLie0
  have hG1le : G1 ≤ omegaGroup hQ := by simpa only [G1, C] using hG1le0
  have hG1le_C : G1 ≤ C := by
    show ⁅C, C⁆ ≤ C
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  have ht_Ω : t ∈ omegaGroup hQ := hG1le ht_G1
  have ht_ne : toProj Q t ≠ 1 := by
    intro h1
    have hker : t ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk' (piGroup Q)] at hker
    rcases mem_piGroup_iff.mp hker with ht1 | htpi
    · rw [ht1, invType_one] at ht_type
      exact absurd ht_type (by decide)
    · rw [htpi, invType_piOrth hQ] at ht_type
      exact absurd (congrArg Prod.fst ht_type) (by omega)
  obtain ⟨hGfin, hGsimple⟩ := ff_fin_simple_psl2 hLie
  haveI := hGfin
  obtain ⟨-, hnc⟩ := ff_simple_of_lieModel_psl2 hLie
  have hfC : ∀ g : ↥G1, omegaToProj hQ (Subgroup.inclusion hG1le g) ∈
      ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q) := by
    intro g
    refine (ff6m_mem_ffFix_sim_iff hQ hdim hsgn ρ _).mpr
      ⟨(g : OGroup Q), hG1le g.2, Or.inl ?_, rfl⟩
    exact mem_fixSub_iff.mp (hG1le_C g.2)
  let f : ↥G1 →* ↥(ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)) :=
    ((omegaToProj hQ).comp (Subgroup.inclusion hG1le)).codRestrict _ hfC
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : omegaToProj hQ (Subgroup.inclusion hG1le g) = 1 := congrArg Subtype.val hg
    rcases (omegaToProj_eq_one_iff hQ _).mp h1 with h | h
    · apply Subtype.ext
      simpa using h
    · exfalso
      apply ff6m_K4_pi_not_mem hQ hdim hρ hρρ
      have h2 : (g : OGroup Q) = piOrth Q := by simpa using h
      exact h2 ▸ g.2
  let w : ↥(omegaProj hQ) :=
    ⟨toProj Q t, (mem_omegaProj_iff hQ).mpr ⟨t, ht_Ω, rfl⟩⟩
  have hw_self : w * w = 1 := by
    apply Subtype.ext
    change toProj Q t * toProj Q t = 1
    rw [← map_mul, ht_self, map_one]
  have hw_range : w ∈ ((ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)).subtype.comp f).range :=
    ⟨⟨t, ht_G1⟩, Subtype.ext rfl⟩
  have hw_X : w ∈ twoPrimeRes (twoRes (ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q))) :=
    ff_mem_X_of_simple_hom _ ((ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)).subtype.comp f)
      (Subtype.val_injective.comp hf) (fun s => (f s).2) hGsimple hnc hw_range hw_self
  have hw_ne : w ≠ 1 := by
    intro hw1
    exact ht_ne (by simpa [w] using congrArg Subtype.val hw1)
  have hle : twoPrimeRes (twoRes (ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q))) ≤
      twoRes (ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)) :=
    (Subgroup.closure_le (twoRes (ffFix hQ h2dim (QuotientGroup.mk ρ : ProjSim Q)))).mpr
      fun g hg => hg.1
  refine ⟨w, hle hw_X, hw_self, hw_ne,
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

theorem ff6m_K4_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx2 : x * x = 1) (hx : KM4 x) :
    ∃ w : ↥(omegaProj hQ), w ∈ twoRes (ffFix hQ (by omega) x) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
  obtain ⟨ρ, rfl, hρ, hρρ⟩ := ff6m_K4_split hQ hdim hsgn hx2 hx
  exact ff6m_K4_cover_of_rho hQ hdim hsgn hρ hρρ

end CFSG.OddStandard.SmallF3.Omega
