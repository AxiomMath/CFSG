module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2CoverAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTwist
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap CFSG.Blueprint
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem reflTot_apply_of_polar_eq_zero (u x : V) (h : polar Q u x = 0) :
    ((reflTot Q u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x := by
  rw [coe_reflTot_apply, h]; simp

private theorem reflTot_apply_self (u : V) (hu : Q u ≠ 0) :
    ((reflTot Q u : OGroup Q) : V ≃ₗ[ZMod 3] V) u = -u := by
  letI : Invertible (Q u) := invertibleOfNonzero hu
  rw [reflTot_of_ne hu, reflOf_eq u hu, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_self]

theorem ff6m_N2_cover_of_p (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {p : OGroup Q} (hp : p * p = piOrth Q) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoRes (ffFix hQ (by omega) (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)) ∧
      w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (QuotientGroup.mk (orthToSim Q p) : ProjSim Q) a * a⁻¹ = w := by
  obtain ⟨u₁, u₂, hu₁, hu₂, h12, h1P1, h2P2, h1P2, h2P1⟩ :=
    ff6m_N2_pair_facts hQ hdim hsgn hp
  have h2dim : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hQ₁ : Q u₁ ≠ 0 := by rw [hu₁]; decide
  have hQ₂ : Q u₂ ≠ 0 := by rw [hu₂]; decide
  have hP₁ : Q ((p : V ≃ₗ[ZMod 3] V) u₁) = 1 := by rw [map_ogroup_apply, hu₁]
  have hP₂ : Q ((p : V ≃ₗ[ZMod 3] V) u₂) = 1 := by rw [map_ogroup_apply, hu₂]
  have hP₁' : Q ((p : V ≃ₗ[ZMod 3] V) u₁) ≠ 0 := by rw [hP₁]; decide
  have hP₂' : Q ((p : V ≃ₗ[ZMod 3] V) u₂) ≠ 0 := by rw [hP₂]; decide
  have hP12 : polar Q ((p : V ≃ₗ[ZMod 3] V) u₁) ((p : V ≃ₗ[ZMod 3] V) u₂) = 0 := by
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup p.2, h12]
  have hP1_2 : polar Q ((p : V ≃ₗ[ZMod 3] V) u₁) u₂ = 0 :=
    (QuadraticMap.polar_comm Q _ _).trans h2P1
  have hPP : ∀ u : V, (p : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) u) = -u := by
    intro u
    have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) u) hp
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_piOrth_apply] using h
  have c12 := reflTot_comm hQ₁ hQ₂ h12
  have c1P1 := reflTot_comm hQ₁ hP₁' h1P1
  have c1P2 := reflTot_comm hQ₁ hP₂' h1P2
  have c2P2 := reflTot_comm hQ₂ hP₂' h2P2
  have cP12 := reflTot_comm hP₁' hQ₂ hP1_2
  have cP1P2 := reflTot_comm hP₁' hP₂' hP12
  let d₁ : OGroup Q := reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)
  let d₂ : OGroup Q := reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)
  let t : OGroup Q := d₁ * d₂
  have hd12 : Commute d₁ d₂ := by
    show Commute (reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁))
      (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂))
    exact Commute.mul_right (Commute.mul_left c12 cP12) (Commute.mul_left c1P2 cP1P2)
  obtain ⟨a, ha_def⟩ : ∃ a : OGroup Q, a = reflTot Q u₁ * reflTot Q u₂ := ⟨_, rfl⟩
  have ha_mem : a ∈ omegaGroup hQ := by
    rw [ha_def, reflTot_of_ne hQ₁, reflTot_of_ne hQ₂]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u₁ u₂ hQ₁ hQ₂ (by rw [hu₁, hu₂])
  have ht_eq : simAct Q (orthToSim Q p) a * a⁻¹ = t := by
    rw [ha_def, map_mul, simAct_orthToSim, simAct_orthToSim, reflTot_conj p u₁,
      reflTot_conj p u₂, mul_inv_rev, reflTot_inv, reflTot_inv]
    show (reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁) * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)) *
      (reflTot Q u₂ * reflTot Q u₁) =
      (reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂))
    simpa only [mul_assoc] using ff_k4iv_comm4 c1P1 c12 c1P2 c2P2
  have hd₁_self : d₁ * d₁ = 1 := by
    show (reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)) = 1
    rw [Commute.mul_mul_mul_comm c1P1.symm (reflTot Q u₁)
      (reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)), reflTot_mul_self u₁,
      reflTot_mul_self ((p : V ≃ₗ[ZMod 3] V) u₁), one_mul]
  have hd₂_self : d₂ * d₂ = 1 := by
    show (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)) *
      (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)) = 1
    rw [Commute.mul_mul_mul_comm c2P2.symm (reflTot Q u₂)
      (reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)), reflTot_mul_self u₂,
      reflTot_mul_self ((p : V ≃ₗ[ZMod 3] V) u₂), one_mul]
  have ht_self : t * t = 1 := by
    show (d₁ * d₂) * (d₁ * d₂) = 1
    rw [Commute.mul_mul_mul_comm hd12.symm d₁ d₂, hd₁_self, hd₂_self, one_mul]
  have hd₁_mem : d₁ ∈ omegaGroup hQ := by
    show reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁) ∈ omegaGroup hQ
    rw [reflTot_of_ne hQ₁, reflTot_of_ne hP₁']
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u₁ ((p : V ≃ₗ[ZMod 3] V) u₁) hQ₁ hP₁'
      (by rw [hu₁, hP₁])
  have hd₂_mem : d₂ ∈ omegaGroup hQ := by
    show reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂) ∈ omegaGroup hQ
    rw [reflTot_of_ne hQ₂, reflTot_of_ne hP₂']
    exact reflOf_mul_reflOf_mem_omegaGroup hQ u₂ ((p : V ≃ₗ[ZMod 3] V) u₂) hQ₂ hP₂'
      (by rw [hu₂, hP₂])
  have ht_Ω : t ∈ omegaGroup hQ := by
    show d₁ * d₂ ∈ omegaGroup hQ
    exact mul_mem hd₁_mem hd₂_mem
  have hd₁_fix : simAct Q (orthToSim Q p) d₁ = d₁ := by
    show simAct Q (orthToSim Q p)
      (reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)) =
      reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)
    rw [map_mul, simAct_orthToSim, simAct_orthToSim, reflTot_conj p u₁,
      reflTot_conj p ((p : V ≃ₗ[ZMod 3] V) u₁), hPP u₁, reflTot_neg]
    exact c1P1.symm
  have hd₂_fix : simAct Q (orthToSim Q p) d₂ = d₂ := by
    show simAct Q (orthToSim Q p)
      (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)) =
      reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)
    rw [map_mul, simAct_orthToSim, simAct_orthToSim, reflTot_conj p u₂,
      reflTot_conj p ((p : V ≃ₗ[ZMod 3] V) u₂), hPP u₂, reflTot_neg]
    exact c2P2.symm
  have ht_fix : simAct Q (orthToSim Q p) t = t := by
    show simAct Q (orthToSim Q p) (d₁ * d₂) = d₁ * d₂
    rw [map_mul, hd₁_fix, hd₂_fix]
  have ht_C : t ∈ Subgroup.centralizer ({p} : Set (OGroup Q)) := by
    rw [← fixSub_simAct_orthToSim p]
    exact mem_fixSub_iff.mpr ht_fix
  let C : Subgroup (OGroup Q) := Subgroup.centralizer ({p} : Set (OGroup Q))
  let G1 : Subgroup (OGroup Q) := ⁅C, C⁆
  obtain ⟨hLie0, hG1le0, hpi0, hcases0⟩ := ff6m_N2_core hQ hdim hsgn hp
  have hLie : LieModel ↥G1 .PSU 3 3 1 := by simpa only [G1, C] using hLie0
  have hG1le : G1 ≤ omegaGroup hQ := by simpa only [G1, C] using hG1le0
  have hpi : piOrth Q ∉ G1 := by simpa only [G1, C] using hpi0
  have hG1le_C : G1 ≤ C := by
    show ⁅C, C⁆ ≤ C
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  have ht_mem : t ∈ omegaGroup hQ ⊓ Subgroup.centralizer ({p} : Set (OGroup Q)) :=
    Subgroup.mem_inf.mpr ⟨ht_Ω, ht_C⟩
  obtain ⟨t', ht'G1, ht't⟩ : ∃ t' ∈ G1, toProj Q t' = toProj Q t := by
    rcases hcases0 t ht_mem with htG1 | htpiG1
    · exact ⟨t, htG1, rfl⟩
    · refine ⟨piOrth Q * t, htpiG1, ?_⟩
      rw [map_mul, toProj_piOrth, one_mul]
  have htu₁ : ((t : OGroup Q) : V ≃ₗ[ZMod 3] V) u₁ = -u₁ := by
    show (((reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)) : OGroup Q) :
        V ≃ₗ[ZMod 3] V) u₁ = -u₁
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    simp only [LinearEquiv.mul_apply]
    rw [reflTot_apply_of_polar_eq_zero ((p : V ≃ₗ[ZMod 3] V) u₂) u₁
        ((QuadraticMap.polar_comm Q ((p : V ≃ₗ[ZMod 3] V) u₂) u₁).trans h1P2),
      reflTot_apply_of_polar_eq_zero u₂ u₁
        ((QuadraticMap.polar_comm Q u₂ u₁).trans h12),
      reflTot_apply_of_polar_eq_zero ((p : V ≃ₗ[ZMod 3] V) u₁) u₁
        ((QuadraticMap.polar_comm Q ((p : V ≃ₗ[ZMod 3] V) u₁) u₁).trans h1P1),
      reflTot_apply_self u₁ hQ₁]
  let f : V →ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
    { toFun := fun w => ![polar Q w u₁, polar Q w u₂, polar Q w ((p : V ≃ₗ[ZMod 3] V) u₁),
        polar Q w ((p : V ≃ₗ[ZMod 3] V) u₂)]
      map_add' := fun x y => by
        funext i
        fin_cases i <;> simp [QuadraticMap.polar_add_left]
      map_smul' := fun c x => by
        funext i
        fin_cases i <;> simp [QuadraticMap.polar_smul_left] }
  have hdimf : Module.finrank (ZMod 3) (Fin 4 → ZMod 3) = 4 := Module.finrank_fin_fun (ZMod 3)
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by rw [hdimf, hdim]; norm_num)
  obtain ⟨v, hvker, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfv : f v = 0 := LinearMap.mem_ker.mp hvker
  have hv1 : polar Q v u₁ = 0 := by
    have h := congrFun hfv (0 : Fin 4); simpa [f] using h
  have hv2 : polar Q v u₂ = 0 := by
    have h := congrFun hfv (1 : Fin 4); simpa [f] using h
  have hv3 : polar Q v ((p : V ≃ₗ[ZMod 3] V) u₁) = 0 := by
    have h := congrFun hfv (2 : Fin 4); simpa [f] using h
  have hv4 : polar Q v ((p : V ≃ₗ[ZMod 3] V) u₂) = 0 := by
    have h := congrFun hfv (3 : Fin 4); simpa [f] using h
  have hvn : v ≠ -v := by
    intro h
    have h2 : (2 : ZMod 3) • v = 0 := by
      rw [two_smul, add_eq_zero_iff_eq_neg]
      exact h
    exact hvne ((smul_eq_zero.mp h2).resolve_left (by decide))
  have htv : ((t : OGroup Q) : V ≃ₗ[ZMod 3] V) v = v := by
    show (((reflTot Q u₁ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₂ * reflTot Q ((p : V ≃ₗ[ZMod 3] V) u₂)) : OGroup Q) :
        V ≃ₗ[ZMod 3] V) v = v
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    simp only [LinearEquiv.mul_apply]
    rw [reflTot_apply_of_polar_eq_zero ((p : V ≃ₗ[ZMod 3] V) u₂) v
        ((QuadraticMap.polar_comm Q ((p : V ≃ₗ[ZMod 3] V) u₂) v).trans hv4),
      reflTot_apply_of_polar_eq_zero u₂ v
        ((QuadraticMap.polar_comm Q u₂ v).trans hv2),
      reflTot_apply_of_polar_eq_zero ((p : V ≃ₗ[ZMod 3] V) u₁) v
        ((QuadraticMap.polar_comm Q ((p : V ≃ₗ[ZMod 3] V) u₁) v).trans hv3),
      reflTot_apply_of_polar_eq_zero u₁ v
        ((QuadraticMap.polar_comm Q u₁ v).trans hv1)]
  have hu₁_ne : u₁ ≠ 0 := by
    intro h0
    rw [h0] at hu₁
    simp at hu₁
  have ht_ne_one : t ≠ 1 := by
    intro ht1
    have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) u₁) ht1
    rw [htu₁] at h
    have h' : -u₁ = u₁ := by simpa using h
    have h2 : (2 : ZMod 3) • u₁ = 0 := by
      rw [two_smul, add_eq_zero_iff_eq_neg]
      exact h'.symm
    exact hu₁_ne ((smul_eq_zero.mp h2).resolve_left (by decide))
  have ht_ne_pi : t ≠ piOrth Q := by
    intro htpi
    apply hvn
    have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) v) htpi
    rw [htv, coe_piOrth_apply] at h
    exact h
  have ht_ne : toProj Q t ≠ 1 := by
    intro h1
    have hker' : t ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk' (piGroup Q)] at hker'
    rcases mem_piGroup_iff.mp hker' with ht1 | htpi
    · exact ht_ne_one ht1
    · exact ht_ne_pi htpi
  obtain ⟨hGfin, hGsimple⟩ := ff_fin_simple_psu3 hLie
  haveI := hGfin
  obtain ⟨-, hnc⟩ := ff_simple_of_lieModel_psu3 hLie
  have hfC : ∀ g : ↥G1, omegaToProj hQ (Subgroup.inclusion hG1le g) ∈
      ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q) := by
    intro g
    refine (ff6m_mem_ffFix_sim_iff hQ hdim hsgn (orthToSim Q p) _).mpr
      ⟨(g : OGroup Q), hG1le g.2, Or.inl ?_, rfl⟩
    have hmem : (g : OGroup Q) ∈ fixSub (simAct Q (orthToSim Q p)) := by
      rw [fixSub_simAct_orthToSim p]
      exact hG1le_C g.2
    exact mem_fixSub_iff.mp hmem
  let φ : ↥G1 →* ↥(ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)) :=
    ((omegaToProj hQ).comp (Subgroup.inclusion hG1le)).codRestrict _ hfC
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : omegaToProj hQ (Subgroup.inclusion hG1le g) = 1 := congrArg Subtype.val hg
    rcases (omegaToProj_eq_one_iff hQ _).mp h1 with h | h
    · apply Subtype.ext
      simpa using h
    · exfalso
      apply hpi
      have h2 : (g : OGroup Q) = piOrth Q := by simpa using h
      exact h2 ▸ g.2
  let w : ↥(omegaProj hQ) :=
    ⟨toProj Q t, (mem_omegaProj_iff hQ).mpr ⟨t, ht_Ω, rfl⟩⟩
  have hw_self : w * w = 1 := by
    apply Subtype.ext
    change toProj Q t * toProj Q t = 1
    rw [← map_mul, ht_self, map_one]
  have hw_range : w ∈
      ((ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)).subtype.comp φ).range :=
    ⟨⟨t', ht'G1⟩, by
      apply Subtype.ext
      exact ht't⟩
  have hw_X : w ∈
      twoPrimeRes (twoRes (ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q))) :=
    ff_mem_X_of_simple_hom _
      ((ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)).subtype.comp φ)
      (Subtype.val_injective.comp hφinj) (fun s => (φ s).2) hGsimple hnc hw_range hw_self
  have hw_ne : w ≠ 1 := by
    intro hw1
    exact ht_ne (by simpa [w] using congrArg Subtype.val hw1)
  have hle : twoPrimeRes (twoRes (ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q))) ≤
      twoRes (ffFix hQ h2dim (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)) :=
    (Subgroup.closure_le _).mpr fun g hg => hg.1
  refine ⟨w, hle hw_X, hw_self, hw_ne,
    ⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ((ffSimOmegaAct hQ (by omega) (QuotientGroup.mk (orthToSim Q p) : ProjSim Q)
    (⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩ : ↥(omegaProj hQ)) :
      ↥(omegaProj hQ)) : ProjOrth Q) *
    ((⟨toProj Q a, (mem_omegaProj_iff hQ).mpr ⟨a, ha_mem, rfl⟩⟩ : ↥(omegaProj hQ))⁻¹ :
      ↥(omegaProj hQ)) = (w : ↥(omegaProj hQ))
  rw [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj]
  change toProj Q (simAct Q (orthToSim Q p) a) * (toProj Q a)⁻¹ = toProj Q t
  rw [← ht_eq, map_mul, map_inv]

theorem ff6m_N2_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KN2 x) :
    ∃ w : ↥(omegaProj hQ), w ∈ twoRes (ffFix hQ (by omega) x) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
  obtain ⟨y, rfl, -, -, p, hp, rfl⟩ := hx
  rw [projOrthToProjSim_toProj]
  exact ff6m_N2_cover_of_p hQ hdim hsgn hp

end CFSG.OddStandard.SmallF3.Omega
