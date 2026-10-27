module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PN1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ffTs (fr : PFrame Q (Option (Fin 5)) ffC) : ProjSim Q :=
  projOrthToProjSim Q (toProj Q (fr.signChange {none}))

private theorem ffOutFF6PSNorm_B0p_simAct_mem_of_ffB1p (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC) (γ : simGroup Q)
    (hγ : ∀ b ∈ ffB1p hQ fr, ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) b ∈ ffB1p hQ fr) :
    ∀ g ∈ ffB0p fr, simAct Q γ g ∈ ffB0p fr ∨ piOrth Q * simAct Q γ g ∈ ffB0p fr := by
  intro g hg
  have hgω : g ∈ omegaGroup hQ := ffB0p_le_omega hQ fr hg
  have hmem : omegaToProj hQ ⟨g, hgω⟩ ∈ ffB1p hQ fr :=
    (mem_ffStar_iff hQ).mpr ⟨⟨g, hgω⟩, hg, rfl⟩
  have h1 := hγ _ hmem
  rw [ff_simOmegaAct_omegaToProj] at h1
  obtain ⟨g', hg', hg'e⟩ := (mem_ffStar_iff hQ).mp h1
  rcases omegaToProj_eq_iff hQ hg'e with h | h
  · left
    have hh : simAct Q γ g = (g' : OGroup Q) := by simpa using h
    rw [hh]; exact hg'
  · right
    have hh : simAct Q γ g = piOrth Q * (g' : OGroup Q) := by simpa using h
    rw [hh, ← mul_assoc, piOrth_mul_self, one_mul]
    exact hg'

theorem ff6p_star_normalizes (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hx : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1p hQ fr) :
    ∃ (σ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))),
      x = projOrthToProjSim Q (toProj Q (fr.pOrth σ * fr.signChange K)) := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have hbwd : ∀ b ∈ ffB1p hQ fr,
      ffSimOmegaAct hQ h2 (QuotientGroup.mk γ⁻¹) b ∈ ffB1p hQ fr := by
    intro b hb
    have hb' : b ∈ (ffB1p hQ fr).map
        (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom := by
      rw [hx]; exact hb
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb'
    have hthis : ffSimOmegaAct hQ h2 (QuotientGroup.mk γ⁻¹) b = c := by
      rw [← hcb, QuotientGroup.mk_inv, map_inv, MulAut.inv_apply]
      exact MulEquiv.symm_apply_apply _ c
    rw [hthis]; exact hc
  obtain ⟨σ, K, hσK⟩ :=
    ff6p_mono_of_normalizes fr γ (ffOutFF6PSNorm_B0p_simAct_mem_of_ffB1p hQ h2 fr γ⁻¹ hbwd)
  refine ⟨σ, K, ?_⟩
  rw [hσK, projOrthToProjSim_toProj]

theorem ff6p_star_normalizes_simInGStar (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hx : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1p hQ fr) :
    SimInGStar x := by
  obtain ⟨σ, K, h⟩ := ff6p_star_normalizes hQ h2 fr hx
  exact ⟨toProj Q (fr.pOrth σ * fr.signChange K), h.symm⟩

theorem ff6p_star_normalizer (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hπ : piOrth Q ∉ omegaGroup hQ) (fr : PFrame Q (Option (Fin 5)) ffC) {n : ↥(omegaProj hQ)}
    (hn : n ∈ Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) :
    ∃ g : ↥(omegaGroup hQ), (g : OGroup Q) ∈ ffN0p hQ fr ∧ n = omegaToProj hQ g := by
  have hmap : (ffB1p hQ fr).map
      (ffSimOmegaAct hQ h2 (projOrthToProjSim Q (n : ProjOrth Q))).toMonoidHom =
      ffB1p hQ fr := by
    rw [ffSimOmegaAct_projOrthToProjSim]
    apply le_antisymm
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
      rw [← hcb]
      change MulAut.conjNormal (H := omegaProj hQ) (n : ProjOrth Q) c ∈ ffB1p hQ fr
      have h1 : MulAut.conjNormal (H := omegaProj hQ) (n : ProjOrth Q) c = n * c * n⁻¹ := by
        refine Subtype.ext ?_
        rw [MulAut.conjNormal_apply]
        rfl
      rw [h1]
      exact (mem_set_normalizer_iff.mp hn c).mp hc
    · intro b hb
      rw [Subgroup.mem_map]
      refine ⟨n⁻¹ * b * n, ?_, ?_⟩
      · have h1 : n * (n⁻¹ * b * n) * n⁻¹ = b := by group
        exact (mem_set_normalizer_iff.mp hn _).mpr (by rw [h1]; exact hb)
      · refine Subtype.ext ?_
        rw [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
  obtain ⟨σ, K, hx⟩ := ff6p_star_normalizes hQ h2 fr hmap
  have hxn : (n : ProjOrth Q) = toProj Q (fr.pOrth σ * fr.signChange K) :=
    projOrthToProjSim_injective hx
  obtain ⟨g, hgω, hg⟩ := (mem_omegaProj_iff hQ).mp n.2
  have hgo : toProj Q g = toProj Q (fr.pOrth σ * fr.signChange K) := by rw [hg, hxn]
  have hker : g⁻¹ * (fr.pOrth σ * fr.signChange K) ∈ piGroup Q := QuotientGroup.eq.mp hgo
  have hg_eq : ∃ K' : Finset (Option (Fin 5)), g = fr.pOrth σ * fr.signChange K' := by
    rcases mem_piGroup_iff.mp hker with h | h
    · exact ⟨K, inv_mul_eq_one.mp h⟩
    · refine ⟨Kᶜ, ?_⟩
      have hm : fr.pOrth σ * fr.signChange K = g * piOrth Q := by
        rw [← h, mul_inv_cancel_left]
      have hg' : g = fr.pOrth σ * fr.signChange K * piOrth Q := by
        rw [hm, mul_assoc, piOrth_mul_self, mul_one]
      rw [hg', fr.piOrth_eq_signChange_univ, mul_assoc, fr.signChange_mul]
      rw [show symmDiff K Finset.univ = Kᶜ by
        ext i
        simp [Finset.mem_symmDiff]]
  obtain ⟨K', hK'⟩ := hg_eq
  obtain ⟨b, hb, hb_eq⟩ := ff6p_omega_mono_eq_hat hQ fr (hK' ▸ hgω)
  refine ⟨⟨g, hgω⟩, ?_, ?_⟩
  · exact (mem_ffN0p_iff hQ fr).mpr ⟨σ, b, hb, hK'.trans hb_eq⟩
  · apply Subtype.ext
    rw [coe_omegaToProj]
    exact hg.symm

theorem ff6p_star_cent_sim (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hz : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) :
    ∃ K : Finset (Option (Fin 5)),
      z = projOrthToProjSim Q (toProj Q (fr.signChange K)) := by
  have hfix : ∀ b ∈ ffB1p hQ fr, ffSimOmegaAct hQ h2 z b = b := by
    intro b hb
    apply ffOmegaToSim_injective hQ
    rw [ff_omegaToSim_act, hz b hb, mul_assoc, mul_inv_cancel, mul_one]
  have hmap : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 z).toMonoidHom = ffB1p hQ fr := by
    apply le_antisymm
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
      rw [← hcb]
      change (ffSimOmegaAct hQ h2 z) c ∈ ffB1p hQ fr
      rw [hfix c hc]
      exact hc
    · intro b hb
      exact Subgroup.mem_map.mpr ⟨b, hb, hfix b hb⟩
  obtain ⟨σ, K, hzσ⟩ := ff6p_star_normalizes hQ h2 fr hmap
  have hzσ' : z = QuotientGroup.mk (orthToSim Q (fr.pOrth σ * fr.signChange K)) := by
    rw [hzσ, projOrthToProjSim_toProj]
  have hperm : ∀ J : Finset (Fin 5), Even J.card → ffAct σ J = J := by
    intro J hJ
    have hJω : fr.signChange (ffOpt J) ∈ omegaGroup hQ :=
      ffB0p_le_omega hQ fr ((mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJ, rfl⟩)
    have hb : omegaToProj hQ ⟨fr.signChange (ffOpt J), hJω⟩ ∈ ffB1p hQ fr :=
      (mem_ffStar_iff hQ).mpr ⟨⟨fr.signChange (ffOpt J), hJω⟩,
        (mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJ, rfl⟩, rfl⟩
    have hcoe : toProj Q (fr.signChange (ffOpt (ffAct σ J))) =
        toProj Q (fr.signChange (ffOpt J)) := by
      have h := congrArg Subtype.val (hfix _ hb)
      rw [coe_ffSimOmegaAct, coe_omegaToProj, hzσ', projSimAct_mk, projActAux_toProj,
        simAct_orthToSim, ffMonoP_conj_signChange, ffOpt_map_optionCongr] at h
      exact h
    rcases (ff6p_toProj_signChange_eq_iff fr (ffOpt (ffAct σ J)) (ffOpt J)).mp hcoe with h | h
    · exact ffOpt_injective h
    · exfalso
      have hnone : none ∈ (ffOpt J)ᶜ := by
        rw [Finset.mem_compl]
        exact none_notMem_ffOpt J
      rw [← h] at hnone
      exact (none_notMem_ffOpt (ffAct σ J)) hnone
  have hσ1 : σ = 1 := ff_perm_eq_one_of_fix_even σ hperm
  refine ⟨K, ?_⟩
  rw [hzσ, hσ1, fr.pOrth_one, one_mul]

end CFSG.OddStandard.SmallF3.Omega
