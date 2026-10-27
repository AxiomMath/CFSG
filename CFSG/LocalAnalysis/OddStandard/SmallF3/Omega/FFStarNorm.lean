module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoComb2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_simOmegaAct_omegaToProj (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (γ : simGroup Q) (g : ↥(omegaGroup hQ)) :
    ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) (omegaToProj hQ g) =
      omegaToProj hQ ⟨simAct Q γ (g : OGroup Q), ff_simAct_mem_omegaGroup hQ h2 γ g.2⟩ := by
  apply Subtype.ext
  simp only [coe_ffSimOmegaAct, coe_omegaToProj, projSimAct_mk, projActAux_toProj]

private theorem ffB0_simAct_mem_of_ffB1 (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1) (γ : simGroup Q)
    (hγ : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) b ∈ ffB1 hQ fr) :
    ∀ g ∈ ffB0 fr, simAct Q γ g ∈ ffB0 fr := by
  intro g hg
  have hgω : g ∈ omegaGroup hQ := ffB0_le_omega hQ fr hg
  have hmem : omegaToProj hQ ⟨g, hgω⟩ ∈ ffB1 hQ fr :=
    (mem_ffStar_iff hQ).mpr ⟨⟨g, hgω⟩, hg, rfl⟩
  have h1 := hγ _ hmem
  rw [ff_simOmegaAct_omegaToProj] at h1
  obtain ⟨g', hg', hg'e⟩ := (mem_ffStar_iff hQ).mp h1
  rcases omegaToProj_eq_iff hQ hg'e with h | h
  · have hh : simAct Q γ g = (g' : OGroup Q) := by simpa using h
    rw [hh]; exact hg'
  · have hh : simAct Q γ g = piOrth Q * (g' : OGroup Q) := by simpa using h
    rw [hh]; exact Subgroup.mul_mem _ (piOrth_mem_ffB0 fr) hg'

theorem ff_star_normalizes (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q}
    (hx : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1 hQ fr) :
    ∃ (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)),
      x = projOrthToProjSim Q (toProj Q (fr.permOrth σ * fr.signChange K)) := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have hbwd : ∀ b ∈ ffB1 hQ fr,
      ffSimOmegaAct hQ h2 (QuotientGroup.mk γ⁻¹) b ∈ ffB1 hQ fr := by
    intro b hb
    have hb' : b ∈ (ffB1 hQ fr).map
        (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom := by
      rw [hx]; exact hb
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb'
    have hthis : ffSimOmegaAct hQ h2 (QuotientGroup.mk γ⁻¹) b = c := by
      rw [← hcb, QuotientGroup.mk_inv, map_inv, MulAut.inv_apply]
      exact MulEquiv.symm_apply_apply _ c
    rw [hthis]; exact hc
  obtain ⟨σ, K, hσK⟩ :=
    ffMono_of_normalizes fr γ (ffB0_simAct_mem_of_ffB1 hQ h2 fr γ⁻¹ hbwd)
  refine ⟨σ, K, ?_⟩
  rw [hσK, projOrthToProjSim_toProj]

theorem ff_star_normalizes_simInGStar (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q}
    (hx : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1 hQ fr) :
    SimInGStar x := by
  obtain ⟨σ, K, h⟩ := ff_star_normalizes hQ h2 fr hx
  exact ⟨toProj Q (fr.permOrth σ * fr.signChange K), h.symm⟩

theorem ff_star_normalizer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {n : ↥(omegaProj hQ)}
    (hn : n ∈ Subgroup.normalizer ((ffB1 hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) :
    ∃ (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6))
      (h : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ),
      n = omegaToProj hQ ⟨fr.permOrth σ * fr.signChange K, h⟩ := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hmap : (ffB1 hQ fr).map
      (ffSimOmegaAct hQ h2 (projOrthToProjSim Q (n : ProjOrth Q))).toMonoidHom =
      ffB1 hQ fr := by
    rw [ffSimOmegaAct_projOrthToProjSim]
    apply le_antisymm
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
      rw [← hcb]
      change MulAut.conjNormal (H := omegaProj hQ) (n : ProjOrth Q) c ∈ ffB1 hQ fr
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
  obtain ⟨σ, K, hx⟩ := ff_star_normalizes hQ h2 fr hmap
  have hxn : (n : ProjOrth Q) = toProj Q (fr.permOrth σ * fr.signChange K) :=
    projOrthToProjSim_injective hx
  obtain ⟨g, hgω, hg⟩ := (mem_omegaProj_iff hQ).mp n.2
  have hgo : toProj Q g = toProj Q (fr.permOrth σ * fr.signChange K) := by rw [hg, hxn]
  have hker : g⁻¹ * (fr.permOrth σ * fr.signChange K) ∈ piGroup Q := QuotientGroup.eq.mp hgo
  have ho_mem : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ := by
    rcases mem_piGroup_iff.mp hker with h | h
    · rw [(inv_mul_eq_one.mp h).symm]; exact hgω
    · have ho : fr.permOrth σ * fr.signChange K = g * piOrth Q := by
        rw [← h, mul_inv_cancel_left]
      rw [ho]
      exact Subgroup.mul_mem _ hgω (ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn)
  refine ⟨σ, K, ho_mem, ?_⟩
  apply Subtype.ext
  rw [coe_omegaToProj]
  exact hxn

theorem ff_star_cent_sim (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : NFrame Q (Fin 6) 1) {z : ProjSim Q}
    (hz : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 z b = b) :
    ∃ K : Finset (Fin 6), z = projOrthToProjSim Q (toProj Q (fr.signChange K)) := by
  have hmap : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 z).toMonoidHom = ffB1 hQ fr := by
    apply le_antisymm
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
      rw [← hcb]
      change (ffSimOmegaAct hQ h2 z) c ∈ ffB1 hQ fr
      rw [hz c hc]
      exact hc
    · intro b hb
      exact Subgroup.mem_map.mpr ⟨b, hb, hz b hb⟩
  obtain ⟨σ, K, hzσ⟩ := ff_star_normalizes hQ h2 fr hmap
  have hzσ' : z = QuotientGroup.mk (orthToSim Q (fr.permOrth σ * fr.signChange K)) := by
    rw [hzσ, projOrthToProjSim_toProj]
  have hperm : ∀ J : Finset (Fin 6), Even J.card →
      J.map σ.toEmbedding = J ∨ J.map σ.toEmbedding = Jᶜ := by
    intro J hJ
    have hJω : fr.signChange J ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJ)
    have hb : omegaToProj hQ ⟨fr.signChange J, hJω⟩ ∈ ffB1 hQ fr :=
      (mem_ffStar_iff hQ).mpr ⟨⟨fr.signChange J, hJω⟩, signChange_mem_ffB0 fr hJ, rfl⟩
    have hmem' : fr.signChange (J.map σ.toEmbedding) ∈ omegaGroup hQ := by
      have h' := ff_simAct_mem_omegaGroup hQ h2
        (orthToSim Q (fr.permOrth σ * fr.signChange K)) hJω
      rwa [simAct_orthToSim, ffMono_conj_signChange] at h'
    have hcoe : toProj Q (fr.signChange (J.map σ.toEmbedding)) = toProj Q (fr.signChange J) := by
      have h := congrArg Subtype.val (hz _ hb)
      rw [coe_ffSimOmegaAct, coe_omegaToProj, hzσ', projSimAct_mk, projActAux_toProj,
        simAct_orthToSim, ffMono_conj_signChange] at h
      exact h
    have hkey : omegaToProj hQ ⟨fr.signChange (J.map σ.toEmbedding), hmem'⟩ =
        omegaToProj hQ ⟨fr.signChange J, hJω⟩ := by
      apply Subtype.ext
      rw [coe_omegaToProj, coe_omegaToProj]
      exact hcoe
    rcases omegaToProj_eq_iff hQ hkey with h | h
    · left
      exact (fr.signChange_injective h).symm
    · right
      have h' : fr.signChange J =
          fr.signChange (symmDiff Finset.univ (J.map σ.toEmbedding)) :=
        h.trans (by rw [fr.piOrth_eq_signChange_univ, fr.signChange_mul])
      have hJ' : J = symmDiff Finset.univ (J.map σ.toEmbedding) := fr.signChange_injective h'
      have hcompl : symmDiff Finset.univ (J.map σ.toEmbedding) = (J.map σ.toEmbedding)ᶜ := by
        ext i
        simp [Finset.mem_symmDiff]
      have hJJ : J = (J.map σ.toEmbedding)ᶜ := hJ'.trans hcompl
      exact ((congrArg compl hJJ).trans (by rw [compl_compl])).symm
  have hσ1 : σ = 1 := ff_perm_eq_one_of_even σ hperm
  refine ⟨K, ?_⟩
  rw [hzσ, hσ1, fr.permOrth_one, one_mul]

end CFSG.OddStandard.SmallF3.Omega
