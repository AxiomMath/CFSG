module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiPar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTwist
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClassModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84t_gi_involution_mem (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v)
    (E : Subgroup ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))) [E.Normal]
    (h2 : IsPGroup 2 (↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) ⧸ E))
    {b : ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))} (hb : b * b = 1) :
    b ∈ E := by
  obtain ⟨g, rfl⟩ := ff6mTwistHom_surjective hQ hdim hsgn ρ b
  have hgg := (ff6mTwistHom_eq_one_iff hQ hdim hsgn ρ (g * g)).mp (by rw [map_mul]; exact hb)
  have hgΩ : (g : OGroup Q) ∈ omegaGroup hQ := (Subgroup.mem_inf.mp g.2).1
  have hgN : (g : OGroup Q) ∈ ff6mTwistSub ρ := (Subgroup.mem_inf.mp g.2).2
  rcases hgg with h1 | hπ
  · rcases mem_ff6mTwistSub_iff.mp hgN with hfix | htw
    · have hgC : (g : OGroup Q) ∈ fixSub (simAct Q ρ) := mem_fixSub_iff.mpr hfix
      obtain ⟨hLie, hG1Ω, -⟩ := ff6m_K4_core hQ hdim hρ hρρ
      have hG1C : ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ≤ fixSub (simAct Q ρ) := by
        rw [Subgroup.commutator_le]
        intro p hp q hq
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
      have hG1N : ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ≤
          omegaGroup hQ ⊓ ff6mTwistSub ρ := fun x hx =>
        Subgroup.mem_inf.mpr ⟨hG1Ω hx,
          mem_ff6mTwistSub_iff.mpr (Or.inl (mem_fixSub_iff.mp (hG1C hx)))⟩
      let ψ : ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ →*
          ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) :=
        (ff6mTwistHom hQ hdim hsgn ρ).comp (Subgroup.inclusion hG1N)
      obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psl2 hLie
      haveI : Group.IsPerfect ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ :=
        (ff_isQuasisimple_of_simple hs hnc).1
      haveI : Group.IsPerfect ↥ψ.range :=
        Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
      have hle : ψ.range ≤ E := ff_perfect_le_of_quot_two E h2 ψ.range inferInstance
      rcases sec8t84t_gi_claimA hQ hdim hsgn hρ hρρ hgΩ hgC with hG | hG
      · exact hle ⟨⟨(g : OGroup Q), hG⟩, rfl⟩
      · have hπΩ : piOrth Q ∈ omegaGroup hQ := by
          rw [piOrth_mem_omegaGroup_iff hQ, hdim, hsgn]
          decide
        have hπ' : piOrth Q ∈ omegaGroup hQ ⊓ ff6mTwistSub ρ :=
          Subgroup.mem_inf.mpr ⟨hπΩ, mem_ff6mTwistSub_iff.mpr (Or.inl (simAct_piOrth ρ))⟩
        let p : ↥(omegaGroup hQ ⊓ ff6mTwistSub ρ) := ⟨piOrth Q, hπ'⟩
        have hp1 : ff6mTwistHom hQ hdim hsgn ρ p = 1 :=
          (ff6mTwistHom_eq_one_iff hQ hdim hsgn ρ p).mpr (Or.inr rfl)
        have hpg : (⟨piOrth Q * (g : OGroup Q), hG1N hG⟩ : ↥(omegaGroup hQ ⊓ ff6mTwistSub ρ)) =
            p * g := Subtype.ext rfl
        have hψ : ψ ⟨piOrth Q * (g : OGroup Q), hG⟩ = ff6mTwistHom hQ hdim hsgn ρ g := by
          show ff6mTwistHom hQ hdim hsgn ρ ⟨piOrth Q * (g : OGroup Q), hG1N hG⟩ = _
          rw [hpg, map_mul, hp1, one_mul]
        rw [← hψ]
        exact hle ⟨_, rfl⟩
    · exact (sec8t84t_gi_twisted_false hQ hdim hρρ h1 hgΩ htw).elim
  · exact (ff6m_not_mem_omega_of_mul_self_eq_pi hQ hdim hsgn hπ hgΩ).elim

end CFSG.OddStandard.SmallF3.Omega
