module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderZ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem component_offender_output
    [Finite V] (hQ : QuadBestOffendersNormalize (ZMod 2) V)
    {G L A : Subgroup (V ≃ₗ[ZMod 2] V)} (hL : IsComponentIn L G) {n : ℕ} (hn : 2 ≤ n)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) (hAG : A ≤ G)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B < weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hcomm : ⁅L, A⁆ ≠ ⊥) :
    ∃ I : Submodule (ZMod 2) V, ComponentSection L A I ∧ commGL L ⊤ = I ∧ I ⊔ fixGL A = ⊤ ∧
      ComponentOffenderOutput L A n α I := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  obtain ⟨I, hsec⟩ := component_section hQ hL hAG hAel hAne hoff hstrict hcomm
  have hI := isInvariant_sup_subgroup hsec.inv_L hsec.inv_A
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hmax : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), B ≤ A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A := by
    intro B hB
    rcases hB.lt_or_eq with hlt | heq
    · by_cases hbot : B = ⊥
      · rw [hbot, weight_bot]
        exact hoff
      · exact (hstrict B (bot_lt_iff_ne_bot.2 hbot) hlt).le
    · rw [heq]
  set R := actOn L A I hsec.A_norm hI L le_sup_left with hR
  have hker : R.ker ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker R) with h | h
    · exfalso
      apply hsec.Lbar_ne
      rw [MonoidHom.range_eq_bot_iff]
      apply MonoidHom.ext
      intro l
      exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top l)
    · exact h
  let RL : ↥L →* ↥(Lbar L A I hsec.A_norm hI) := R.rangeRestrict
  have hRLsurj : Function.Surjective RL := R.rangeRestrict_surjective
  have hRLker : RL.ker ≤ Subgroup.center ↥L :=
    (MonoidHom.ker_rangeRestrict R).le.trans hker
  let α₀ : (↥(Lbar L A I hsec.A_norm hI) ⧸ Subgroup.center ↥(Lbar L A I hsec.A_norm hI)) ≃*
      SL(2, F) := (quotientCenterEquiv hLq.1 RL hRLsurj hRLker).symm.trans α
  have : CFSG.IsElementaryAbelian 2 ↥(Abar L A I hsec.A_norm hI) := hsec.Abar_elem
  obtain ⟨hcen, θ, hθ, halt, hwA⟩ := central_quotient_SL2_alternatives_GL hn hF
    (Lbar L A I hsec.A_norm hI) (Abar L A I hsec.A_norm hI)
    (lbar_irreducible hsec.A_norm hI hsec.irr) hsec.Lbar_qs.1 α₀ hsec.Abar_ne
    (abar_le_normalizer_lbar hsec.A_norm hI)
    (fun a ha b hb w => hsec.Abar_quad a ha b hb w) hsec.Abar_off
  have hinj : ∀ a : ↥A, actOn L A I hsec.A_norm hI A le_sup_right a = 1 →
      resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A I hsec.inv_A a = 1 := by
    intro a ha
    have h1 := hsec.inj ⟨a, Subgroup.mem_sup_right a.2⟩ ha
    rw [← resSub_sup_A hsec.inv_L hsec.inv_A a]
    exact h1
  obtain ⟨hf1, hf2, hVsplit, hIL, hILA, hZfix, hweight⟩ :=
    irreducible_section_weight_equality_saturates hsec.A_norm hsec.L_perf hmax hstrict
      hsec.inv_L hsec.inv_A hsec.comm hinj hsec.Abar_ne hwA
  have hdel : DeletedAlt n (Lbar L A I hsec.A_norm hI) (Abar L A I hsec.A_norm hI) θ →
      I ⊓ fixGL L = ⊥ := fun hD => deleted_Z_trivial hsec θ hD
  refine ⟨I, hsec, hIL, hVsplit, hsec.A_norm, hsec.L_perf, hsec.inv_L, hsec.inv_A, hIL, hILA, hVsplit, hsec.irr, hZfix,
    hf1, injective_iff_map_eq_one _ |>.2 hf2, ?_, ⟨θ, ?_, halt.imp_right fun hD => ⟨hD, hdel hD⟩⟩,
    hweight⟩
  · apply le_antisymm hker
    intro z hz
    rw [MonoidHom.mem_ker]
    have hz' : RL z ∈ Subgroup.center ↥(Lbar L A I hsec.A_norm hI) := by
      have := preimage_center_eq_center hLq.1 RL hRLsurj hRLker
      rw [← this] at hz
      exact hz
    rw [hcen] at hz'
    have : RL z = 1 := Subgroup.mem_bot.1 hz'
    exact congrArg Subtype.val this
  · intro l
    have h1 := hθ (RL l)
    have h2 : α₀ (QuotientGroup.mk (RL l)) = α (QuotientGroup.mk l) := by
      show α ((quotientCenterEquiv hLq.1 RL hRLsurj hRLker).symm (QuotientGroup.mk (RL l))) = _
      rw [(MulEquiv.symm_apply_eq _).2 (quotientCenterEquiv_mk hLq.1 RL hRLsurj hRLker l).symm]
    exact h1.trans h2

end CFSG.QuasithinUnique.Setup.Lift
