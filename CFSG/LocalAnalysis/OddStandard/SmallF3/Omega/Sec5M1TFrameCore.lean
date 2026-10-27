module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TDiagOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimFaith

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5m1t_aux_mul_self (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  revert x
  decide

theorem sec5m1t_core_frame (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (fr : NFrame Q (Fin 6) 1) {x : simGroup Q}
    (hcomm : ∀ h ∈ omegaGroup hQ,
      h * fr.signChange {0, 1, 2, 3} = fr.signChange {0, 1, 2, 3} * h → Odd (orderOf h) →
        x * orthToSim Q h = orthToSim Q h * x)
    (hsq : ∀ t ∈ omegaGroup hQ,
      simAct Q (x * x) t = simAct Q (orthToSim Q (fr.signChange {0, 1, 2, 3})) t) :
    ∃ x₀ : OGroup Q, x = orthToSim Q x₀ ∧ x₀ * x₀ = piOrth Q * fr.signChange {0, 1, 2, 3} := by
  classical
  let t0 : OGroup Q := fr.signChange {0, 1, 2, 3}
  have hy : ∀ h ∈ omegaGroup hQ, h * t0 = t0 * h → Odd (orderOf h) →
      (x : V ≃ₗ[ZMod 3] V) * (h : V ≃ₗ[ZMod 3] V) =
        (h : V ≃ₗ[ZMod 3] V) * (x : V ≃ₗ[ZMod 3] V) := by
    intro h hh hhcomm hodd
    have h' := hcomm h hh hhcomm hodd
    have := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V)) h'
    simpa only [Subgroup.coe_mul, coe_orthToSim] using this
  obtain ⟨a, ha0, ha⟩ := sec5m1t_diag_of_odd hQ fr hy
  obtain ⟨m, hm⟩ := x.2
  have hm1 : m = 1 :=
    sec9t_multiplier_eq_one hm ha0 (ha 0 (by decide)) (by rw [fr.norm 0]; exact one_ne_zero)
  have hxorth : (x : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    isSimilitude_one_iff.mp (by simpa [hm1] using hm)
  let x₀ : OGroup Q := ⟨(x : V ≃ₗ[ZMod 3] V), hxorth⟩
  have hxeq : x = orthToSim Q x₀ := by
    apply Subtype.ext
    rfl
  refine ⟨x₀, hxeq, ?_⟩
  let γ : simGroup Q := (x * x) * (orthToSim Q t0)⁻¹
  have hγact : ∀ t ∈ omegaGroup hQ, simAct Q γ t = t := by
    intro t ht
    have ht' : simAct Q ((orthToSim Q t0)⁻¹) t ∈ omegaGroup hQ := by
      rw [← map_inv, simAct_orthToSim]
      exact (omegaGroup_normal hQ).conj_mem t ht t0⁻¹
    have key : simAct Q (x * x) (simAct Q ((orthToSim Q t0)⁻¹) t) = t := by
      rw [hsq _ ht']
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    show simAct Q ((x * x) * (orthToSim Q t0)⁻¹) t = t
    rw [map_mul, MulAut.mul_apply]
    exact key
  have hγker : ffSimOmegaAct hQ (by omega) (QuotientGroup.mk γ) = 1 :=
    (ffSimOmegaAct_eq_one_iff hQ (by omega) γ).mpr fun t ht => Or.inl (hγact t ht)
  have hγpi : QuotientGroup.mk γ = (1 : ProjSim Q) :=
    ffSimOmegaAct_injective hQ (by omega) (by rw [hγker, map_one])
  have hγmem : γ ∈ piSim Q := (QuotientGroup.eq_one_iff γ).mp hγpi
  rcases mem_piSim_iff.mp hγmem with hγ1 | hγpi
  ·
    exfalso
    have hxx : x * x = orthToSim Q t0 := by
      have h := congrArg (fun g : simGroup Q => g * orthToSim Q t0) hγ1
      simp only [γ, mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    have hL : ((x * x : simGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b 0) = fr.b 0 := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ha 0 (by decide), map_smul, ha 0 (by decide),
        ← smul_assoc, smul_eq_mul, sec5m1t_aux_mul_self a ha0, one_smul]
    have hR : ((orthToSim Q t0 : simGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b 0) = -fr.b 0 := by
      rw [coe_orthToSim, show (t0 : V ≃ₗ[ZMod 3] V) (fr.b 0) =
        (if (0 : Fin 6) ∈ ({0, 1, 2, 3} : Finset (Fin 6)) then -fr.b 0 else fr.b 0) from
        fr.signChange_basis {0, 1, 2, 3} 0, if_pos (by decide)]
    have hlin : ((x * x : simGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b 0) =
        ((orthToSim Q t0 : simGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b 0) := by rw [hxx]
    have hneg : fr.b 0 = -fr.b 0 := by
      calc fr.b 0 = ((x * x : simGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b 0) := hL.symm
        _ = ((orthToSim Q t0 : simGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b 0) := hlin
        _ = -fr.b 0 := hR
    have h2 : (2 : ZMod 3) • fr.b 0 = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hneg
    exact fr.b.ne_zero 0 ((smul_eq_zero.mp h2).resolve_left (by decide))
  ·
    have hxx : x * x = orthToSim Q (piOrth Q) * orthToSim Q t0 := by
      have h := congrArg (fun g : simGroup Q => g * orthToSim Q t0) hγpi
      simp only [γ, mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    have hmap : x * x = orthToSim Q (x₀ * x₀) := by
      rw [hxeq, ← map_mul]
    have hgoal : orthToSim Q (x₀ * x₀) = orthToSim Q (piOrth Q * t0) := by
      rw [← hmap, hxx, map_mul]
    simpa only [t0] using orthToSim_injective hgoal

end CFSG.OddStandard.SmallF3.Omega
