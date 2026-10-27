module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_comp_cplx_comm {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (hact : CoverAct L φ s x) {a : ↥L} (ha : s * (a : G) = (a : G) * s) (v : V) :
    (((φ a : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) v) =
      (x : V ≃ₗ[ZMod 3] V) ((((φ a : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) v) := by
  have h := t5_cent_map_mem hact ha
  have h2 := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) h
  simp only [coe_simAct] at h2
  have h3 : (x : V ≃ₗ[ZMod 3] V) * (((φ a : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      (((φ a : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) * (x : V ≃ₗ[ZMod 3] V) :=
    mul_inv_eq_iff_eq_mul.mp h2
  have h4 := congrArg (fun f : V ≃ₗ[ZMod 3] V => f v) h3
  exact h4.symm

theorem t5_comp_cplx_data (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {s : G}
    (hk : Kind5 L s 4 ∨ Kind5 L s 5) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (φ : ↥L →* omegaGroup hQ)
      (c : V ≃ₗ[ZMod 3] V), IsCoverMap L φ ∧ (∀ v, c (c v) = -v) ∧
        ∀ a : ↥L, s * (a : G) = (a : G) * s →
          ∀ v, (((φ a : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) (c v) =
            c ((((φ a : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) v) := by
  rcases hk with hk | hk
  · obtain ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, y, hyx, -, -, p, hpp, hpy⟩ := hk
    have hx' : (QuotientGroup.mk (orthToSim Q p) : ProjSim Q) = x := by
      rw [← hyx, ← hpy, projOrthToProjSim_toProj]
    obtain ⟨φ, hφ, -, hact⟩ := t5_cover_data hS hL hdim hsgn hx hx'
    refine ⟨V, i1, i2, i3, Q, hQ, φ, (p : V ≃ₗ[ZMod 3] V), hφ, ?_, ?_⟩
    · intro v
      have h := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V) v) hpp
      simpa [coe_piOrth_apply] using h
    · intro a ha v
      exact t5_comp_cplx_comm hact ha v
  · obtain ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, hx2, hxn⟩ := hk
    obtain ⟨ρ, hρx, -, hρρ⟩ := ff6m_K4_split hQ hdim hsgn hx2 hxn
    obtain ⟨φ, hφ, -, hact⟩ := t5_cover_data hS hL hdim hsgn hx hρx
    exact ⟨V, i1, i2, i3, Q, hQ, φ, (ρ : V ≃ₗ[ZMod 3] V), hφ, hρρ,
      fun a ha v => t5_comp_cplx_comm hact ha v⟩

end CFSG.OddStandard.SmallF3.Omega
