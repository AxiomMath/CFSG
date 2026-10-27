module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Asm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Expl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Sign
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5c_k3_data (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {s : G} (hk : Kind5 L s 3) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (φ : ↥L →* omegaGroup hQ)
      (g : OGroup Q) (α : ℤˣ), IsCoverMap L φ ∧ g * g = 1 ∧ invType g = (3, α) ∧
        CoverAct L φ s (orthToSim Q g) := by
  obtain ⟨α, V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, hxt⟩ := hk
  obtain ⟨y, hyx, -, g, hg2, hgty, hgy⟩ := hxt
  have hgx : (QuotientGroup.mk (orthToSim Q g) : ProjSim Q) = x := by
    rw [← hyx, ← hgy, projOrthToProjSim_toProj]
  obtain ⟨φ, hφ, he⟩ := t5_cover_of_model hS hL hdim hsgn e
  exact ⟨V, i1, i2, i3, Q, hQ, φ, g, α, hφ, hg2, hgty,
    t5_coverAct_of_inducesViaP hL hφ he hx hgx⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem covModelI4_of_invType_three (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) {g : OGroup Q}
    (hg : g * g = 1) {α : ℤˣ} (hty : invType g = (3, α)) : CovModelI4 hQ g := by
  obtain ⟨c, fr, hfr⟩ := exists_signChange_three_type hQ hdim hs α
  have hconj : IsConj (fr.signChange {0, 1, 2}) g :=
    isConj_of_invType_eq hQ (fr.signChange_mul_self _) hg (hfr.trans hty.symm)
  exact covModelI4_of_isConj hQ hconj (covModelI4_signChange_three hQ fr)

theorem asc82Tab5_cover_i4_kind3_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 3 →
        ∃ u ∈ XOut L s, orderOf u = 2 ∧ IsI4PlusIn L u ∧ s * u ∈ conjClassIn L s := by
  intro G _ _ L hL s hs _ hk
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, g, α, hφ, hg2, hgty, hact⟩ := t5c_k3_data hS hL hk
  obtain ⟨w, hw, hww, hwt, c, hc⟩ := CovModelI4.exists_cover hQ
    (covModelI4_of_invType_three hQ hφ.finrank_eq hφ.quadSign_eq hg2 hgty)
  exact t5c_cover_i4_of_model hL hφ hs hact hw hww hwt hc

end CFSG.OddStandard.SmallF3.Omega
