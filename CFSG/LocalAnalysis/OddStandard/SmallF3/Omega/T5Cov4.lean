module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Asm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov4Expl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5c_k4_data (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {s : G} (hk : Kind5 L s 4) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (φ : ↥L →* omegaGroup hQ)
      (p : OGroup Q), IsCoverMap L φ ∧ p * p = piOrth Q ∧ CoverAct L φ s (orthToSim Q p) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, hxp⟩ := hk
  obtain ⟨y, hyx, -, -, p, hp, hpy⟩ := hxp
  have hpx : (QuotientGroup.mk (orthToSim Q p) : ProjSim Q) = x := by
    rw [← hyx, ← hpy, projOrthToProjSim_toProj]
  obtain ⟨φ, hφ, he⟩ := t5_cover_of_model hS hL hdim hsgn e
  exact ⟨V, i1, i2, i3, Q, hQ, φ, p, hφ, hp, t5_coverAct_of_inducesViaP hL hφ he hx hpx⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem covModelI4_of_mul_self_eq_piOrth (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) {p : OGroup Q}
    (hp : p * p = piOrth Q) : CovModelI4 hQ p := by
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hs
  have hconj : IsConj fr.complexStructure p :=
    isConj_of_mul_self_eq_piOrth hQ fr.complexStructure_mul_self hp
  exact covModelI4_of_isConj hQ hconj (covModelI4_complexStructure hQ fr)

theorem asc82Tab5_cover_i4_kind4_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 4 →
        ∃ u ∈ XOut L s, orderOf u = 2 ∧ IsI4PlusIn L u ∧ s * u ∈ conjClassIn L s := by
  intro G _ _ L hL s hs _ hk
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, p, hφ, hp, hact⟩ := t5c_k4_data hS hL hk
  obtain ⟨w, hw, hww, hwt, c, hc⟩ := CovModelI4.exists_cover hQ
    (covModelI4_of_mul_self_eq_piOrth hQ hφ.finrank_eq hφ.quadSign_eq hp)
  exact t5c_cover_i4_of_model hL hφ hs hact hw hww hwt hc

end CFSG.OddStandard.SmallF3.Omega
