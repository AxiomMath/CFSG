module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_cover_data (hS : Asc82SchurU43) (hL : IsOm6Z2 L)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e s x) {x' : simGroup Q}
    (hx' : (QuotientGroup.mk x' : ProjSim Q) = x) :
    ∃ φ : ↥L →* omegaGroup hQ, IsCoverMap L φ ∧
      (∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φ l)) ∧ CoverAct L φ s x' := by
  obtain ⟨φ, hφ, he⟩ := t5_cover_of_model hS hL hdim hs e
  exact ⟨φ, hφ, he, t5_coverAct_of_inducesViaP hL hφ he hx hx'⟩

theorem t5_simHasType_elim {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (h : SimHasType x r α) :
    ∃ t : OGroup Q, t * t = 1 ∧ invType t = (r, α) ∧
      (QuotientGroup.mk (orthToSim Q t) : ProjSim Q) = x := by
  obtain ⟨y, hyx, -, t, ht2, hty, hty'⟩ := h
  refine ⟨t, ht2, hty, ?_⟩
  rw [← hyx, ← hty', projOrthToProjSim_toProj]

end CFSG.OddStandard.SmallF3.Omega
