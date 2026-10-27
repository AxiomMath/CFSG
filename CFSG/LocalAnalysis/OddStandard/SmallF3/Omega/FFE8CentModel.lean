module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8_cent_abelian (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    CFSG.Open.IsElemAbelian 2 (centralizer (Ē : Set (ProjSim Q))) ∧
      Nat.card (centralizer (Ē : Set (ProjSim Q))) ≤ 32 := by
  obtain ⟨ε, hε, fr, hĒ, -⟩ := ffE8_frame_sim hQ hdim hsgn h
  subst hĒ
  rw [ffOutFFE8CentModel_centralizer_eq hε fr]
  exact ⟨ffOutFFE8CentModel_map_elemAbelian fr, ffOutFFE8CentModel_card_le fr⟩

theorem ffE8_cent_sylow (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    ∃ P : Subgroup (ProjSim Q), IsSylow2Of P (ffOmegaSim hQ) ∧
      IsNormalE16In P (ffOmegaSim hQ ⊓ centralizer (Ē : Set (ProjSim Q))) := by
  obtain ⟨ε, hε, fr, hĒ, -⟩ := ffE8_frame_sim hQ hdim hsgn h
  subst hĒ
  rw [ffOutFFE8CentModel_centralizer_eq hε fr]
  exact ffOutFFE8CentModel_cent_sylow_of_frame hQ hdim hsgn hε fr

theorem ffE8_model_cent (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    (CFSG.Open.IsElemAbelian 2 (centralizer (Ē : Set (ProjSim Q))) ∧
        Nat.card (centralizer (Ē : Set (ProjSim Q))) ≤ 32) ∧
      ∃ P : Subgroup (ProjSim Q), IsSylow2Of P (ffOmegaSim hQ) ∧
        IsNormalE16In P (ffOmegaSim hQ ⊓ centralizer (Ē : Set (ProjSim Q))) :=
  ⟨ffE8_cent_abelian hQ hdim hsgn h, ffE8_cent_sylow hQ hdim hsgn h⟩

end CFSG.OddStandard.SmallF3.Omega
