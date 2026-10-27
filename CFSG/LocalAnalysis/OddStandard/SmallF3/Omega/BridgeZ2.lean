module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Transport
import CFSG.ClassicalInvolution.Balance.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem isTwoU43_omegaGroup (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) : IsTwoU43 (omegaGroup hQ) := by
  exact ⟨natCard_center_omegaGroup_six_minus hQ hdim hs,
    lieModel_quotient_center_omegaGroup_six_minus hQ hdim hs⟩

@[expose] def Asc82SchurU43 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y → IsTwoU43 Y → IsOmegaCover Y 6 (-1)

theorem isTwoU43_of_isOmegaCover {Y : Type} [Group Y] (h : IsOmegaCover Y 6 (-1)) : IsTwoU43 Y := by
  obtain ⟨V', i1, i2, i3, Q', hQ', hdim, hs, ⟨f⟩⟩ := h
  letI := i1
  letI := i2
  letI := i3
  exact isTwoU43_of_mulEquiv f.symm (isTwoU43_omegaGroup hQ' hdim hs)

theorem isOmegaCover_iff_isTwoU43 (hS : Asc82SchurU43) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) : IsOmegaCover Y 6 (-1) ↔ IsTwoU43 Y := by
  exact ⟨isTwoU43_of_isOmegaCover, fun h => hS Y hY h⟩

theorem isQuasisimple_quotient_oddCore {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L) :
    CFSG.IsQuasisimple (L ⧸ oddCore L) := by
  have h' : CFSG.Open.IsQuasisimple L := ⟨hL.1.commutator_eq_top, hL.2.1⟩
  have hO : CFSG.oddCore L ≤ Subgroup.center L :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple h'
  exact (CFSG.LocalCores.quasisimple_central_quotient hL (CFSG.oddCore L) hO).1

theorem isOmegaCover_oddCore_quotient (hS : Asc82SchurU43) {L : Type} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) (h : IsTwoU43 (L ⧸ oddCore L)) :
    IsOmegaCover (L ⧸ oddCore L) 6 (-1) := by
  exact (isOmegaCover_iff_isTwoU43 hS (isQuasisimple_quotient_oddCore hL)).mpr h

end CFSG.OddStandard.SmallF3.Omega
