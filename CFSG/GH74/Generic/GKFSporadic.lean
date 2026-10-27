module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.Walter.J1Props.Multiplier
public import CFSG.Walter.Models

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.Blueprint

theorem noTwoCover_J1_of_walter (S : Type) [Group S] (h : NativeSporadic.IsSporadic S .J1) :
    NoTwoCover S := by
  intro K _ _ hK _ ⟨e⟩
  obtain ⟨eS⟩ := h
  let ε : K ⧸ center K ≃* ↥CFSG.Open.walterJ1 :=
    (e.trans eS).trans CFSG.Walter.walterJ1EquivNative.symm
  have hker := CFSG.Walter.J1Props.J3_multiplier (centralQuotientMap ε)
    (centralQuotientMap_surjective ε) (centralQuotientMap_ker ε).le hK.1.commutator_eq_top
  rwa [centralQuotientMap_ker ε] at hker

end CFSG.GH74.Generic
