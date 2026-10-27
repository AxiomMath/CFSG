module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

@[expose] def layerIn (X : Subgroup H) : Subgroup H :=
  sSup {M : Subgroup H | IsCompIn M X}

@[expose] def conjClosure (L S : Subgroup H) : Subgroup H :=
  ⨆ g ∈ S, L.map (MulAut.conj g).toMonoidHom

@[expose] def InLF (K : Subgroup H) : Prop :=
  ∃ t : H, orderOf t = 2 ∧ IsCompIn K (centralizer ({t} : Set H))

@[expose] def LtF (K L : Subgroup H) : Prop :=
  ∃ s t : H, orderOf s = 2 ∧ orderOf t = 2 ∧ s * t = t * s ∧
    IsCompIn K (centralizer ({s} : Set H)) ∧ IsCompIn L (centralizer ({t} : Set H)) ∧
    K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom

@[expose] def MaximalF (K : Subgroup H) : Prop :=
  InLF K ∧ ∀ L : Subgroup H, TransGen LtF K L → Nonempty (↥K ≃* ↥L)

@[expose] def InL (K : Subgroup H) : Prop :=
  ∃ T : Subgroup H, T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsCompIn K (centralizer (T : Set H))

@[expose] def Lt (K L : Subgroup H) : Prop :=
  ∃ S T : Subgroup H, S ≠ ⊥ ∧ T ≠ ⊥ ∧ IsPGroup 2 S ∧ IsPGroup 2 T ∧ ⁅S, T⁆ ≤ S ⊓ T ∧
    IsCompIn K (centralizer (S : Set H)) ∧ IsCompIn L (centralizer (T : Set H)) ∧
    K ≤ conjClosure L S

@[expose] def Maximal (K : Subgroup H) : Prop :=
  InL K ∧ ∀ L : Subgroup H, TransGen Lt K L → Nonempty ((↥K ⧸ center ↥K) ≃* (↥L ⧸ center ↥L))

theorem InLF.isQuasisimple {K : Subgroup H} (h : InLF K) : CFSG.IsQuasisimple ↥K := by
  obtain ⟨t, -, ht⟩ := h
  exact ht.isQuasisimple

theorem InL.isQuasisimple {K : Subgroup H} (h : InL K) : CFSG.IsQuasisimple ↥K := by
  obtain ⟨T, -, -, ht⟩ := h
  exact ht.isQuasisimple

end CFSG.EvenSporadicStandard.Induction
