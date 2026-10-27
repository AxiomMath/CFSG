module

public import CFSG.GH74.E2.Cen

public section

namespace CFSG.GH74.E2

open Subgroup

@[expose] def IsCompCen {G : Type*} [Group G] (t : G) (K : Subgroup G) : Prop :=
  GLS.IsCompIn (Cen t) K

structure LocalK (C : Type) [Group C] (Q K : Subgroup C) : Prop where
  Q_normal : Q.Normal
  Q_pgroup : IsPGroup 2 Q
  K_normal : K.Normal
  K_quasi : IsQuasisimple ↥K
  commute : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q
  self_centralizing : ∀ c : C, (∀ q ∈ Q, c * q = q * c) → (∀ k ∈ K, c * k = k * c) → c ∈ Q

end CFSG.GH74.E2
