module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G]

@[expose] def invCent (t : G) : Subgroup G := Subgroup.centralizer ({t} : Set G)

@[expose] def twoCore (t : G) : Subgroup G := CFSG.Open.pCoreOf 2 (invCent t)

structure WreathRel (x₁ x₂ lam : G) : Prop where
  ord_x₁ : orderOf x₁ = 4
  ord_x₂ : orderOf x₂ = 4
  comm : x₁ * x₂ = x₂ * x₁
  inf_eq_bot : zpowers x₁ ⊓ zpowers x₂ = ⊥
  ord_lam : orderOf lam = 2
  conj_x₁ : lam * x₁ * lam⁻¹ = x₂

structure M12Rel (x₁ x₂ lam tau : G) : Prop extends WreathRel x₁ x₂ lam where
  ord_tau : orderOf tau = 2
  comm_lam_tau : lam * tau = tau * lam
  tau_x₁ : tau * x₁ * tau⁻¹ = x₁⁻¹
  tau_x₂ : tau * x₂ * tau⁻¹ = x₂⁻¹

@[expose] def baseGrp (x₁ x₂ : G) : Subgroup G := closure {x₁, x₂}

@[expose] def wreathGrp (x₁ x₂ lam : G) : Subgroup G := closure {x₁, x₂, lam}

@[expose] def m12Grp (x₁ x₂ lam tau : G) : Subgroup G := closure {x₁, x₂, lam, tau}

@[expose] def fourGrp (x₁ x₂ : G) : Subgroup G := closure {x₁ ^ 2, (x₁ * x₂) ^ 2}

@[expose] def NormalIn (K X : Subgroup G) : Prop :=
  K ≤ X ∧ ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K

end CFSG.OddStandard.SmallF3.HarrisU33
