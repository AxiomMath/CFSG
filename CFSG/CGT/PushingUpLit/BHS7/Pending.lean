module

public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.CGT.PushingUpLit.BHS7.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def IsMaximalSubgroup (G H : Subgroup Γ) : Prop :=
  H < G ∧ ∀ K : Subgroup Γ, H ≤ K → K < G → K = H

@[expose] def Seven4 (G T : Subgroup Γ) : Prop :=
  ∀ E ∈ bStarG G T, ¬ IsSubnormal E G

@[expose] def omegaSet (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | E ∈ bStarG G T ∧ IsSubnormal E G}

@[expose] def OmegaCStar (G T : Subgroup Γ) : Prop :=
  cStarIn G T ⊓ (⨆ E ∈ omegaSet G T, E) = ⨆ E ∈ omegaSet G T, cStarIn G T ⊓ E ∧
    ∀ E ∈ omegaSet G T,
      ((∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∧
        cStarIn G T ⊓ E = Subgroup.normalizer ((T ⊓ E : Subgroup Γ) : Set Γ) ⊓ E) ∨
      (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m ∧
        Nonempty ((((cStarIn G T ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
          alternatingGroup (Fin (2 * m))))

@[expose] def OmegaCStarProd (G T : Subgroup Γ) : Prop :=
  cStarIn G T ⊓ (⨆ E ∈ omegaSet G T, E) = ⨆ E ∈ omegaSet G T, cStarIn G T ⊓ E

@[expose] def OmegaCStarAlt (G T : Subgroup Γ) : Prop :=
  ∀ E ∈ omegaSet G T, ∀ m : ℕ, 1 ≤ m → IsNaturalAltModule ↥E m →
    Nonempty ((((cStarIn G T ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
      alternatingGroup (Fin (2 * m)))

@[expose] def OmegaMaxSwap (G T : Subgroup Γ) : Prop :=
  ∀ E ∈ omegaSet G T, ∀ m : ℕ, 2 ≤ m → IsNaturalAltModule ↥E m →
    Nat.card ↥(autOn (baum T) (pCoreOf 2 E)) = 2 ^ m

@[expose] def Seven5 (G T : Subgroup Γ) : Prop :=
  ¬ IsMinParabolic2 T G

@[expose] def Seven7 (G T : Subgroup Γ) : Prop :=
  ∀ E ∈ bStarT G T, ∃ H : Subgroup Γ, IsMaximalSubgroup G H ∧ E ⊔ baum T ≤ H ∧
    IsSubnormal E H ∧ ∀ H' : Subgroup Γ, IsMaximalSubgroup G H' → E ⊔ baum T ≤ H' → H' = H

@[expose] def Seven13 (G T : Subgroup Γ) : Prop :=
  ⁅vSub G T, zSub T⁆ = ⊥ ∧
    ∀ A : Subgroup Γ, A ≤ T → ¬ (IsOffG (vSub G T) A ∧ Nat.card (vSub G T) < wtG (vSub G T) A)

@[expose] def Seven14 (G T : Subgroup Γ) : Prop :=
  ∀ E : Subgroup Γ, IsBTBlock G T E → ¬ E ≤ cStarIn G T →
    ∃ A : Subgroup Γ, A ≤ baum T ∧ ⁅E, A⁆ = E ∧ ⁅⁅vSub G T, A⁆, A⁆ = ⊥ ∧
    (vSub G T ⊓ Subgroup.centralizer (A : Set Γ)).relIndex (vSub G T) =
      (A ⊓ Subgroup.centralizer (vSub G T : Set Γ)).relIndex A ∧
    ∀ a ∈ A, a ∉ Subgroup.centralizer (vSub G T : Set Γ) →
      vSub G T ⊓ Subgroup.centralizer (A : Set Γ) =
        vSub G T ⊓ Subgroup.centralizer ({a} : Set Γ)

structure Sec7Pending : Prop where
  seven_thirteen : ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T : Subgroup Γ), MinCex G T →
    Seven4 G T → Seven5 G T → Seven7 G T → Seven13 G T

end CFSG.CGT.PushingUpLit.BHS7
