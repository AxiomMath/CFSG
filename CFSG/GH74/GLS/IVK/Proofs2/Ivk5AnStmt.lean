module

public import CFSG.GH74.GLS.Stage1.Thm4.Closed
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
open scoped commutatorElement

section Vocab

variable {H : Type} [Group H]

@[expose] def ZK (K : Subgroup H) : Subgroup H := (center ↥K).map K.subtype

@[expose] def CenK (K : Subgroup H) (S : Set H) : Subgroup H := K ⊓ centralizer S

@[expose] def O2res (C : Subgroup H) : Subgroup H := (oResidual 2 ↥C).map C.subtype

@[expose] def O2core (C : Subgroup H) : Subgroup H := (pCore 2 ↥C).map C.subtype

@[expose] def QuotIso (C N : Subgroup H) (P : Type) [Group P] : Prop :=
  ∃ φ : ↥C →* P, Function.Surjective φ ∧ φ.ker = N.subgroupOf C

end Vocab

section Lemma53

variable {H : Type} [Group H]

@[expose] def Concl53ab (K : Subgroup H) (U : Subgroup H) : Prop :=
  ∃ X : Subgroup H, X ≤ CenK K (U : Set H) ∧ Nat.card X = 3 ∧
    (∃ v ∈ CenK K (U : Set H), v ^ 2 = 1 ∧
      ∀ c ∈ CenK K (U : Set H), ∃ o ∈ pPrimeCoreOf 2 (CenK K (U : Set H)), ∃ q ∈ O2core (O2res (CenK K (U : Set H))),
        ∃ x ∈ X, ∃ e ∈ zpowers v, c = o * q * x * e) ∧
    ⁅O2core (O2res (CenK K (U : Set H))), X⁆ = O2core (O2res (CenK K (U : Set H))) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 (O2core (O2res (CenK K (U : Set H)))) (O2res (CenK K (U : Set H))) ∧
    O2core (O2res (CenK K (U : Set H))) ⊓ centralizer (X : Set H) = U

@[expose] def Concl53c (K : Subgroup H) (U : Subgroup H) : Prop :=
  Nonempty (↥(O2core (O2res (CenK K (U : Set H)))) ≃* CFSG.GH74.GLS.Bg.TwoGroups.SylSL3_4)

@[expose] def Concl53d (K : Subgroup H) (U : Subgroup H) : Prop :=
  CenK K ((O2core (O2res (CenK K (U : Set H))) : Subgroup H) : Set H) = U ⊔ pPrimeCoreOf 2 (CenK K (U : Set H)) ∧
    U ⊓ pPrimeCoreOf 2 (CenK K (U : Set H)) = ⊥ ∧
    ∀ u ∈ U, ∀ o ∈ pPrimeCoreOf 2 (CenK K (U : Set H)), u * o = o * u

@[expose] def Concl53e (K : Subgroup H) (n : ℕ) (U : Subgroup H) : Prop :=
  Nat.card (pPrimeCoreOf 2 (CenK K (U : Set H))) = (if n = 11 then 3 else 1)

@[expose] def Concl53f (K : Subgroup H) (n : ℕ) (U : Subgroup H) : Prop :=
  (n ≤ 9 → QuotIso (CenK K (U : Set H)) (O2core (O2res (CenK K (U : Set H)))) (alternatingGroup (Fin 3))) ∧
    (10 ≤ n → QuotIso (CenK K (U : Set H))
      (pPrimeCoreOf 2 (CenK K (U : Set H)) ⊔ O2core (O2res (CenK K (U : Set H)))) (Equiv.Perm (Fin 3)))

@[expose] def IVK_5_3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) (n : ℕ), Hyp5B H K n →
    ∀ U : Subgroup H, U ≤ K → IVK.IsFourSubgroup U → ZK K ≤ U →
      Concl53ab K U ∧ Concl53c K U ∧ Concl53d K U ∧ Concl53e K n U ∧ Concl53f K n U

end Lemma53

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
