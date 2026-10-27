module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def secV (t : G) (S L E : Subgroup G) : Subgroup G :=
  ⁅E, secM t S L ⊓ L⁆

structure Sec12Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (K1 K2 E : Subgroup G) : Prop extends Sec10Ctx G t L S z K1 K2 where
  alt1 : Sec1011Alt1 t S L
  sylowE : IsSylow2Of E (secCMB t S L)
  S_norm : S ≤ normalizer (E : Set G)
  ML_norm : secM t S L ⊓ L ≤ normalizer (E : Set G)

@[expose] def secN (V : Subgroup G) : Subgroup G :=
  normalizer (V : Set G)

@[expose] def secNb (V : Subgroup G) : Subgroup (MulAut ↥V) :=
  autIn (secN V) V

@[expose] noncomputable def betaOf (V : Subgroup G) (n : G) : MulAut ↥V :=
  open Classical in
  if h : n ∈ normalizer (V : Set G) then V.normalizerMonoidHom ⟨n, h⟩ else 1

@[expose] def secLayerNb (V : Subgroup G) : Subgroup (MulAut ↥V) :=
  CFSG.inSubgroup CFSG.layer (secNb V)

@[expose] def Sec122Alt1 (V X : Subgroup G) : Prop :=
  IsElemAb2 V 8 ∧ ∃ V1 V2 : Subgroup G, V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
    ((Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) ∧ IsNatModA5 V1 ⊥ X ∧ IsNatModA5 V2 ⊥ X) ∨
      (Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧ IsNatModS5 V1 ⊥ X ∧ IsNatModS5 V2 ⊥ X))

@[expose] def Sec122Alt2 (t : G) (V X : Subgroup G) : Prop :=
  IsZ4Pow4 V ∧
    ((Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) ∧
        IsZ4AugModuleMod (alternatingGroup (Fin 5)) V ⊥ X) ∨
      (Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧ IsZ4AugModuleMod ⊤ V ⊥ X)) ∧
    ∀ v ∈ V, t * v * t⁻¹ = v⁻¹

structure Sec12X (t : G) (S L E X : Subgroup G) : Prop where
  inf : X ⊓ secA t S L = ⊥
  sup : X ⊔ secA t S L = (secM t S L ⊓ L) ⊔ S
  alt : Sec122Alt1 (secV t S L E) X ∨ Sec122Alt2 t (secV t S L E) X

@[expose] def Sec128Alt1 (t : G) (S L V : Subgroup G) : Prop :=
  QuotEquivTo (secN V) (oddCoreIn (secN V)) (WrZ2 ↥(secM t S L ⊓ L))

@[expose] def Sec128Alt2 (V : Subgroup G) : Prop :=
  IsNatOmega4Plus V (secLayerNb V) ∧
    (Nat.card (secNb V) = 2 * Nat.card (secLayerNb V) ∨
      Nat.card (secNb V) = 6 * Nat.card (secLayerNb V))

end CFSG.OddStandard.SmallF3.Omega
