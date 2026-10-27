module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Alts

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {F : Type} [Field F]

@[expose] def NaturalAlt (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) (θ : ↥L₀ ≃* SL(2, F)) : Prop :=
  A₀ ≤ L₀ ∧ ∃ β : W ≃+ (Fin 2 → F),
    (∀ (x : ↥L₀) (w : W), β ((x : W ≃ₗ[ZMod 2] W) w) =
      (θ x : Matrix (Fin 2) (Fin 2) F).mulVec (β w)) ∧
    ∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
      ∀ g : SL(2, F), g ∈ (A₀.subgroupOf L₀).map θ.toMonoidHom ↔
        ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
          ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)

@[expose] def DeletedAlt [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] (n : ℕ)
    (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) (θ : ↥L₀ ≃* SL(2, F)) : Prop :=
  ¬ A₀ ≤ L₀ ∧ n = 2 ∧ Fintype.card (ℙ F (Fin 2 → F)) = 5 ∧
    ∃ (ψ : ↥(L₀ ⊔ A₀) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
      (β : W ≃ₗ[ZMod 2] ↥(evenWeight (ℙ F (Fin 2 → F)))),
      (∀ (x : ↥L₀) (h : (x : W ≃ₗ[ZMod 2] W) ∈ L₀ ⊔ A₀),
        ψ ⟨x, h⟩ = MulAction.toPerm (θ x)) ∧
      (∀ (y : ↥(L₀ ⊔ A₀)) (w : W),
        ((β ((y : W ≃ₗ[ZMod 2] W) w) : ↥(evenWeight (ℙ F (Fin 2 → F)))) :
            ℙ F (Fin 2 → F) → ZMod 2) =
          permAct (ψ y) (β w : ℙ F (Fin 2 → F) → ZMod 2)) ∧
      ((L₀.subgroupOf (L₀ ⊔ A₀)).map ψ.toMonoidHom = alternatingGroup (ℙ F (Fin 2 → F))) ∧
      ((∃ x y, x ≠ y ∧ (A₀.subgroupOf (L₀ ⊔ A₀)).map ψ.toMonoidHom =
          Subgroup.closure {Equiv.swap x y}) ∨
        (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
          (A₀.subgroupOf (L₀ ⊔ A₀)).map ψ.toMonoidHom =
            Subgroup.closure {Equiv.swap x y, Equiv.swap z t}))

end Alts

section Output

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def Lbar (L A : Subgroup (V ≃ₗ[ZMod 2] V)) (I : Submodule (ZMod 2) V)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) :
    Subgroup ((↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I)) :=
  (actOn L A I hAn hI L le_sup_left).range

@[expose] noncomputable def Abar (L A : Subgroup (V ≃ₗ[ZMod 2] V)) (I : Submodule (ZMod 2) V)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) :
    Subgroup ((↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I)) :=
  (actOn L A I hAn hI A le_sup_right).range

structure ComponentOffenderOutput (L A : Subgroup (V ≃ₗ[ZMod 2] V)) (n : ℕ) {F : Type} [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) (I : Submodule (ZMod 2) V) : Prop where
  A_norm : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))
  L_perf : ⁅L, A⁆ = L
  inv_L : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L I
  inv_A : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A I
  I_L : commGL L ⊤ = I
  I_LA : commGL (L ⊔ A) ⊤ = I
  V_split : I ⊔ fixGL A = ⊤
  irr : IsIrrQuot (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L I
  Z_fixed : I ⊓ fixGL L ≤ fixGL (L ⊔ A)
  A_faithful_I : ∀ a : ↥A, resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A I inv_A a = 1 → a = 1
  A_faithful_W : Function.Injective
    (actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) A le_sup_right)
  kernel_L : (actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) L le_sup_left).ker =
    Subgroup.center ↥L
  alternatives : ∃ θ : ↥(Lbar L A I A_norm (isInvariant_sup_subgroup inv_L inv_A)) ≃* SL(2, F),
    (∀ l : ↥L, θ ⟨actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) L le_sup_left l,
      ⟨l, rfl⟩⟩ = α (QuotientGroup.mk l)) ∧
    (NaturalAlt (Lbar L A I A_norm (isInvariant_sup_subgroup inv_L inv_A))
        (Abar L A I A_norm (isInvariant_sup_subgroup inv_L inv_A)) θ ∨
      (DeletedAlt n (Lbar L A I A_norm (isInvariant_sup_subgroup inv_L inv_A))
          (Abar L A I A_norm (isInvariant_sup_subgroup inv_L inv_A)) θ ∧
        I ⊓ fixGL L = ⊥))
  weight_eq : weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V

end Output

end CFSG.QuasithinUnique.Setup.Lift
