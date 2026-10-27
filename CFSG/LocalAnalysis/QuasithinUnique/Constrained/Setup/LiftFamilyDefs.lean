module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups commutatorElement

universe v

section Defs

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def blockB (H L : Subgroup (V ≃ₗ[ZMod 2] V)) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  ⨆ (A : Subgroup (V ≃ₗ[ZMod 2] V)) (_ : IsMinOffender H A ∧ ⁅L, A⁆ ≠ ⊥), A

structure EvenSL2FamilyCommon (H T : Subgroup (V ≃ₗ[ZMod 2] V)) (r : ℕ)
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  J_eq : offenderJ H = ⨆ i, blockB H (Lc i)
  B_comm : ∀ i j, i ≠ j → ∀ x ∈ blockB H (Lc i), ∀ y ∈ blockB H (Lc j), x * y = y * x
  B_direct : ∀ i, blockB H (Lc i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), blockB H (Lc j)) = ⊥
  B_normal : ∀ i, ((blockB H (Lc i)).subgroupOf (offenderJ H)).Normal
  B_subnormal : ∀ i, ((blockB H (Lc i)).subgroupOf H).IsSubnormal
  L_le_B : ∀ i, Lc i ≤ blockB H (Lc i)
  perm : ∀ t ∈ T, ∀ i, ∃ j, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j ∧
    (blockB H (Lc i)).map (MulAut.conj t).toMonoidHom = blockB H (Lc j) ∧
    (commGL (Lc i) ⊤).map (t : V →ₗ[ZMod 2] V) = commGL (Lc j) ⊤
  trans : ∀ i j, ∃ t ∈ T, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j ∧
    (blockB H (Lc i)).map (MulAut.conj t).toMonoidHom = blockB H (Lc j) ∧
    (commGL (Lc i) ⊤).map (t : V →ₗ[ZMod 2] V) = commGL (Lc j) ⊤
  B_fix_C : ∀ i, ∀ b ∈ blockB H (Lc i), ∀ c ∈ fixGL (oddGen H), b c = c
  B_fix_I : ∀ i j, j ≠ i → ∀ b ∈ blockB H (Lc i), ∀ v ∈ commGL (Lc j) ⊤, b v = v
  I_eq_B : ∀ i, commGL (blockB H (Lc i)) ⊤ = commGL (Lc i) ⊤
  C_eq_J : fixGL (oddGen H) = fixGL (offenderJ H)
  I_inf_C : ∀ i, commGL (Lc i) ⊤ ⊓ fixGL (oddGen H) = commGL (Lc i) ⊤ ⊓ fixGL (Lc i)
  V_sum : (⨆ i, commGL (Lc i) ⊤) ⊔ fixGL (oddGen H) = ⊤
  sum_direct : ∀ x : Fin r → V, (∀ i, x i ∈ commGL (Lc i) ⊤) → ∑ i, x i ∈ fixGL (oddGen H) →
    ∀ i, x i ∈ fixGL (Lc i)
  H_perm_I : ∀ h ∈ H, ∀ i, ∃ j, (commGL (Lc i) ⊤).map (h : V →ₗ[ZMod 2] V) = commGL (Lc j) ⊤
  H_fix_C : ∀ h ∈ H, ∀ c ∈ fixGL (oddGen H), h c ∈ fixGL (oddGen H)
  faithful_VC : ∀ h ∈ H, (∀ v, h v - v ∈ fixGL (oddGen H)) → h = 1
  weight_eq : ∀ A, IsMinOffender H A → weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V
  weight_le : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ H → E ≠ ⊥ → CFSG.IsElementaryAbelian 2 E →
    weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E ≤ Nat.card V

structure NaturalFamily (H : Subgroup (V ≃ₗ[ZMod 2] V)) (F : Type) [Field F] (r : ℕ)
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  B_eq : ∀ i, blockB H (Lc i) = Lc i
  J_eq : offenderJ H = oddGen H
  model : ∀ i, ∃ (θ : ↥(Lc i) ≃* SL(2, F))
      (β : (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) ≃+ (Fin 2 → F)),
    (∀ (l : ↥(Lc i)) (u u' : ↥(commGL (Lc i) ⊤)), (u' : V) = (l : V ≃ₗ[ZMod 2] V) (u : V) →
      β (Submodule.Quotient.mk u') =
        (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u))) ∧
    ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), IsSylowTwoOf A (Lc i) →
      ∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
        ∀ g : SL(2, F), g ∈ (A.subgroupOf (Lc i)).map θ.toMonoidHom ↔
          ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
            ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)
  P_eq : ∀ A, IsMinOffender H A ↔ ∃ i, IsSylowTwoOf A (Lc i)

structure DeletedFamily (H : Subgroup (V ≃ₗ[ZMod 2] V)) (n r : ℕ)
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  n_eq : n = 2
  Z_bot : ∀ i, commGL (Lc i) ⊤ ⊓ fixGL (Lc i) = ⊥
  derived : ∀ i, ⁅blockB H (Lc i), blockB H (Lc i)⁆ = Lc i
  V_direct : (⨆ i, commGL (Lc i) ⊤) ⊓ fixGL (oddGen H) = ⊥
  model : ∀ i, ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω), Fintype.card Ω = 5 ∧
    ∃ (ψ : ↥(blockB H (Lc i)) ≃* Equiv.Perm Ω)
      (β : ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight Ω)),
      (∀ (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
        (u' : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) →
          ((β u' : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) =
            SL2Modules.permAct (ψ b) ((β u : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2)) ∧
      ((Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom = alternatingGroup Ω ∧
      ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), (IsMinOffender H A ∧ ⁅Lc i, A⁆ ≠ ⊥) ↔
        ∃ x y : Ω, x ≠ y ∧ A ≤ blockB H (Lc i) ∧
          (A.subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom = Subgroup.closure {Equiv.swap x y}

structure EvenSL2FamilyOutput (H T : Subgroup (V ≃ₗ[ZMod 2] V)) (n : ℕ) (F : Type) [Field F]
    (r : ℕ) (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  layer : EvenSL2LayerOutput H T r F Lc
  common : EvenSL2FamilyCommon H T r Lc
  alternatives : (NaturalFamily H F r Lc ∧ ¬ DeletedFamily H n r Lc) ∨
    (DeletedFamily H n r Lc ∧ ¬ NaturalFamily H F r Lc)

end Defs

end CFSG.QuasithinUnique.Setup.Lift
