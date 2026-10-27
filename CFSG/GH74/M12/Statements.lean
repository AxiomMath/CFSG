module

public import CFSG.GH74.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.GH74.M12

open Subgroup CFSG.Blueprint

abbrev M12Group : Type := NativeSporadic.Carrier .M12

@[expose] def TwoInvolutionClasses (G : Type*) [Group G] : Prop :=
  ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y

@[expose] def SylowTypeM12 (G : Type*) [Group G] : Prop :=
  ∃ (P : Sylow 2 G) (Q : Sylow 2 M12Group), Nonempty (↥P ≃* ↥Q)

@[expose] def SameInvolutionCentralizerPattern (G : Type*) [Group G] (G' : Type*) [Group G'] :
    Prop :=
  ∃ (P : Sylow 2 G) (P' : Sylow 2 G') (φ : ↥P ≃* ↥P'),
    (∀ u v : ↥P, orderOf (u : G) = 2 → orderOf (v : G) = 2 →
      (IsConj (u : G) (v : G) ↔ IsConj ((φ u : ↥P') : G') ((φ v : ↥P') : G'))) ∧
    (∀ u : ↥P, orderOf (u : G) = 2 →
      Nonempty (↥(centralizer ({(u : G)} : Set G)) ≃*
        ↥(centralizer ({((φ u : ↥P') : G')} : Set G'))))

@[expose] def S_BrauerFong : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → SylowTypeM12 G → TwoInvolutionClasses G →
    NativeSporadic.IsSporadic G .M12

@[expose] def S_GLS_16_1_M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    SameInvolutionCentralizerPattern G M12Group → NativeSporadic.IsSporadic G .M12

@[expose] def q8Subgroups {H : Type*} [Group H] (Q : Subgroup H) : Set (Subgroup H) :=
  {K | K ≤ Q ∧ Nonempty (↥K ≃* QuaternionGroup 2)}

structure Asc03Hyp (G : Type*) [Group G] (z : G) : Prop where
  orderTwo : orderOf z = 2
  card_core : Nat.card ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = 32
  extraspecial : IsExtraspecial 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G)))
  quotient_S3 : Nonempty (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G))
    ≃* Equiv.Perm (Fin 3))
  centralizer_X : ∀ X : Sylow 3 ↥(centralizer ({z} : Set G)),
    ∀ q ∈ CFSG.pCore 2 ↥(centralizer ({z} : Set G)), (∀ x ∈ X, x * q = q * x) →
      (q : G) ∈ zpowers z
  not_weakly_closed : ∃ g : G, g * z * g⁻¹ ≠ z ∧
    ∃ q ∈ CFSG.pCore 2 ↥(centralizer ({z} : Set G)), (q : G) = g * z * g⁻¹

@[expose] def S_Asc03_Theorem1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc03Hyp G z →
    (∃ (V : Subgroup G) (_ : V.Normal), IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 8 ∧
        Nonempty (G ⧸ V ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∨
    ((Nonempty (G ≃* alternatingGroup (Fin 8)) ∨ Nonempty (G ≃* alternatingGroup (Fin 9))) ∧
        ∀ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), ¬ K.Normal) ∨
    (NativeSporadic.IsSporadic G .M12 ∧
        ∀ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal)

@[expose] def S_Asc03_simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ z : G, Asc03Hyp G z →
    (∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal) →
      NativeSporadic.IsSporadic G .M12

@[expose] def S_M12_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → Nat.card G = 95040 →
    ∀ z : G, Asc03Hyp G z →
      (∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal) →
        NativeSporadic.IsSporadic G .M12

@[expose] def S_T2_local : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    SameInvolutionCentralizerPattern G M12Group →
      ∃ z : G, IsCentralInvolution z ∧ Asc03Hyp G z ∧
        ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal

@[expose] def S_T2_order : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    SameInvolutionCentralizerPattern G M12Group → Nat.card G = 95040

structure M12PresRel {G : Type*} [Group G] (f₁ f₂ f₃ f₄ y : G) : Prop where
  r1 : f₁ ^ 2 = 1
  r2 : f₁⁻¹ * f₂ * f₁ * f₂⁻¹ * f₃⁻¹ * f₄ * f₃⁻¹ * f₄⁻¹ = 1
  r3 : f₂ ^ 2 * f₄ * (f₃ ^ 2)⁻¹ * f₄ * f₃ * (f₄ ^ 2)⁻¹ * f₃ * f₄⁻¹ * f₃⁻¹ * f₄ ^ 2 = 1
  r4 : f₁⁻¹ * f₃ * f₁ * f₄⁻¹ * f₃ * f₄ ^ 2 * f₃⁻¹ * f₄⁻¹ = 1
  r5 : f₁⁻¹ * f₄ * f₁ * f₄⁻¹ * f₃ * f₄ * f₃⁻¹ * f₄⁻¹ * f₃⁻¹ * f₄ = 1
  r6 : f₂⁻¹ * f₃ * f₂ * f₄⁻¹ * f₃ * f₄ * f₃ * f₄⁻¹ * (f₃ ^ 2)⁻¹ * f₄ * f₃ = 1
  r7 : f₂⁻¹ * f₄ * f₂ * f₄⁻¹ * f₃⁻¹ * (f₄ * f₃) ^ 2 * f₄⁻¹ * f₃ ^ 2 * f₄ = 1
  r8 : f₃ ^ 5 * (f₄ ^ 5)⁻¹ = 1
  r9 : f₃ ^ 5 * (f₄⁻¹ * f₃⁻¹) ^ 3 = 1
  r10 : (f₃⁻¹ * f₄⁻¹ * f₃ * f₄) ^ 2 = 1
  r11 : ((f₃ ^ 2)⁻¹ * f₄⁻¹ * f₃ * f₄ ^ 2) ^ 2 = 1
  r12 : y ^ 2 = 1
  r13 : (y * (f₄⁻¹ * f₃⁻¹ * (f₄ * f₃) ^ 2 * f₄⁻¹ * (f₃ ^ 2)⁻¹ * f₄ * f₃⁻¹)) ^ 3 = 1
  r14 : (y * f₁) ^ 3 = 1
  r15 : y * (f₄⁻¹ * f₃⁻¹ * f₄ * f₃⁻¹ * f₄⁻¹ * (f₃ ^ 2)⁻¹ * f₄ ^ 2) * y⁻¹ *
    (f₄⁻¹ * (f₃⁻¹ * f₄ ^ 2) ^ 2 * f₃⁻¹ * f₄⁻¹ * f₃ ^ 2 * f₄⁻¹ * f₂)⁻¹ = 1

@[expose] def bfE : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1, 3, 2] * List.formPerm [4, 5, 11, 9, 8, 10, 7, 6]

@[expose] def bfN : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [5, 6] * List.formPerm [7, 11] * List.formPerm [9, 10]

@[expose] def bfF : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 2] * List.formPerm [4, 5, 7, 9, 8, 10, 11, 6]

@[expose] def bfX : Equiv.Perm (Fin 12) := bfE⁻¹ * bfF * bfE * bfF⁻¹

@[expose] def bfJ : Equiv.Perm (Fin 12) := bfF ^ 4

@[expose] def bfS : Subgroup (Equiv.Perm (Fin 12)) := Subgroup.closure {bfE, bfN, bfF}

theorem bfF_pow_mem (n : ℕ) : bfF ^ n ∈ bfS :=
  Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) n

@[expose] def bfJ' : ↥bfS := ⟨bfF ^ 4, bfF_pow_mem 4⟩

@[expose] def bfFusion (pairs : List (Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))) :
    ↥bfS → ↥bfS → Prop :=
  Relation.EqvGen fun x y =>
    IsConj x y ∨ ((x : Equiv.Perm (Fin 12)), (y : Equiv.Perm (Fin 12))) ∈ pairs

@[expose] def bfPairsII : List (Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) :=
  [(bfJ, bfN), (bfJ, bfE * bfF ^ 3), (bfJ, bfX), (bfE * bfN, bfE * bfF), (bfE * bfN, bfN * bfF),
    (bfE * bfN * bfX, bfE * bfN * bfF ^ 3), (bfE * bfN * bfX, bfX * bfF ^ 2),
    (bfN * bfX * bfF, bfF ^ 2), (bfN * bfX * bfF, bfE * bfN * bfF)]

@[expose] def bfPairsIII : List (Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) :=
  [(bfN, bfE * bfN), (bfN, bfE * bfF), (bfN, bfN * bfF), (bfE * bfN * bfX, bfE * bfN * bfF),
    (bfE * bfN * bfX, bfX * bfF ^ 2), (bfJ, bfE * bfF ^ 3), (bfJ, bfX),
    (bfN * bfX * bfF, bfF ^ 2), (bfN * bfX * bfF, bfE * bfN * bfF ^ 3)]

@[expose] def RealizesFusion {G : Type*} [Group G] {P : Sylow 2 G} (ψ : ↥bfS ≃* ↥P)
    (R : ↥bfS → ↥bfS → Prop) : Prop :=
  ∀ x y : ↥bfS, IsConj ((ψ x : ↥P) : G) ((ψ y : ↥P) : G) ↔ R x y

end CFSG.GH74.M12
