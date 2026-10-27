module

public import CFSG.CGT.Foote82.T66.Perm310
public import CFSG.CGT.Foote82.T66.Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.PGLModel

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def vFix (v : V) : Subgroup (GLV V) where
  carrier := {g | g v = v}
  mul_mem' := fun {a b} ha hb => by
    show a (b v) = v
    rw [show b v = v from hb, show a v = v from ha]
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    show a⁻¹ v = v
    conv_lhs => rw [← show a v = v from ha]
    exact a.symm_apply_apply v

structure CaseIData (G L : Subgroup (GLV V)) (z : GLV V) (v : V) (H₁ : Subgroup (GLV V))
    (n : ℕ) (ψ : ↥H₁ ≃* Equiv.Perm (Fin (n + 2))) : Prop where
  le : H₁ ≤ G ⊓ vFix v
  six_le : 6 ≤ n
  z_mem : z ∈ H₁
  ψ_z : ψ ⟨z, z_mem⟩ = Equiv.swap 0 1
  L_le : L ≤ H₁
  ψ_L : (L.subgroupOf H₁).map ψ.toMonoidHom = altOn {i | i ≠ 0 ∧ i ≠ 1}
  ψ_H : ((alternatingGroup (Fin (n + 2))).comap ψ.toMonoidHom).map H₁.subtype =
    normalClosure (layerIn (G ⊓ vFix v)) L
  component : IsComponentOf (normalClosure (layerIn (G ⊓ vFix v)) L) (G ⊓ vFix v)
  heart : ∃ β : ↥(commSpace (normalClosure (layerIn (G ⊓ vFix v)) L) ⊤) →+ altHeart (n + 2),
    Function.Surjective β ∧
    β.ker = ((fixedSpace (normalClosure (layerIn (G ⊓ vFix v)) L)).comap
      (commSpace (normalClosure (layerIn (G ⊓ vFix v)) L) ⊤).subtype).toAddSubgroup ∧
    ∀ (h : ↥H₁) (w w' : ↥(commSpace (normalClosure (layerIn (G ⊓ vFix v)) L) ⊤)),
      (w' : V) = (h : GLV V) (w : V) → ∀ x : evenWeight (n + 2), β w = (x : altHeart (n + 2)) →
        β w' = (evenWeightPerm (ψ h) x : altHeart (n + 2))

structure CaseIIData (G L : Subgroup (GLV V)) (z : GLV V) (v : V) (H₁ : Subgroup (GLV V))
    (ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : Prop where
  le : H₁ ≤ G ⊓ vFix v
  z_mem : z ∈ H₁
  ψ_z : Module.finrank (ZMod 2)
    ↥(LinearMap.range (Matrix.mulVecLin
      (((ψ ⟨z, z_mem⟩ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1))) = 1
  L_le : L ≤ H₁
  L_iso : Nonempty (↥L ≃* alternatingGroup (Fin 6))
  ψ_H : ((omegaMinusTwo 2).subgroupOf (orthogonalMinus 2 (ZMod 2) 1 1)
      |>.comap ψ.toMonoidHom).map H₁.subtype = normalClosure (layerIn (G ⊓ vFix v)) L
  component : IsComponentOf (normalClosure (layerIn (G ⊓ vFix v)) L) (G ⊓ vFix v)
  natural : ∃ β : ↥(commSpace (normalClosure (layerIn (G ⊓ vFix v)) L) ⊤) →+
      (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2),
    Function.Surjective β ∧
    β.ker = ((fixedSpace (normalClosure (layerIn (G ⊓ vFix v)) L)).comap
      (commSpace (normalClosure (layerIn (G ⊓ vFix v)) L) ⊤).subtype).toAddSubgroup ∧
    ∀ (h : ↥H₁) (w w' : ↥(commSpace (normalClosure (layerIn (G ⊓ vFix v)) L) ⊤)),
      (w' : V) = (h : GLV V) (w : V) →
        β w' = ((ψ h : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).mulVec (β w)

@[expose] def Lemma51 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V), StdForm G L z →
      CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1 →
      ∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 → ¬ IsSubnormal L (G ⊓ vFix v) →
        (∃ (H₁ : Subgroup (GLV V)) (n : ℕ) (ψ : ↥H₁ ≃* Equiv.Perm (Fin (n + 2))),
            CaseIData G L z v H₁ n ψ) ∨
          ∃ (H₁ : Subgroup (GLV V)) (ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)),
            CaseIIData G L z v H₁ ψ

@[expose] def BranchAFalse : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V), StdForm G L z →
      CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1 →
      (∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 →
        G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))) → False

structure OddTranspConf (G L : Subgroup (GLV V)) (z : GLV V) : Prop where
  std : StdForm G L z
  rank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1
  branchA : ∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 →
    G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))
  oddTransp : ∀ g ∈ G, ∀ h ∈ G, orderOf ((g * z * g⁻¹) * (h * z * h⁻¹)) ≤ 2 ∨
    Odd (orderOf ((g * z * g⁻¹) * (h * z * h⁻¹)))
  gen : G = Subgroup.closure {x | ∃ g ∈ G, x = g * z * g⁻¹}
  derived : ⁅G, G⁆ = layerIn G

@[expose] def Lemma52 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V), StdForm G L z →
      CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1 →
      (∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 →
        G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))) → OddTranspConf G L z

@[expose] def BranchAAlt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V), OddTranspConf G L z →
      (∃ n : ℕ, 7 ≤ n ∧ IsAltNaturalModule L n) ∨ IsA7FourModule L ∨ IsOmegaPlusModule L 3 →
        False

@[expose] def BranchASmall : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V), OddTranspConf G L z →
      IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3 ∨
        IsA6Z3Module L → False

@[expose] def CaseIFalse : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V) (v : V) (H₁ : Subgroup (GLV V)) (n : ℕ) (ψ : ↥H₁ ≃* Equiv.Perm (Fin (n + 2))),
    StdForm G L z → CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1 →
      v ∈ commSpace (Subgroup.zpowers z) ⊤ → CaseIData G L z v H₁ n ψ → False

@[expose] def CaseIIFalse : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (z : GLV V) (v : V) (H₁ : Subgroup (GLV V)) (ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)),
    StdForm G L z → CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1 →
      v ∈ commSpace (Subgroup.zpowers z) ⊤ → CaseIIData G L z v H₁ ψ → False

end CFSG.CGT.Foote82
