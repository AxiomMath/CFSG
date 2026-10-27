module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def blockQ (L : Subgroup G) : Subgroup G := pCoreOf 2 L

@[expose] def blockU (L : Subgroup G) : Subgroup G := ⁅blockQ L, L⁆

@[expose] def blockZ (L : Subgroup G) : Subgroup G :=
  blockU L ⊓ Subgroup.centralizer (L : Set G)

@[expose] def IsShort2 (L : Subgroup G) : Prop :=
  (∀ (N : Subgroup L) [N.Normal], IsPGroup 2 (L ⧸ N) → N = ⊤) ∧
  CharTwo L ∧
  (blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) ∧
    ∀ x ∈ blockU L, x ^ 2 = 1) ∧
  (CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) ∨ Nat.card (L ⧸ CFSG.pCore 2 L) = 3) ∧
  (blockZ L < blockU L ∧
    ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L → L ≤ Subgroup.normalizer (W : Set G) →
      W = blockZ L ∨ W = blockU L)

@[expose] def IsBlock2 (X L : Subgroup G) : Prop :=
  IsShort2 L ∧ L ≤ X ∧ (L.subgroupOf X).IsSubnormal

@[expose] def IsLin2Type (L : Subgroup G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ α : L →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
    ∃ β : blockU L →* Multiplicative (Fin 2 → F),
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ ℓ : L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) =
          (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

@[expose] def evenWeight (m : ℕ) : AddSubgroup (Fin m → ZMod 2) :=
  (AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i)
    (fun _ _ => Finset.sum_add_distrib)).ker

@[expose] def IsAltType (L : Subgroup G) (m : ℕ) : Prop :=
  ∃ α : L →* alternatingGroup (Fin m),
    Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
  ∃ β : blockU L →* Multiplicative (evenWeight m),
    Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ ℓ : L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin m,
      ((Multiplicative.toAdd (β v) : evenWeight m) : Fin m → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight m) : Fin m → ZMod 2)
          ((α ℓ : Equiv.Perm (Fin m))⁻¹ i)

@[expose] def IsChi0Block (X L : Subgroup G) : Prop :=
  IsBlock2 X L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3 ∨ IsAltType L 5)

end CFSG.QuasithinUnique
