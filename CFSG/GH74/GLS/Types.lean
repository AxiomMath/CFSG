module

public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank
open scoped commutatorElement

section Induced

variable {G : Type*} [Group G]

@[expose] noncomputable def inducedQuotAut (K : Subgroup G) (N : Subgroup ↥K) [N.Characteristic]
    (x : normalizer (K : Set G)) : MulAut (↥K ⧸ N) :=
  QuotientGroup.congr N N (K.normalizerMonoidHom x)
    (Subgroup.characteristic_iff_map_eq.mp ‹N.Characteristic› _)

@[expose] def InducesUnitaryAut (y : G) (K : Subgroup G) : Prop :=
  ∃ hy : y ∈ normalizer (K : Set G), ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥(MonoidHom.eqLocus (inducedQuotAut K (center ↥K) ⟨y, hy⟩).toMonoidHom
      (MonoidHom.id _)) ≃* StatedProj (StatedSU 3 2 F))

@[expose] def HasElemAbelianSylowTwo (H : Subgroup G) (n : ℕ) : Prop :=
  ∃ P : Sylow 2 ↥H, IsElementaryAbelian 2 ↥(P : Subgroup ↥H) ∧ Nat.card ↥(P : Subgroup ↥H) = 2 ^ n

end Induced

@[expose] def IsEvenType (G : Type) [Group G] : Prop :=
  L2Sub G InC2 ∧
    (∀ x : G, orderOf x = 2 → pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) ∧
    3 ≤ pRank 2 G

@[expose] def IsSmallOddType (G : Type) [Group G] : Prop :=
  ¬ IsEvenType G ∧ ¬ L2Meets G InG2

@[expose] def IsRestrictedEvenType (G : Type) [Group G] : Prop :=
  IsEvenType G ∧
    (∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel ↥K .PSL 2 p f →
        (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 17) ∧ 4 ≤ pRank 2 G) ∧
    (∀ (x : G) (K : Subgroup G), IsTerminalPair 2 x K →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel ↥K .PSL 2 p f →
        4 ≤ pRank 2 ↥(centralizer ({x} : Set G)) ∧ ¬ IsCentralInvolution x ∧
          ((p ^ f = 5 ∧ HasElemAbelianSylowTwo (normalizer (K : Set G)) 4) ∨
            (p ^ f = 9 ∧ pRank 2 ↥(centralizer (K : Set G)) = 1))) ∧
    (∀ (x y : G) (K : Subgroup G), orderOf x = 2 → orderOf y = 2 → x * y = y * x →
      IsTerminalPair 2 x K → IsL34Quotient ↥K → InducesUnitaryAut y K →
        4 ≤ 2 ^ ((normalizer (K : Set G)).index.factorization 2))

@[expose] def IsSpecialOddType (G : Type) [Group G] : Prop :=
  ¬ IsRestrictedEvenType G ∧ ¬ L2Meets G InG2

@[expose] def IsLB2Type (G : Type) [Group G] : Prop :=
  L2Sub G (fun K _ => InC2 K ∨ InT2 K) ∧ (L2Meets G InB2 ∨ pRank 2 G ≤ 3) ∧
    ¬ IsRestrictedEvenType G

@[expose] def IsLT2Type (G : Type) [Group G] : Prop :=
  Even (Nat.card G) ∧ IsSpecialOddType G ∧ ¬ IsLB2Type G

@[expose] def IsLT2oType (G : Type) [Group G] : Prop :=
  4 ≤ pRank 2 G ∧ L2Sub G (fun K _ => InC2 K ∨ InU2 K)

@[expose] def HasTwoThinConfiguration (G : Type) [Group G] : Prop :=
  ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ InB2 (↥K ⧸ pPrimeCore 2 ↥K)

@[expose] def IsLBStar2Type (G : Type) [Group G] : Prop :=
  pRank 2 G = 2 ∨
    (pRank 2 G ≤ 3 ∧ L2Meets G (fun K _ =>
      Nonempty (K ≃* alternatingGroup (Fin 7)) ∨ HasL2Model K (fun q => Odd q ∧ 3 < q))) ∨
    HasTwoThinConfiguration G

theorem IsRestrictedEvenType.isEvenType {G : Type} [Group G] (h : IsRestrictedEvenType G) :
    IsEvenType G := h.1

theorem IsLB2Type.isSpecialOddType {G : Type} [Group G] (h : IsLB2Type G) : IsSpecialOddType G :=
  ⟨h.2.2, fun ⟨x, hx, K, hK, hG⟩ => ((h.1 x hx K hK).elim hG.2.1 hG.2.2)⟩

theorem IsLT2Type.isSpecialOddType {G : Type} [Group G] (h : IsLT2Type G) : IsSpecialOddType G :=
  h.2.1

section Uniqueness

variable {G : Type*} [Group G]

@[expose] def gammaK (p : ℕ) (P : Subgroup G) (k : ℕ) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ P) (_ : k ≤ pRank p ↥Q), normalizer (Q : Set G)

@[expose] def gammaO (p : ℕ) (P : Subgroup G) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ P) (_ : 2 ≤ pRank p ↥Q)
    (_ : 3 ≤ pRank p ↥(Q ⊔ (centralizer (Q : Set G) ⊓ P))), normalizer (Q : Set G)

@[expose] def IsTwoUniquenessSubgroup (Y : Subgroup G) : Prop :=
  Y ≠ ⊤ ∧ ∃ S : Sylow 2 G,
    (3 ≤ pRank 2 ↥(S : Subgroup G) → gammaO 2 (S : Subgroup G) ≤ Y) ∧
    (pRank 2 ↥(S : Subgroup G) = 2 → gammaK 2 (S : Subgroup G) 1 ≤ Y)

@[expose] def HasTwoUniquenessSubgroup (G : Type*) [Group G] : Prop :=
  ∃ Y : Subgroup G, IsTwoUniquenessSubgroup Y

end Uniqueness

end CFSG.GH74.GLS
