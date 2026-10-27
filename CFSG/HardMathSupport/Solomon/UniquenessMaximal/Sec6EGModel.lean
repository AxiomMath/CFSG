module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

section Defs

variable {G : Type*} [Group G]

@[expose] def autIn (B X : Subgroup G) : Subgroup (MulAut ↥B) :=
  (X.subgroupOf (Subgroup.normalizer (B : Set G))).map B.normalizerMonoidHom

@[expose] def inB (B X : Subgroup G) : Subgroup ↥B := X.subgroupOf B

variable {B : Subgroup G}

@[expose] def NWQ2 (B : Subgroup G) (Q : Subgroup (MulAut ↥B)) :
    Set (Subgroup (MulAut ↥B)) :=
  {X | X ≤ autIn B ⊤ ∧ Odd (Nat.card X) ∧ ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X}

@[expose] def centerSub (Q : Subgroup (MulAut ↥B)) : Subgroup (MulAut ↥B) :=
  (Subgroup.center ↥Q).map Q.subtype

@[expose] def conjAutW (x : MulAut ↥B) (H : Subgroup (MulAut ↥B)) : Subgroup (MulAut ↥B) :=
  H.map (MulAut.conj x⁻¹).toMonoidHom

@[expose] def imgB (x : MulAut ↥B) (S : Subgroup ↥B) : Subgroup ↥B :=
  S.map (x⁻¹ : MulAut ↥B).toMonoidHom

@[expose] def permutesAF (A F : Subgroup ↥B) (g : MulAut ↥B) : Prop :=
  (A.map g.toMonoidHom = A ∧ F.map g.toMonoidHom = F) ∨
    (A.map g.toMonoidHom = F ∧ F.map g.toMonoidHom = A)

@[expose] def commB (P : Subgroup (MulAut ↥B)) : Subgroup ↥B :=
  Subgroup.closure {y | ∃ p ∈ P, ∃ b : ↥B, y = p b * b⁻¹}

@[expose] def fixB (P : Subgroup (MulAut ↥B)) : Subgroup ↥B where
  carrier := {b | ∀ p ∈ P, p b = b}
  mul_mem' := fun {a b} ha hb p hp => by rw [map_mul, ha p hp, hb p hp]
  one_mem' := fun p _ => map_one p
  inv_mem' := fun {a} ha p hp => by rw [map_inv, ha p hp]

end Defs

section GSide

variable {G : Type*} [Group G] {B : Subgroup G}

structure GSideK (B : Subgroup G) (A F : Subgroup ↥B) (Q : Subgroup (MulAut ↥B)) : Prop where
  Q_le_W : Q ≤ autIn B ⊤
  Q_fix_A : ∀ q ∈ Q, ∀ a ∈ A, q a = a
  Q_mem_F : ∀ q ∈ Q, ∀ f ∈ F, q f ∈ F
  Q_faith_F : ∀ q ∈ Q, (∀ f ∈ F, q f = f) → q = 1
  hasKa : ∀ a ∈ A, a ≠ 1 → ∃ S : Subgroup (MulAut ↥B), S ≤ autIn B ⊤ ∧ Q ≤ S ∧
    (∀ s ∈ S, ∀ f ∈ F, s f ∈ F) ∧ (∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1) ∧
    ∀ w ∈ autIn B ⊤, (w a = a ∨ w a = a⁻¹) → ∀ s ∈ S, w * s * w⁻¹ ∈ S

@[expose] def GSideJ (B : Subgroup G) (A F : Subgroup ↥B) (Q : Subgroup (MulAut ↥B)) : Prop :=
  ∃ S : Subgroup (MulAut ↥B), S ≤ autIn B ⊤ ∧ Q ≤ S ∧
    (∀ s ∈ S, ∀ f ∈ F, s f ∈ F) ∧ (∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1) ∧
    ∀ w ∈ autIn B ⊤, (∀ a ∈ A, w a ∈ A) → ∀ s ∈ S, w * s * w⁻¹ ∈ S

end GSide

@[expose] def Lemma65 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ (b : G) (L A : Subgroup G), IsExtremalWitness B b L A →
      ∀ Q : Subgroup (MulAut ↥B), Q ≤ autIn B (jLayerOf L A) → Nonempty (Q ≃* QuaternionGroup 2) →
        (autIn B ⊤ ≤ Subgroup.normalizer (Q : Set (MulAut ↥B))) ∨
        ∃ x ∈ autIn B ⊤,
          (Q ⊓ conjAutW x Q = ⊥ ∧ ∀ q ∈ Q, ∀ q' ∈ conjAutW x Q, q * q' = q' * q) ∧
          x * x ∈ Subgroup.normalizer (Q : Set (MulAut ↥B)) ∧
          (imgB x (inB B A) = inB B (B ⊓ L) ∧ imgB x (inB B (B ⊓ L)) = inB B A) ∧
          (∀ g ∈ autIn B ⊤ ⊓ Subgroup.normalizer ((Q ⊔ conjAutW x Q : Subgroup (MulAut ↥B)) :
              Set (MulAut ↥B)), permutesAF (inB B A) (inB B (B ⊓ L)) g) ∧
          (autIn B ⊤ ≤ Subgroup.normalizer ((Q ⊔ conjAutW x Q : Subgroup (MulAut ↥B)) :
              Set (MulAut ↥B)) ∨
            ((autIn B ⊤ ⊓ Subgroup.normalizer ((Q ⊔ conjAutW x Q : Subgroup (MulAut ↥B)) :
                Set (MulAut ↥B))).relIndex (autIn B ⊤) = 5 ∧
              ∀ u v : ↥B, u ≠ 1 → v ≠ 1 → ∃ w ∈ autIn B ⊤, w u = v))

@[expose] def Lemma66 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ (b : G) (L A : Subgroup G), IsExtremalWitness B b L A →
      ∀ Q : Subgroup (MulAut ↥B), Q ≤ autIn B (jLayerOf L A) → Nonempty (Q ≃* QuaternionGroup 2) →
        ∀ P : Subgroup (MulAut ↥B), P ≤ autIn B ⊤ → IsPGroup 3 P →
          (∃ w ∈ autIn B ⊤, ∀ τ ∈ centerSub Q, ∀ p ∈ P, (w⁻¹ * p * w) * τ = τ * (w⁻¹ * p * w)) ∧
          (Nat.card P ≤ 9 ∧ IsElemAbelian 3 P) ∧
          (∀ y ∈ commB P, ∀ p ∈ P, p y = y) ∧
          ((fixB P).index = Nat.card (commB P) ∧ (Nat.card P = 9 → Nat.card (commB P) = 9)) ∧
          ((∀ τ ∈ centerSub Q, ∀ p ∈ P, p * τ = τ * p) → Nat.card (commB P) = 3 →
            ((commB P ≤ inB B (B ⊓ L) ∧ inB B A ≤ fixB P) ∨
              (commB P ≤ inB B A ∧ inB B (B ⊓ L) ≤ fixB P)))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
