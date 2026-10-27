module

public import CFSG.CGT.Foote82.Setup
public import CFSG.CGT.Foote82.T66.Cited

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique

@[expose] def CaseIFooteLemma25 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (H : Subgroup (GLV V)) (N : ℕ)
    (φ : ↥H ≃* Equiv.Perm (Fin N)), 7 ≤ N →
    (∃ β : ↥(commSpace (((alternatingGroup (Fin N)).comap φ.toMonoidHom).map H.subtype) ⊤) →+
        altHeart N, Function.Surjective β ∧
      β.ker = ((fixedSpace (((alternatingGroup (Fin N)).comap φ.toMonoidHom).map H.subtype)).comap
        (commSpace (((alternatingGroup (Fin N)).comap φ.toMonoidHom).map H.subtype) ⊤).subtype
          ).toAddSubgroup ∧
      ∀ (h : ↥H) (w w' : ↥(commSpace
          (((alternatingGroup (Fin N)).comap φ.toMonoidHom).map H.subtype) ⊤)),
        (w' : V) = (h : GLV V) (w : V) → ∀ x : evenWeight N, β w = (x : altHeart N) →
          β w' = (evenWeightPerm (φ h) x : altHeart N)) →
    ∀ t₁ t₂ : ↥H, (φ t₁).IsSwap → φ t₂ * φ t₂ = 1 → Equiv.Perm.sign (φ t₂) = -1 →
      (φ t₂).IsSwap ∨ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (t₁ : GLV V)) ⊤) <
        Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (t₂ : GLV V)) ⊤)

@[expose] def CaseIG10 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P Q : Subgroup X), Nat.card X = 128 → P.index = 2 →
    Nonempty (↥P ≃* DihedralGroup 4 × DihedralGroup 4) →
    (∃ x : X, ∃ c ∈ Subgroup.center ↥P, x * (c : X) ≠ (c : X) * x) → Q.index = 2 →
    Nonempty (↥Q ≃* DihedralGroup 4 × DihedralGroup 4) →
    (Subgroup.center ↥Q).map Q.subtype = (Subgroup.center ↥P).map P.subtype

@[expose] def CaseILemma511 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (J X L : Subgroup (GLV V))
    (z : GLV V) (k : ℕ) (e : ↥L ≃* alternatingGroup (Fin k)),
    J ≤ X → (J.subgroupOf X).Normal → J.relIndex X ≤ 2 → CFSG.IsQuasisimple ↥J →
    Odd (Nat.card ↥(Subgroup.center ↥J)) →
    X ⊓ Subgroup.centralizer (J : Set (GLV V)) ≤ (Subgroup.center ↥J).map J.subtype →
    IsIrr J ⊤ → z ∈ X → orderOf z = 2 → IsComponentOf L (X ⊓ Subgroup.centralizer {z}) →
    (k = 6 ∨ k = 7) → IsAltNaturalModule L k →
    (∀ c : ↥L, ((e c : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)).IsThreeCycle →
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (c : GLV V)) ⊤) = 2) →
    ((∃ (m : ℕ) (P : Subgroup ↥J) (Q : Subgroup (Equiv.Perm (Fin m))), (m = 8 ∨ m = 9) ∧
        IsPGroup 2 P ∧ ¬ 2 ∣ P.index ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index ∧ Nonempty (↥P ≃* ↥Q)) →
      Nonempty (↥J ≃* alternatingGroup (Fin 10)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 11))) ∧
    ((∃ (m : ℕ) (P : Subgroup ↥J) (Q : Subgroup (alternatingGroup (Fin m))), (m = 8 ∨ m = 9) ∧
        IsPGroup 2 P ∧ ¬ 2 ∣ P.index ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index ∧ Nonempty (↥P ≃* ↥Q)) →
      Nonempty (↥J ≃* alternatingGroup (Fin 8)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 9)) ∨
        Nat.card ↥J = 25920)

@[expose] def CaseIG6 : Prop := SchurU42Lift

end CFSG.CGT.Foote82
