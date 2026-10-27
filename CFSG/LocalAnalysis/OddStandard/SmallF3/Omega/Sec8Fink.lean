module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8E (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B E : Subgroup G) : Prop where
  ctx : Sec8Ctx G t L S z g B
  le_N : E ≤ Nsub8 t B
  elem : IsElemAb2 E 8
  t_norm : ∀ e ∈ E, t * e * t⁻¹ ∈ E
  cent_t : E ⊓ centralizer ({t} : Set G) = B
  comm_le : ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ B
  comm_onto : ∀ b ∈ B, ∃ e ∈ E, e * t * e⁻¹ * t⁻¹ = b
  decomp : Nsub8 t B = E ⊔ (Nsub8 t B ⊓ centralizer ({t} : Set G))
  normal : ((E ⊔ oddCoreIn (Nsub8 t B)).subgroupOf (Nsub8 t B)).Normal

@[expose] def Asc82FinkE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B → ∃ E : Subgroup G, Sec8E G t L S z g B E

@[expose] def Asc82FinkCE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec8E G t L S z g B E →
      centralizer (E : Set G) = E ⊔ oddCoreIn (normalizer (E : Set G)) ∧
        oddCoreIn (normalizer (E : Set G)) ≤ centralizer (E : Set G)

@[expose] def Asc82FinkCX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec8E G t L S z g B E → ∀ x ∈ normalizer (E : Set G),
      x * t * x⁻¹ * t⁻¹ ∈ centralizer (E : Set G) →
        ∃ c ∈ centralizer (E : Set G), (x * c) * t = t * (x * c)

@[expose] def Asc82FinkAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec8E G t L S z g B E →
      QuotEquivTo (normalizer (E : Set G) ⊓ centralizer ({t} : Set G) ⊔ centralizer (E : Set G))
          (zpowers t ⊔ centralizer (E : Set G)) ↥(autIn (centralizer ({t} : Set G)) B) ∧
        (Nonempty (↥(autIn (centralizer ({t} : Set G)) B) ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (↥(autIn (centralizer ({t} : Set G)) B) ≃* Equiv.Perm (Fin 6)))

@[expose] def Asc82FinkSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec8E G t L S z g B E → IsSylow2Of (zpowers t ⊔ E) (centralizer (B : Set G))

@[expose] def Asc82Lemma88a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec8E G t L S z g B E → ∀ y : G, orderOf y = 2 → y ∈ centralizer ({t} : Set G) →
      y ∉ conjClassIn L z → CFSG.Open.pRank 2 (E ⊓ centralizer ({y} : Set G)) < 6

@[expose] def Asc82Lemma88b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
    Sec8E G t L S z g B E → ∀ s : G, IsConj t s →
      ∀ y ∈ E ⊓ centralizer ({s} : Set G), y ≠ 1 → IsConj z y

@[expose] def Asc82Lemma89 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B →
      Nonempty (↥(autIn (centralizer ({t} : Set G)) B) ≃* alternatingGroup (Fin 6))

structure Sec8X (G : Type) [Group G] [Finite G] (t : G) (E X1 X2 : Subgroup G) : Prop where
  c_le1 : centralizer (E : Set G) ≤ X1
  c_le2 : centralizer (E : Set G) ≤ X2
  le1 : X1 ≤ normalizer (E : Set G)
  le2 : X2 ≤ normalizer (E : Set G)
  comm : ∀ a ∈ X1, ∀ b ∈ X2, a * b * a⁻¹ * b⁻¹ ∈ centralizer (E : Set G)
  inf : X1 ⊓ X2 ≤ centralizer (E : Set G)
  sup : X1 ⊔ X2 ⊔ zpowers t = normalizer (E : Set G)
  t_not : t ∉ X1 ⊔ X2
  swap1 : ∀ a ∈ X1, t * a * t⁻¹ ∈ X2
  swap2 : ∀ a ∈ X2, t * a * t⁻¹ ∈ X1
  quot1 : QuotEquivTo X1 (centralizer (E : Set G)) (alternatingGroup (Fin 6))
  quot2 : QuotEquivTo X2 (centralizer (E : Set G)) (alternatingGroup (Fin 6))

structure Sec8XO (G : Type) [Group G] [Finite G] (t : G) (E Y1 Y2 : Subgroup G) : Prop where
  o_le1 : oddCoreIn (normalizer (E : Set G)) ≤ Y1
  o_le2 : oddCoreIn (normalizer (E : Set G)) ≤ Y2
  le1 : Y1 ≤ normalizer (E : Set G)
  le2 : Y2 ≤ normalizer (E : Set G)
  comm : ∀ a ∈ Y1, ∀ b ∈ Y2, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G))
  inf : Y1 ⊓ Y2 ≤ oddCoreIn (normalizer (E : Set G))
  sup : Y1 ⊔ Y2 ⊔ zpowers t = normalizer (E : Set G)
  t_not : t ∉ Y1 ⊔ Y2
  swap1 : ∀ a ∈ Y1, t * a * t⁻¹ ∈ Y2
  swap2 : ∀ a ∈ Y2, t * a * t⁻¹ ∈ Y1
  E_sup : E = (E ⊓ Y1) ⊔ (E ⊓ Y2)
  e16_1 : IsElemAb2 (E ⊓ Y1) 4
  e16_2 : IsElemAb2 (E ⊓ Y2) 4
  quot1 : QuotEquivTo Y1 ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) (alternatingGroup (Fin 6))
  quot2 : QuotEquivTo Y2 ((E ⊓ Y2) ⊔ oddCoreIn (normalizer (E : Set G))) (alternatingGroup (Fin 6))
  cent1 : Y1 ⊓ centralizer ((E ⊓ Y1 : Subgroup G) : Set G) ≤
    (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))
  cent2 : Y2 ⊓ centralizer ((E ⊓ Y2 : Subgroup G) : Set G) ≤
    (E ⊓ Y2) ⊔ oddCoreIn (normalizer (E : Set G))
  trans1 : ∀ v ∈ E ⊓ Y1, v ≠ 1 → ∀ w ∈ E ⊓ Y1, w ≠ 1 → ∃ y ∈ Y1, y * v * y⁻¹ = w
  trans2 : ∀ v ∈ E ⊓ Y2, v ≠ 1 → ∀ w ∈ E ⊓ Y2, w ≠ 1 → ∃ y ∈ Y2, y * v * y⁻¹ = w
  split1 : ∃ H : Subgroup G, H ≤ Y1 ∧ H ⊓ ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) ≤
    oddCoreIn (normalizer (E : Set G)) ∧ H ⊔ ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) = Y1
  split2 : ∃ H : Subgroup G, H ≤ Y2 ∧ H ⊓ ((E ⊓ Y2) ⊔ oddCoreIn (normalizer (E : Set G))) ≤
    oddCoreIn (normalizer (E : Set G)) ∧ H ⊔ ((E ⊓ Y2) ⊔ oddCoreIn (normalizer (E : Set G))) = Y2

end CFSG.OddStandard.SmallF3.Omega
