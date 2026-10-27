module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asc82Lemma111N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      S.relIndex T = 2 ∧ conjClassIn T t = {t, t * z} ∧ T ≤ normalizer (secK0 t z : Set G) ∧
        ∀ x ∈ T, x ∈ centralizer (secQ K1 K2 : Set G) ↔
          ∀ k ∈ secK0 t z, x * k * x⁻¹ * k⁻¹ ∈ oddCoreIn (secK0 t z)

@[expose] def Asc82Lemma112 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      (Nonempty (↥(secMstar t S L) ≃* ↥(alternatingGroup (Fin 6))) ∧
          secCTQ K1 K2 T = zpowers t ⊔ zpowers z) ∨
        (Nonempty (↥(secMstar t S L) ≃* Equiv.Perm (Fin 6)) ∧
          ∃ r : G, orderOf r = 2 ∧ secCTQ K1 K2 T = zpowers t ⊔ zpowers r ∧
            IsD8 (secCTQ K1 K2 T) ∧
            ∃ φ : (Fin 6 → ZMod 2) → G,
              IsPermModuleMod (n := 6) (fun _ => True) ({0, fun _ => 1} : Set (Fin 6 → ZMod 2))
                φ (secA t S L) ⊥ (secM t S L) ⊤ ∧
              ∃ i j : Fin 6, i ≠ j ∧ ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap i j) v))

@[expose] def Asc82Lemma113 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R → ∃ a x : G, Sec11Ax G t L S z K1 K2 T R a x

@[expose] def Asc82Lemma114 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R → IsDihSd (secD K1 K2 R)

@[expose] def Asc82Lemma115b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      Nonempty (↥(secMstar t S L) ≃* ↥(alternatingGroup (Fin 6))) → R = T

@[expose] def Asc82Lemma115c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      R ≤ normalizer (secKD (secD K1 K2 R) : Set G) ∧
        secK0 t z = secKD (secD K1 K2 R) ⊔ oddCoreIn (secK0 t z)

@[expose] def Asc82Lemma115d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      R = T ⊔ secD K1 K2 R ∨
        ∃ x1 ∈ R, R = T ⊔ secD K1 K2 R ⊔ zpowers x1 ∧
          ⁅zpowers x1, secKiD t z K2 (secD K1 K2 R)⁆ ≤ oddCoreIn (secKD (secD K1 K2 R)) ∧
          IsOuterOn x1 (secKiD t z K1 (secD K1 K2 R)) (oddCoreIn (secKD (secD K1 K2 R))) ∧
          (∀ y ∈ secKiD t z K1 (secD K1 K2 R),
            x1 * x1 * y * (x1 * x1)⁻¹ * y⁻¹ ∈ oddCoreIn (secKD (secD K1 K2 R))) ∧
          secD K1 K2 R = zpowers t ⊔ zpowers (x1⁻¹ * t * x1)

@[expose] def Asc82Lemma116 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R → IsSylow2Of T (hatCent t z)

@[expose] def Asc82Lemma117 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      IsElemAbelianMod z (secCTQ K1 K2 T ⊔ secQ K1 K2) ∧
        JMod z T = secCTQ K1 K2 T ⊔ secQ K1 K2 ∧ JMod z R = secD K1 K2 R ⊔ secQ K1 K2

@[expose] def Asc82Lemma118 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ secD K1 K2 R ⊔ secQ K1 K2 →
        h⁻¹ * t * h ∈ secD K1 K2 R

@[expose] def Asc82Lemma119 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R → IsSylow2Of R (centralizer ({z} : Set G))

@[expose] def Asc82Lemma1110 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      (∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ R → h⁻¹ * t * h ∈ secD K1 K2 R) ∧
        IsDih2 (Subgroup.closure {s | s ∈ R ∧ ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h})

@[expose] def Asc82Lemma1111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      centralizer ({z} : Set G) ≤
        normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G)

@[expose] def Asc82Lemma1112 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      ¬ Hyp111 t S L ∧ conjClassIn (secM t S L) t = secTB t S L

end CFSG.OddStandard.SmallF3.Omega
