module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma101 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec10Setting G t L → InCStar L

@[expose] def Asc82Lemma102 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec10Setting G t L →
    ∀ P : Sylow 2 (centralizer (L : Set G)), IsCyclic (P : Subgroup (centralizer (L : Set G)))

@[expose] def Asc82Lemma103 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec10Z G t L S z →
    omega1 (centerIn S) = zpowers z ⊔ zpowers t

@[expose] def Asc82Lemma10K0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      secK0 t z = oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2 ∧
        secK0 t z = oTwoRes (centralizer ({z, t} : Set G))

@[expose] def Asc82Lemma104 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → IsStrClosedModZ t z (secW t K1 K2) →
      ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ hatCent t z →
        h⁻¹ * t * h ∈ normalizer ((K1 ⊔ oddCoreIn (secK0 t z) : Subgroup G) : Set G)

@[expose] def Asc82Lemma105 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → ∃ g : G, g⁻¹ * t * g = t * z

@[expose] def Asc82Lemma106 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → centralizer (L : Set G) ⊓ S = zpowers t

end CFSG.OddStandard.SmallF3.Omega
