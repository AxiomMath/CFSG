module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4AData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82SetU {G : Type} [Group G] (D : Subgroup G) (v : G) : Prop :=
  v ∈ D ∧ orderOf v = 2 ∧ ∃ K : Subgroup G,
    IsComponentIn K (D ⊓ centralizer ({v} : Set G)) ∧ LieModel (K ⧸ oddCore K) .PSp 2 3 1

@[expose] def Asc82FactD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ s : G, orderOf s = 2 → InducesTypeSome L s 7 1 6 1 →
      let D := L ⊓ centralizer ({s} : Set G)
      (∀ v, Asc82SetU D v → InducesTypeSome L v 7 1 2 (-1) ∨ InducesTypeSome L v 7 1 6 (-1)) ∧
      (∀ v v', Asc82SetU D v → Asc82SetU D v' →
        ((InducesTypeSome L v 7 1 2 (-1) ∧ InducesTypeSome L v' 7 1 2 (-1)) ∨
          (InducesTypeSome L v 7 1 6 (-1) ∧ InducesTypeSome L v' 7 1 6 (-1))) →
        v' ∈ conjClassIn D v) ∧
      (∃ v, Asc82SetU D v ∧ InducesTypeSome L v 7 1 2 (-1)) ∧
      (∃ v, Asc82SetU D v ∧ InducesTypeSome L v 7 1 6 (-1)) ∧
      (∀ v, Asc82SetU D v → InducesTypeSome L v 7 1 2 (-1) → s * v ∈ conjClassIn L s)

@[expose] def Sec4FDConcl {G : Type} [Group G] (L : Subgroup G) (s : G) (D : Subgroup G) : Prop :=
  (∀ v, Asc82SetU D v → InducesTypeSome L v 7 1 2 (-1) ∨ InducesTypeSome L v 7 1 6 (-1)) ∧
  (∀ v v', Asc82SetU D v → Asc82SetU D v' →
    ((InducesTypeSome L v 7 1 2 (-1) ∧ InducesTypeSome L v' 7 1 2 (-1)) ∨
      (InducesTypeSome L v 7 1 6 (-1) ∧ InducesTypeSome L v' 7 1 6 (-1))) →
    v' ∈ conjClassIn D v) ∧
  (∃ v, Asc82SetU D v ∧ InducesTypeSome L v 7 1 2 (-1)) ∧
  (∃ v, Asc82SetU D v ∧ InducesTypeSome L v 7 1 6 (-1)) ∧
  (∀ v, Asc82SetU D v → InducesTypeSome L v 7 1 2 (-1) → s * v ∈ conjClassIn L s)

theorem Asc82FactD.apply (hD : Asc82FactD) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsOmega7Group L) {s : G} (hs : orderOf s = 2) (h6 : InducesTypeSome L s 7 1 6 1) :
    Sec4FDConcl L s (L ⊓ centralizer ({s} : Set G)) :=
  hD G L hL s hs h6

@[expose] def Asc82FactMono : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P B : Subgroup G) (φ : (Fin 7 → ZMod 2) → G),
    IsOmega7Group L → Sec4BData L P B φ →
    ∀ (μ : G) (i j : Fin 7), i ≠ j → orderOf μ = 2 → μ ∈ normalizer (L : Set G) →
      InducesTypeSome L μ 7 1 6 1 →
      (∀ v, IsEvenVec v → μ * φ v * μ⁻¹ = φ (permVec (Equiv.swap i j) v)) →
      ∀ v, IsEvenVec v → μ * φ v = φ v * μ → InducesTypeSome L (μ * φ v) 7 1 6 1 →
        v = 0 ∨ v = Pi.single i 1 + Pi.single j 1

@[expose] def Asc82FactSixSix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ (a b : G) (α β : ℤˣ), a * b = b * a → InducesTypeSome L a 7 1 6 α →
      InducesTypeSome L b 7 1 6 β →
      ∀ w c : G, IsI4PlusIn L w → c ∈ centralizer (L : Set G) → a * b ≠ w * c

@[expose] def Asc82ClaimsABC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      InducesTypeSome L (g⁻¹ * t * g) 7 1 6 1 →
        InducesTypeSome (CFSG.conjugate L g) t 7 1 6 1 ∧
          L ⊓ centralizer ({g⁻¹ * t * g} : Set G) ≤ (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd L ∧
          CFSG.conjugate L g ⊓ centralizer ({t} : Set G) ≤
            (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd (CFSG.conjugate L g)

structure Sec4FInputs : Prop where
  h36 : Asc82Lemma36
  h39 : Asc82Lemma39
  h42 : Asc82Lemma42
  h43 : Asc82Lemma43
  h46b : Asc82Lemma46b
  hAD : Asc82ADataExists
  hf43c : Asc82Fact43Class
  hf6 : Asc82Fact6Class
  hf214 : Asc82Fact214
  hin6 : Asc82FactInner6
  hk6 : Asc82FactK6
  hcB : Asc82FactCentB
  hD : Asc82FactD
  hMono : Asc82FactMono
  h66 : Asc82FactSixSix
  hABC : Asc82ClaimsABC

end CFSG.OddStandard.SmallF3.Omega
