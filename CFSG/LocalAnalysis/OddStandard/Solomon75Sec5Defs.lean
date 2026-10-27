module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Final
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Equiv

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Basic

variable {X : Type} [Group X]

@[expose] def CentModOdd (A : Subgroup X) (c : X) : Prop := ∀ a ∈ A, ⁅a, c⁆ ∈ oddCoreOf A

@[expose] def QOf (A : Subgroup X) : Subgroup X := centralizerSection A (pPrimeCoreOf 2 A)

theorem mem_normalizer_oddCoreOf_of_mem_normalizer {A : Subgroup X} {c : X}
    (hc : c ∈ normalizer (A : Set X)) : c ∈ normalizer (oddCoreOf A : Set X) := by
  apply mem_normalizer_of_map_conj_eq
  have h := pPrimeCoreOf_map_mulEquiv (MulAut.conj c) A
  rw [map_conj_eq_of_mem_normalizer hc] at h
  exact h.symm

theorem mem_QOf_iff {A : Subgroup X} {c : X} :
    c ∈ QOf A ↔ c ∈ normalizer (A : Set X) ∧ CentModOdd A c :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, mem_normalizer_oddCoreOf_of_mem_normalizer h.1, h.2⟩⟩

end Basic

@[expose] def Sec5Comp (X : Type) [Group X] (n : ℕ) (H A : Subgroup X) : Prop :=
  (∃ u, IsIntrinsicIn X H A u) ∧ IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n

theorem K0_eq_sSup_sec5Comp (X : Type) [Group X] (n : ℕ) (H : Subgroup X) :
    K0 X n H = sSup {A : Subgroup X | Sec5Comp X n H A} := rfl

structure IsSec5Inv (X : Type) [Group X] (Z : Subgroup X) (s : X) : Prop where
  mem : s ∈ normalizer (Z : Set X)
  notMem : s ∉ Z
  sq : s * s = 1
  conj : ∃ g : X, g⁻¹ * s * g ∈ Z ∧ g⁻¹ * s * g ≠ 1

structure Sec5Data (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))) : Prop where
  cex : SolCEx X
  hypA : HypA X
  maxdeg : IsMaxAhatDeg X n
  pair : IsSec5Pair X n z Z
  l52 : Lemma52 X n Z S

abbrev Sec5Syl {X : Type} [Group X] {Z : Subgroup X} (S : Sylow 2 ↥(normalizer (Z : Set X))) :
    Subgroup X :=
  (S : Subgroup ↥(normalizer (Z : Set X))).map (normalizer (Z : Set X)).subtype

section Model

variable {X : Type} [Group X]

@[expose] noncomputable def conjAut {A : Subgroup X} {c : X}
    (hc : c ∈ normalizer (A : Set X)) : ↥A ≃* ↥A :=
  (Subgroup.equivMapOfInjective A (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer hc))

theorem coe_conjAut {A : Subgroup X} {c : X} (hc : c ∈ normalizer (A : Set X)) (a : ↥A) :
    ((conjAut hc a : ↥A) : X) = c * (a : X) * c⁻¹ := rfl

@[expose] noncomputable def quotConj {A : Subgroup X} {c : X} (hc : c ∈ normalizer (A : Set X)) :
    (↥A ⧸ pPrimeCore 2 ↥A) ≃* (↥A ⧸ pPrimeCore 2 ↥A) :=
  QuotientGroup.congr (pPrimeCore 2 ↥A) (pPrimeCore 2 ↥A) (conjAut hc)
    (pPrimeCore_map_iso 2 (conjAut hc))

structure AhatModel (X : Type) [Group X] (n : ℕ) (A : Subgroup X) where
  K : Type
  [grp : Group K]
  e : ↥A ⧸ pPrimeCore 2 ↥A ≃* K
  C : AhatData.CoverSetup n K

attribute [instance] AhatModel.grp

variable {n : ℕ} {A : Subgroup X}

@[expose] noncomputable def AhatModel.autOf (M : AhatModel X n A) (c : X)
    (hc : c ∈ normalizer (A : Set X)) : MulAut M.K :=
  (M.e.symm.trans (quotConj hc)).trans M.e

open Classical in
@[expose] noncomputable def AhatModel.perm (M : AhatModel X n A) (c : X)
    (hc : c ∈ normalizer (A : Set X)) : Perm (Fin n) :=
  if h : ∃ σ, M.C.Induces (M.autOf c hc) σ then h.choose else 1

end Model

@[expose] def fixCount {n : ℕ} (σ : Perm (Fin n)) : ℕ := (Finset.univ.filter fun i => σ i = i).card

@[expose] def transCount {n : ℕ} (σ : Perm (Fin n)) : ℕ := σ.support.card / 2

@[expose] def Solomon75Frac53 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → ∀ s, IsSec5Inv X Z s →
      (∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → ∀ hs : s ∈ normalizer (A : Set X),
          ∀ M : AhatModel X n A,
            fixCount (M.perm s hs) ≤ 3 ∧ transCount (M.perm s hs) ≠ 3) ∧
      (∀ A A', Sec5Comp X n (normalizer (Z : Set X)) A → Sec5Comp X n (normalizer (Z : Set X)) A' →
        A ≠ A' → A.map (MulAut.conj s).toMonoidHom = A' →
          zStar A ⊔ oddCoreOf (K0 X n (normalizer (Z : Set X))) =
            zStar A' ⊔ oddCoreOf (K0 X n (normalizer (Z : Set X))))

@[expose] def Solomon75NoSwap : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → ∀ s, IsSec5Inv X Z s →
      ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → A.map (MulAut.conj s).toMonoidHom = A

@[expose] def Solomon75TwoComp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X)
    (S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))),
    Sec5Data X n z (zpowers z) S →
      ¬ ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (centralizer ({z} : Set X)) A₁ ∧
        Sec5Comp X n (centralizer ({z} : Set X)) A₂ ∧ A₁ ≠ A₂

@[expose] def Solomon75Lemma54p : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S →
    (∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂) →
    ∀ s, IsSec5Inv X Z s → ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A →
      ∀ r ∈ A, r ≠ 1 → r * r = 1 → r * s = s * r →
        K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) = ⊥ ∧
          ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → r ∈ normalizer (B : Set X)

@[expose] def Sec5One (X : Type) [Group X] (n : ℕ) (Z : Subgroup X) : Prop :=
  ∀ A A' : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A →
    Sec5Comp X n (normalizer (Z : Set X)) A' → A = A'

@[expose] def Solomon75Lemma55 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → Sec5One X n Z

@[expose] def Solomon75Cor56 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → Sec5One X n Z →
      Z = zpowers z ∧ ∃ s₁ x : X, s₁ ∈ Sec5Syl S ∧ x ∈ Sec5Syl S ∧ orderOf s₁ = 2 ∧ s₁ ∉ Z ∧
        (∃ g : X, g⁻¹ * z * g = s₁) ∧ x * x = s₁

@[expose] def Solomon75Lemma57 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → Sec5One X n Z →
      Z = zpowers z →
        centralizer ({z} : Set X) ⊓ QOf (K0 X n (centralizer ({z} : Set X))) =
            oddCoreOf (centralizer ({z} : Set X)) ⊔ zpowers z ∧
          Nat.card ↥(centralizer ({z} : Set X) ⊓ QOf (K0 X n (centralizer ({z} : Set X)))) =
            2 * Nat.card ↥(oddCoreOf (centralizer ({z} : Set X)))

@[expose] def Solomon75Lemma58 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → Sec5One X n Z →
      Z = zpowers z → n ≤ 11

end CFSG.OddStandard.Solomon75
