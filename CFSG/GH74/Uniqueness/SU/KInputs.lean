module

public import CFSG.GH74.Uniqueness.SU.SU0GH
public import CFSG.GH74.Uniqueness.SU.SU5Models
public import CFSG.GH74.Uniqueness.SU.SU4Defs

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def IsPGL2 (X : Type*) [Group X] (p f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
    Nonempty (X ≃* Matrix.ProjGenLinGroup (Fin 2) F)

@[expose] def Psub (H : Type) [Group H] (T : Sylow 2 H) : Subgroup H :=
  (T : Subgroup H) ⊓ generalizedFitting H

@[expose] def ZP (H : Type) [Group H] (T : Sylow 2 H) : Subgroup H :=
  (Subgroup.center ↥(Psub H T)).map (Psub H T).subtype

@[expose] def J2Structure (H : Type) [Group H] (T : Sylow 2 H) : Prop :=
  SU5.IsJ2Type ↥(T : Subgroup H) ∧ SU5.IsL34Type ↥(Psub H T) ∧
    ∃ E : Subgroup H,
      normalizer ((Psub H T : Subgroup H) : Set H) = Psub H T ⊔ E ∧ Psub H T ⊓ E = ⊥ ∧
      (Nonempty (↥E ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (↥E ≃* Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) ∧
      ∃ E₀ : Subgroup H, E₀ ≤ E ∧ Nonempty (↥E₀ ≃* Equiv.Perm (Fin 3)) ∧
        E = E₀ ⊔ (centralizer ((ZP H T : Subgroup H) : Set H) ⊓ E) ∧
        E₀ ⊓ (centralizer ((ZP H T : Subgroup H) : Set H) ⊓ E) = ⊥ ∧
        (∀ a ∈ E₀, ∀ c ∈ centralizer ((ZP H T : Subgroup H) : Set H) ⊓ E, a * c = c * a) ∧
        (∀ a ∈ E₀, orderOf a = 3 → ∀ t ∈ Psub H T, a * t * a⁻¹ = t → t = 1) ∧
        (Nat.card ↥(centralizer ((ZP H T : Subgroup H) : Set H) ⊓ E) = 1 ∨
          Nat.card ↥(centralizer ((ZP H T : Subgroup H) : Set H) ⊓ E) = 3)

@[expose] def KI1 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    3 ≤ Open.twoRank H → center H = ⊥ →
    ∀ (T : Sylow 2 H) (x : H), x ∈ (T : Subgroup H) → orderOf x = 2 →
      Open.pRank 2 (centralizer ({x} : Set H)) = 2 →
        (((GLS.oPrimeResidual 2 H = generalizedFitting H ⊔ zpowers x ∧
            LieModel ↥(generalizedFitting H) .PSL 3 2 2 ∧
            9 ∣ Nat.card ↥(centralizer ({x} : Set H) ⊓ generalizedFitting H)) ∧ J2Structure H T) ∨
          (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥(generalizedFitting H) .PSL 2 p f ∧
            IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f) ∨
          (generalizedFitting H ≤ (T : Subgroup H) ∧ J2Structure H T))

@[expose] def KI2 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel ↥(generalizedFitting H) .PSL 2 p f →
      ∀ x : H, orderOf x = 2 → IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f →
        Open.pRank 2 (generalizedFitting H ⊔ zpowers x) = 2 ∧
          (∃ _ : (generalizedFitting H ⊔ zpowers x).Normal,
            IsCyclic (H ⧸ (generalizedFitting H ⊔ zpowers x))) ∧
          ∀ E₁ E₂ : Subgroup H, Open.IsElemAbelian 2 E₁ → Nat.card E₁ = 8 →
            Open.IsElemAbelian 2 E₂ → Nat.card E₂ = 8 →
              ∃ h : H, E₂ = E₁.map (MulAut.conj h).toMonoidHom

@[expose] def KI3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    LieModel ↥(generalizedFitting H) .PSL 3 2 2 →
      ∀ x ∈ generalizedFitting H, orderOf x = 2 →
        Group.IsSolvable ↥(centralizer ({x} : Set H)) ∧
          pPrimeCore 2 ↥(centralizer ({x} : Set H)) = ⊥ ∧
          SU4.IsSylowIn (generalizedFitting H)
            (centralizer ({x} : Set H) ⊓ generalizedFitting H)

@[expose] def KI4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    ∀ (S : Sylow 2 H) (R : Subgroup H), R ≤ (S : Subgroup H) → Open.IsElemAbelian 2 R →
      Nat.card R = 16 →
      (∀ r ∈ R, ∀ h : H, h⁻¹ * r * h ∈ (S : Subgroup H) → h⁻¹ * r * h ∈ R) →
      ∀ X₀ : Set H, X₀ ⊆ (R : Set H) → X₀.ncard = 5 → (∀ x ∈ X₀, orderOf x = 2) →
        Subgroup.closure X₀ = R →
        (∀ x ∈ X₀, ∀ y ∈ X₀, ∃ h : H, h⁻¹ * x * h = y) →
        (∀ x ∈ X₀, ∀ h : H, h⁻¹ * x * h ∈ R → h⁻¹ * x * h ∈ X₀) →
          ∀ (h : H), ∀ r ∈ R, h⁻¹ * r * h ∈ R

@[expose] def KI5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → center K ≠ ⊥ →
    Nonempty ((K ⧸ center K) ≃* CFSG.Theory.Comparator.SzModel 1) →
      (Nat.card (center K) = 2 ∨ Nat.card (center K) = 4) ∧
      (∀ P : Sylow 2 K,
        Subgroup.center ↥(P : Subgroup K) = (center K).subgroupOf (P : Subgroup K)) ∧
      (∀ (P : Sylow 2 K) (φ : MulAut K), (∀ g ∈ (P : Subgroup K), φ g = g) → φ = 1) ∧
      (Nat.card (center K) = 2 → ∀ φ : MulAut K, ∃ g : K, φ = MulAut.conj g) ∧
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), g ^ 2 ∈ center K → g ^ 2 = 1) ∧
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), ∀ h ∈ (P : Subgroup K),
        g ^ 2 ∈ center K → h ^ 2 ∈ center K → g * h = h * g)

@[expose] def IsSL25 (X : Type*) [Group X] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 5 ∧ Nonempty (X ≃* StatedSL 2 F)

@[expose] def IsTwoSz8 (X : Type*) [Group X] : Prop :=
  CFSG.IsQuasisimple X ∧ ∃ _ : Finite X, Nat.card (center X) = 2 ∧
    Nonempty ((X ⧸ center X) ≃* CFSG.Theory.Comparator.SzModel 1)

@[expose] def IsTwoAlt (X : Type*) [Group X] (n : ℕ) : Prop :=
  CFSG.IsQuasisimple X ∧ ∃ _ : Finite X, Nat.card (center X) = 2 ∧
    Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin n))

@[expose] def KI6 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    3 ≤ Open.twoRank H → center H ≠ ⊥ →
    ∀ (T : Sylow 2 H) (H₀ : Subgroup H), Open.properTwoGenCoreGamma (T : Subgroup H) 2 ≤ H₀ →
      H₀ ≠ ⊤ →
        ∃ K₁ : Subgroup H, IsComponent K₁ ∧ ¬ K₁ ≤ H₀ ∧
          Open.pRank 2 (centralizer (K₁ : Set H)) = 1 ∧
          (((K₁.Normal ∧ (IsSL25 ↥K₁ ∨ CFSG.BenderSuzuki.IsBenderGroup ↥K₁) ∧
              centralizer (K₁ : Set H) ≤ H₀ ∧
              Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤
                K₁ ⊔ centralizer (K₁ : Set H)) ∨
            (IsSL25 ↥K₁ ∧ ∃ K₂ : Subgroup H, IsComponent K₂ ∧ K₂ ≠ K₁ ∧ IsSL25 ↥K₂ ∧
              generalizedFitting H = K₁ ⊔ K₂ ∧
              Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤
                generalizedFitting H) ∨
            (K₁ = ⊤ ∧ IsTwoAlt ↥K₁ 9 ∧ IsTwoAlt ↥H₀ 8) ∨
            (IsTwoSz8 ↥K₁ ∧ K₁ ⊔ centralizer (K₁ : Set H) = ⊤ ∧
              Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ K₁)) ∧
            (CFSG.BenderSuzuki.IsBenderGroup ↥K₁ ∨ IsCyclic ↥(center ↥(T : Subgroup H))))

end CFSG.GH74.Uniqueness.SU.K
