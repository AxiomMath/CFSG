module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bRows
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def CFProp23Row516 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∉ h.K ⊔ coreActionKernel h.K →
    ∀ z : H, z ∈ h.D → (∀ s ∈ h.S, s * z = z * s) → orderOf z = 2 →
      ∃ g ∈ h.W, ∃ y ∈ h.B ⊓ (Open.fusionZStar ↥h.K).map h.K.subtype,
        g⁻¹ * h.a * g = h.a * z * y

@[expose] def CFAutL2Stab : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p (2 * f) → ∀ t : Y, orderOf t = 2 →
      Group.IsSolvable ↥(MulAction.stabilizer (MulAut Y) t) ∧
        (p ^ f = 3 → IsPGroup 2 ↥(MulAction.stabilizer (MulAut Y) t))

@[expose] def CF516Cent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Nat.card (center Y) = 2 →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    (Blueprint.LieModel (Y ⧸ center Y) .PSL 4 p f ∨
      Blueprint.LieModel (Y ⧸ center Y) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (Y ⧸ center Y) .POmegaMinus 4 p e) →
    ∀ α : MulAut Y, α ^ 2 = 1 →
      ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧
        (⁅N, N⁆ = N ∨ (p ^ f = 3 ∧ N ≤ closure {y : Y | α y = y ∧ Odd (orderOf y)})) ∧
        (center Y ≤ N ∨
          (∃ A : Subgroup Y, A ≤ N ∧ (∀ u ∈ A, ∀ v ∈ A, u * v = v * u) ∧ Nat.card A = 8 ∧
            ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2) ∨
          ((∀ t : Y, α ≠ MulAut.conj t) ∧ 4 ∣ Nat.card N))

@[expose] noncomputable def centralizerCore516 {Y : Type*} [Group Y] (q : ℕ) (ℓ : Y) :
    Subgroup Y :=
  if q = 3 then closure {y : Y | y ∈ centralizer ({ℓ} : Set Y) ∧ Odd (orderOf y)}
  else Quasithin.perfectCore (centralizer ({ℓ} : Set Y))

@[expose] def CFRow516InnerCenter : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → center (OddBar h.K) = ⊥

@[expose] def CFRow516InnerFusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ z : H, z ∈ h.D → (∀ s ∈ h.S, s * z = z * s) → orderOf z = 2 →
      ∀ a₁ ∈ h.P ⊓ h.K, orderOf a₁ = 2 → ∃ g ∈ h.K, g⁻¹ * a₁ * g = z

@[expose] def CFRow516InnerT : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → h.T ≤ h.K ⊔ h.B ∧ IsCyclic ↥(h.T ⊓ h.K)

@[expose] def CFRow516InnerOut : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ u v : MulAut (OddBar h.K),
      ⁅u, v⁆ ∈ (MulAut.conj : OddBar h.K →* MulAut (OddBar h.K)).range

@[expose] def CFRow516InnerPSp : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) →
    ∀ ℓ : OddBar h.K, ℓ ^ 2 = 1 →
      pPrimeCore 2 ↥(centralizerCore516 (p ^ f) ℓ) = ⊥ ∧
      ∀ ε : MulAut (OddBar h.K), ε ^ 2 = 1 → ε ≠ 1 → ε ≠ MulAut.conj ℓ →
        ε * MulAut.conj ℓ = MulAut.conj ℓ * ε → (∀ y ∈ centralizerCore516 (p ^ f) ℓ, ε y = y) →
        ∃ M : Subgroup (OddBar h.K), (∀ y ∈ M, ε y = y) ∧ Blueprint.LieModel ↥M .PSp 2 p f

@[expose] def CFRow516NoPSp : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) →
    ∀ w : H, ∀ hw : w ∈ normalizer (h.K : Set H), w ∈ h.W → w * w = 1 →
      oddBarConj h.K ⟨w, hw⟩ ≠ 1 →
      ¬ ∃ M : Subgroup (OddBar h.K), (∀ y ∈ M, oddBarConj h.K ⟨w, hw⟩ y = y) ∧
        Blueprint.LieModel ↥M .PSp 2 p f

@[expose] def CFL2InvPair : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p (2 * f) → ∀ t : Y, orderOf t = 2 →
      ∃ u : Y, orderOf u = 2 ∧ u ≠ t ∧ u * t = t * u

end CFSG.ComponentClassification.GSThmB
