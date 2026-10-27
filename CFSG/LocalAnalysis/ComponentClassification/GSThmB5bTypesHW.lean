module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasicHW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

@[expose] def Table54 : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧ Nonempty (OddBar h.J ≃* alternatingGroup (Fin n)) ∧
      ((conjugate h.K h.a = h.K ∧ (Nonempty (OddBar h.K ≃* alternatingGroup (Fin (n + 2))) ∨
          Nonempty (OddBar h.K ≃* alternatingGroup (Fin (n + 4))))) ∨
        (conjugate h.K h.a ≠ h.K ∧ Nat.card (center (OddBar h.K)) = 2 ∧
          Nonempty (ZStarBar h.K ≃* alternatingGroup (Fin n))))) ∨
  ((Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1) ∧
      conjugate h.K h.a = h.K ∧ center (OddBar h.K) ≠ ⊥ ∧
      Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2) ∨
  (Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2 ∧ conjugate h.K h.a = h.K ∧
      center (OddBar h.K) ≠ ⊥ ∧ Nonempty (ZStarBar h.K ≃* Blueprint.NativeSporadic.Suz)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
        Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
        ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p f ∧ conjugate h.K h.a = h.K ∧
      Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p f ∧ conjugate h.K h.a ≠ h.K ∧
      Nat.card (center (OddBar h.K)) = 2 ∧ Blueprint.LieModel (ZStarBar h.K) .PSL 2 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ Blueprint.LieModel (OddBar h.K) .PSp 2 p f)

@[expose] def Row516 : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
    conjugate h.K h.a = h.K ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)

end Hyp52W

@[expose] def ConjFixStatementHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H) (g : H), g ∈ h.W →
    g⁻¹ * h.a * g ∈ h.S → g⁻¹ * h.a * g ∉ h.P →
    h.B = h.P ⊓ centralizer ({g⁻¹ * h.a * g} : Set H) ⊓ coreActionKernel (conjugate h.J g) ∧
      g⁻¹ * h.a * g ∉ closure ((h.D : Set H) ∪ {h.a}) ⊓ centralizer ({h.x} : Set H)

@[expose] def SylowKernelStatementHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.B ≤ coreActionKernel h.V ∧
    ∃ R : Sylow 2 ↥(coreActionKernel h.V),
      (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V)

@[expose] def EmbedsTQuotStatementHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59W H),
    ∃ f : ↥h.B →* ↥h.T ⧸ h.B.subgroupOf h.T, Function.Injective f

@[expose] def Row516InnerStatementHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → False

@[expose] def Row516CentralizerStatementHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → IsCyclic h.B → ∀ b ∈ h.B, orderOf b = 2 →
      h.a * b ∈ h.K → centralizer ({b} : Set H) ≠ ⊤ →
      ∃ L : Subgroup H, h.K ≤ L ∧ L ≤ h.K ⊔ oddCoreIn (centralizer ({b} : Set H)) ∧
        L ≤ centralizer ({b} : Set H) ∧ IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set H)))

@[expose] def CFRow516InnerCenterHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → center (OddBar h.K) = ⊥

@[expose] def CFRow516InnerFusionHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ z : H, z ∈ h.D → (∀ s ∈ h.S, s * z = z * s) → orderOf z = 2 →
      ∀ a₁ ∈ h.P ⊓ h.K, orderOf a₁ = 2 → ∃ g ∈ h.K, g⁻¹ * a₁ * g = z

@[expose] def CFRow516InnerTHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → h.T ≤ h.K ⊔ h.B ∧ IsCyclic ↥(h.T ⊓ h.K)

@[expose] def CFRow516InnerOutHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ u v : MulAut (OddBar h.K),
      ⁅u, v⁆ ∈ (MulAut.conj : OddBar h.K →* MulAut (OddBar h.K)).range

@[expose] def CFRow516InnerPSpHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) →
    ∀ ℓ : OddBar h.K, ℓ ^ 2 = 1 →
      pPrimeCore 2 ↥(centralizerCore516 (p ^ f) ℓ) = ⊥ ∧
      ∀ ε : MulAut (OddBar h.K), ε ^ 2 = 1 → ε ≠ 1 → ε ≠ MulAut.conj ℓ →
        ε * MulAut.conj ℓ = MulAut.conj ℓ * ε → (∀ y ∈ centralizerCore516 (p ^ f) ℓ, ε y = y) →
        ∃ M : Subgroup (OddBar h.K), (∀ y ∈ M, ε y = y) ∧ Blueprint.LieModel ↥M .PSp 2 p f

@[expose] def CFRow516NoPSpHW : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52W H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) →
    ∀ w : H, ∀ hw : w ∈ normalizer (h.K : Set H), w ∈ h.W → w * w = 1 →
      oddBarConj h.K ⟨w, hw⟩ ≠ 1 →
      ¬ ∃ M : Subgroup (OddBar h.K), (∀ y ∈ M, oddBarConj h.K ⟨w, hw⟩ y = y) ∧
        Blueprint.LieModel ↥M .PSp 2 p f

end CFSG.ComponentClassification.GSThmB
