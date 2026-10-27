module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCDefs
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Matrix
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def LinUniModelLin (p : ℕ) {Y : Type} [Group Y] (x : Y) (L : Subgroup Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K)
    (e : (↥L ⧸ center ↥L) ≃* StatedProj (StatedSL p K)) (ŷ : GL (Fin p) K) (ω : Kˣ),
    p ∣ Nat.card K - 1 ∧ ŷ ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) ω ∧
    orderOf ω = p ^ (Nat.card K - 1).factorization p ∧
    ∀ (g h : ↥L) (A B : ↥(StatedSL p K)), x * (g : Y) * x⁻¹ = (h : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B : GL (Fin p) K) = ŷ * (A : GL (Fin p) K) * ŷ⁻¹ →
      e (QuotientGroup.mk h) = QuotientGroup.mk B

@[expose] def LinUniModelUni (p : ℕ) {Y : Type} [Group Y] (x : Y) (L : Subgroup Y) : Prop :=
  ∃ (q : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (e : (↥L ⧸ center ↥L) ≃* StatedProj (StatedSU p q K)) (ŷ : GL (Fin p) K) (ω : Kˣ),
    Nat.card K = q ^ 2 ∧ p ∣ q + 1 ∧
    ((ŷ : Matrix (Fin p) (Fin p) K).map (· ^ q))ᵀ * (ŷ : Matrix (Fin p) (Fin p) K) = 1 ∧
    ŷ ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) ω ∧
    orderOf ω = p ^ (q + 1).factorization p ∧
    ∀ (g h : ↥L) (A B : ↥(StatedSU p q K)), x * (g : Y) * x⁻¹ = (h : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B : GL (Fin p) K) = ŷ * (A : GL (Fin p) K) * ŷ⁻¹ →
      e (QuotientGroup.mk h) = QuotientGroup.mk B

@[expose] def LinUniModel (p : ℕ) {Y : Type} [Group Y] (x : Y) (L : Subgroup Y) : Prop :=
  LinUniModelLin p x L ∨ LinUniModelUni p x L

structure LinUniCfg (p : ℕ) {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y)
    (L : Subgroup Y) : Prop where
  data : YData p Y P x z
  comp : IsComponentOf L ⊤
  uniq : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L
  linuni : IsLinearOrUnitaryAt p (↥L ⧸ center ↥L)

structure LinUniZero (p : ℕ) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) : Prop where
  pCore_cyclic : IsCyclic ↥(CFSG.pCore p Y)
  omega_le : ∀ g ∈ CFSG.pCore p Y, g ^ p = 1 → g ∈ L

structure LinUniShape (p : ℕ) {Y : Type} [Group Y] [Finite Y] (x : Y) (L : Subgroup Y) :
    Prop where
  zero : LinUniZero p L
  model : LinUniModel p x L

@[expose] def omegaOneTwo {Y : Type} [Group Y] (T L : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {t : Y | t ∈ T ⊓ L ∧ t ^ 2 = 1}

@[expose] def KD291LinUniZero : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniZero p L

@[expose] def KD291LinUniModel : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniModel p x L

@[expose] def KD292CaseALin : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniZero p L → LinUniModelLin p x L →
    ∀ T : Subgroup Y, IsPGroup 2 T → x ∈ normalizer (T : Set Y) →
      (∀ t ∈ T, ∀ r ∈ centralizer (L : Set Y), t * r = r * t) → T ⊓ L = ⊥ →
        ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ centralizer (T : Set Y)

@[expose] def KD292CaseAUni : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniZero p L → LinUniModelUni p x L →
    ∀ T : Subgroup Y, IsPGroup 2 T → x ∈ normalizer (T : Set Y) →
      (∀ t ∈ T, ∀ r ∈ centralizer (L : Set Y), t * r = r * t) → T ⊓ L = ⊥ → T = ⊥

@[expose] def KD292CaseBSylow : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniShape p x L →
    ∀ T : Subgroup Y, IsPGroup 2 T → x ∈ normalizer (T : Set Y) →
      (∀ t ∈ T, ∀ r ∈ centralizer (L : Set Y), t * r = r * t) → T ⊓ L ≠ ⊥ →
        ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ normalizer (omegaOneTwo T L : Set Y)

@[expose] def KD292CaseBConstr : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniShape p x L →
    ∀ T : Subgroup Y, IsPGroup 2 T → x ∈ normalizer (T : Set Y) →
      (∀ t ∈ T, ∀ r ∈ centralizer (L : Set Y), t * r = r * t) → T ⊓ L ≠ ⊥ →
        GLAPLayer p (normalizer (omegaOneTwo T L : Set Y)) = ⊥

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
