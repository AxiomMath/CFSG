module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Facts
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

inductive S2019Family
  | linear
  | unitary
  | symplectic
  | orthogonal

@[expose] def s2019Family : TauCeti.LieTypeIndex → Option S2019Family
  | .A _ _ => some .linear
  | .twistedA _ _ => some .unitary
  | .C _ _ => some .symplectic
  | .B _ _ | .D _ _ | .twistedD _ _ => some .orthogonal
  | _ => none

@[expose] def S2019FactClassicalOn (F : S2019Family) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (PSimple p S)
        (onLie fun d => d.characteristic = q ∧ s2019Family d = some F ∧ ¬ S2019IsA1 d) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

@[expose] def S2019FixCentralizes (p : ℕ) {G : Type} [Group G] (β : MulAut G) : Prop :=
  ∀ L : Subgroup G, GLAPComponent p (fixSubgroup β) L → ∀ T : Subgroup G, IsPGroup 2 T →
    L ≤ Subgroup.normalizer (T : Set G) → ⁅T, L⁆ = ⊥

@[expose] def S2019LinInner (Qs : ℕ → Prop) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → Qs q →
    ∀ (F : Type) [Field F] [Finite F] [CharP F q] (n : ℕ) (A : GL (Fin n) F) (c : Fˣ),
      A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c →
      S2019FixCentralizes p (LinearFlag.conjAut n F A)

@[expose] def S2019LinOuter : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (F : Type) [Field F] [Finite F] [CharP F q] (n : ℕ), 3 ≤ n →
      ∀ β : MulAut (LinearFlag.projectiveSL n F), β ^ p = 1 →
        (∀ A : GL (Fin n) F, β ≠ LinearFlag.conjAut n F A) → S2019FixCentralizes p β

@[expose] def S2019UniInner (Qs : ℕ → Prop) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → Qs q →
    ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData q f K) (n : ℕ)
      (A : primeFormUnitary h (idGram K n)) (c : Kˣ),
      (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c →
      S2019FixCentralizes p (primeFormConjHom h (idGram K n) A)

@[expose] def S2019UniOuter : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData q f K) (n : ℕ), 3 ≤ n →
      ∀ β : MulAut (primeFormP h (idGram K n)), β ^ p = 1 →
        (∀ A : primeFormUnitary h (idGram K n), β ≠ primeFormConjHom h (idGram K n) A) →
        S2019FixCentralizes p β

end CFSG.LocalAnalysis.GLTheoremA.S2019
