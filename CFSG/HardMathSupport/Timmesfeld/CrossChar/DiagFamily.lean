module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def regimeADiag (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ p ∣ q.card - 1 ∧ p ∣ m + 1

@[expose] def regimeAThreeTwo (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ p = 3 ∧ q.card = 2

@[expose] def DiagLinearBalance : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∣ Nat.card F - 1 → p ∣ n → ∀ D : Subgroup (MulAut (projectiveSL n F)),
      IsElemAbelian p D → Nat.card D = p ^ 3 → D ≤ linearAutGroup n F →
      ∀ H : Subgroup (MulAut (projectiveSL n F)), innerAut (projectiveSL n F) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (projectiveSL n F))) → localDeltaIn p H D = ⊥

theorem crossCharFamAt_ADiag_of_linear (hlin : DiagLinearBalance) :
    CrossCharFamAt .A regimeADiag := by
  rintro ⟨d, hv⟩ _ p hp hp2 _ ⟨m, q, hd, h1, h2⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hn3 : 3 ≤ m + 1 := by
    have := Nat.le_of_dvd (Nat.succ_pos m) h2
    have := hp.two_le
    omega
  have hpF : p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by rwa [hcardF]
  exact IsLocallyBalancedAbs.of_mulEquiv
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _))
    (isLocallyBalancedAbs_projectiveSL_of_linear hn3 hp hp2 hpF
      (hlin (m + 1) _ hn3 p hp hp2 hpF h2))

theorem crossCharFamAt_A_compl_of_linear (hlin : DiagLinearBalance)
    (h32 : CrossCharFamAt .A regimeAThreeTwo) :
    CrossCharFamAt .A fun idx p => ¬ regimeA idx p := by
  intro idx hk p hp hp2 hc hr
  obtain ⟨m, q, hd⟩ := hk
  by_cases h : p ∣ q.card - 1 ∧ p ∣ m + 1
  · exact crossCharFamAt_ADiag_of_linear hlin idx ⟨m, q, hd⟩ p hp hp2 hc ⟨m, q, hd, h⟩
  · have h3 : p = 3 ∧ q.card = 2 := by
      by_contra h3
      exact hr ⟨m, q, hd, h, h3⟩
    exact h32 idx ⟨m, q, hd⟩ p hp hp2 hc ⟨m, q, hd, h3⟩

theorem crossCharFamCat_A_of_linear (hlin : DiagLinearBalance)
    (h32 : CrossCharFamAt .A regimeAThreeTwo) : CrossCharFamCat .A :=
  crossCharFamCat_of_at regimeA crossCharFamAt_A (crossCharFamAt_A_compl_of_linear hlin h32)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
