module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectStd
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open scoped MatrixGroups

theorem fundPerfect_of_longest_root (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {γ₀ : Fin (modelUniv t n p e hp.out).D.rank → ℤ}
    (h₀ : IsLongestRoot (modelUniv t n p e hp.out).D γ₀)
    (hperf : (modelUniv t n p e hp.out).D.rootGroup γ₀ ⊔
        (modelUniv t n p e hp.out).D.rootGroup (-γ₀) ≤
      ⁅(modelUniv t n p e hp.out).D.rootGroup γ₀ ⊔ (modelUniv t n p e hp.out).D.rootGroup (-γ₀),
        (modelUniv t n p e hp.out).D.rootGroup γ₀ ⊔ (modelUniv t n p e hp.out).D.rootGroup (-γ₀)⁆) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  have hsc := fundamentalSingleClass t n p e hp.out hfund hadm hG2 hD4
  have hmem : ((modelUniv t n p e hp.out).D.rootGroup γ₀ ⊔
      (modelUniv t n p e hp.out).D.rootGroup (-γ₀)) ∈
      fundamentalSubgroups t (modelUniv t n p e hp.out).D :=
    ⟨1, γ₀, Or.inl h₀, (map_conj_one _).symm⟩
  intro R hR
  obtain ⟨g, rfl⟩ := hsc _ hmem R hR
  exact fundPerfect_map_conj_le_commutator hperf g

section Tags

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundPerfect_PSL_two (hadm : StatedLieAdmissible .PSL 2 p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 2 p e hp.out).D, R ≤ ⁅R, R⁆ := by
  intro R hR
  rw [fundamentalSubgroups_eq_top_PSL_two p e hp.out hadm R hR]
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  have hSL : Group.IsPerfect (modelUniv .PSL 2 p e hp.out).K :=
    CFSG.ClassicalInvolution.sl2_isPerfect (F := GaloisField p e) h4'
  exact le_of_eq hSL.commutator_eq_top.symm

theorem fundPerfect_PSp (hadm : StatedLieAdmissible .PSp n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  have hn : 2 ≤ n := hadm.2.2.1
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk : IsLongestRoot (modelUniv .PSp n p e hp.out).D (Pi.single k 1) :=
    isLongestRoot_single .PSp n p e hp.out trivial hadm k (show (n - 1) + 1 = n by omega)
  refine fundPerfect_of_longest_root .PSp n p e trivial hadm (by simp) (by simp) hk ?_
  have h := Models.SymplecticPairs.range_longBlock_eq_rankOne (K := GaloisField p e) (n := n)
    (k := k) (show ¬ k.val + 1 < n by show ¬ n - 1 + 1 < n; omega)
  have h' : (modelUniv .PSp n p e hp.out).D.rootGroup (Pi.single k 1) ⊔
      (modelUniv .PSp n p e hp.out).D.rootGroup (-Pi.single k 1) =
        (Models.SymplecticPairs.longBlock (GaloisField p e) n k).range := h.symm
  have hr := fundPerfect_range_le_commutator
    (CFSG.ClassicalInvolution.sl2_isPerfect (F := GaloisField p e) h4')
    (Models.SymplecticPairs.longBlock (GaloisField p e) n k)
  rw [← h'] at hr
  exact hr

theorem fundPerfect_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p e hp.out).D, R ≤ ⁅R, R⁆ := by
  have hf : 1 ≤ e := hadm.2.1
  have h4F : 4 ≤ Nat.card (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
      (CFSG.LieType.Steinberg.Exceptional.frobQ p e)) := by
    rw [card_fixedField_frobQ p e hf]
    exact h4
  let k : Fin (modelUniv .twistedE6 0 p e hp.out).D.rank :=
    CFSG.LieType.Steinberg.TwistedE6.nf 0
  have hk : IsLongestRoot (modelUniv .twistedE6 0 p e hp.out).D (Pi.single k 1) :=
    isLongestRoot_single .twistedE6 0 p e hp.out trivial hadm k (by show 0 < 2; decide)
  refine fundPerfect_of_longest_root .twistedE6 0 p e trivial hadm (by simp) (by simp) hk ?_
  have h := rankOne_twistedE6_zero (CFSG.LieType.Steinberg.Exceptional.frobQ p e)
  have h' : (modelUniv .twistedE6 0 p e hp.out).D.rootGroup (Pi.single k 1) ⊔
      (modelUniv .twistedE6 0 p e hp.out).D.rootGroup (-Pi.single k 1) =
        (nodeHom0 (CFSG.LieType.Steinberg.Exceptional.frobQ p e)).range := h
  have hr := fundPerfect_range_le_commutator
    (CFSG.ClassicalInvolution.sl2_isPerfect h4F)
    (nodeHom0 (CFSG.LieType.Steinberg.Exceptional.frobQ p e))
  rw [← h'] at hr
  exact hr

theorem fundPerfect_POmegaMinus_any (hadm : StatedLieAdmissible .POmegaMinus n p e)
    (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
      R ≤ ⁅R, R⁆ := by
  have hn : 4 ≤ n := hadm.2.2
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  let k : Fin (modelUniv .POmegaMinus n p e hp.out).D.rank := ⟨0, by show 0 < n - 1; omega⟩
  have hk : IsLongestRoot (modelUniv .POmegaMinus n p e hp.out).D (Pi.single k 1) :=
    isLongestRoot_single .POmegaMinus n p e hp.out trivial hadm k (by show 0 + 2 < n; omega)
  refine fundPerfect_of_longest_root .POmegaMinus n p e trivial hadm (by simp) (by simp) hk ?_
  have h := rankOne_minusDatum_long (minusCoeffs_irr p e) (n := n) (k := k)
    (by show 0 + 1 < n - 1; omega)
  have h' : (modelUniv .POmegaMinus n p e hp.out).D.rootGroup (Pi.single k 1) ⊔
      (modelUniv .POmegaMinus n p e hp.out).D.rootGroup (-Pi.single k 1) =
        (rLong n (minusCoeffs p e).1 (minusCoeffs p e).2
          (show (k : Fin (n - 1)).val + 1 < n - 1 by show 0 + 1 < n - 1; omega)).range := h
  have hr := fundPerfect_range_le_commutator
    (CFSG.ClassicalInvolution.sl2_isPerfect h4')
    (rLong n (minusCoeffs p e).1 (minusCoeffs p e).2
      (show (k : Fin (n - 1)).val + 1 < n - 1 by show 0 + 1 < n - 1; omega))
  rw [← h'] at hr
  exact hr

end Tags

end CFSG.ClassicalInvolution.ModelFacts
