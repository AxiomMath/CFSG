module

public import CFSG.LieType.Steinberg.Classical.SpinPlus.Commutator
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Weyl
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Unipotent
public import CFSG.LieType.CurtisTits.Spin

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinPlus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

private theorem isUnit_of_natAbs_eq_one {z : ℤ} (h : z.natAbs = 1) : IsUnit (z : K) := by
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl
  · simp
  · simp

theorem rankTwo {O : CommOrder (Φ n K hn)} {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (x n K hn) O C) (k : Fin n) :
    ∃ δ ∈ roots (isFiniteType_cartanD n) ∅, ∃ γ ∈ roots (isFiniteType_cartanD n) ∅,
      δ + γ ≠ 0 ∧ ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ (Pi.single k 1 : Fin n → ℤ) = δ + j • γ ∧
        IsUnit (C δ γ (1, j) : K) := by
  set a := rootIdxD n k
  set b := rootIdxD' n k
  have hab : a ≠ b := rootIdxD_ne n (by omega) k
  obtain ⟨m, hma, hmb⟩ := exists_ne_and_ne hn a b
  obtain ⟨δ, hδ, hδ'⟩ := exists_mem_rootsD_toStdD_eq n (Ne.symm hma) (s := boolSign true)
    (t := boolSign true) (Or.inl rfl) (Or.inl rfl)
  obtain ⟨γ, hγ, hγ'⟩ := exists_mem_rootsD_toStdD_eq n hmb (s := boolSign false)
    (t := boolSign (rootSignD n k)) (Or.inr rfl) (boolSign_eq_one_or_eq_neg_one _)
  have hsum : δ + γ = Pi.single k 1 := by
    apply toStdD_injective n
    rw [toStdD_add, hδ', hγ', toStdD_single (by omega)]
    have h : (Pi.single m (boolSign true) + Pi.single m (boolSign false) : Fin n → ℤ) = 0 := by
      rw [← Pi.single_add, boolSign_true, boolSign_false, add_neg_cancel, Pi.single_zero]
    calc (Pi.single a (boolSign true) + Pi.single m (boolSign true) +
          (Pi.single m (boolSign false) + Pi.single b (boolSign (rootSignD n k))) : Fin n → ℤ)
        = Pi.single a (boolSign true) +
            (Pi.single m (boolSign true) + Pi.single m (boolSign false)) +
            Pi.single b (boolSign (rootSignD n k)) := by abel
      _ = _ := by rw [h, add_zero]
  have hsingle : (Pi.single k 1 : Fin n → ℤ) ∈ (Φ n K hn).roots := (Φ n K hn).single_mem k
  have hne : δ + γ ≠ 0 := by
    rw [hsum]
    exact fun h => (Φ n K hn).zero_notMem (h ▸ hsingle)
  have hp : (1, 1) ∈ expPairs (Φ n K hn) δ γ :=
    ⟨one_pos, one_pos, by rwa [one_smul, one_smul, hsum]⟩
  refine ⟨δ, hδ, γ, hγ, hne, 1, Or.inl rfl, by rw [one_smul, hsum], ?_⟩
  rw [cast_eq_commC hn hC hδ hγ hne hp]
  exact isUnit_of_natAbs_eq_one (commC_natAbs δ γ (1, 1))

theorem chevalleyExtras (O : CommOrder (Φ n K hn)) (C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (x n K hn) O C) :
    ChevalleyExtras (plusDatum n K hn) K (x n K hn) C O where
  param := isParametrization hn
  comm := hC
  weyl i _ hβ := weyl hn i hβ
  rankOne i := rankOne hn i
  prodInjective f L hL hpos hsort := prodInjective hn f L hL hpos hsort
  rankTwo i := rankTwo hn hC i

theorem isCTGroupDatum :
    CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem
      (weylAction (isFiniteType_cartanD n)) (roots (isFiniteType_cartanD n) ∅)
      (plusRootGroup n K hn) (weylD K hn) (fun k => (torusD K hn k).range) :=
  plusDatum_isCTGroupDatum hn (plusDatum_iSup_eq_top n K hn)

theorem presentationB [Finite K] : PresentationB (Φ := Φ n K hn) (x n K hn) :=
  presentationB_of rfl
    (fun O => ⟨commC, commC_natAbs_mem hn, commutatorFormula hn O⟩)
    (fun O C hC => chevalleyExtras hn O C hC)
    (bijective_stPi_of (D := plusDatum n K hn) (isCTGroupDatum hn)
      (plusDatum_steinbergExtras hn)).2

theorem redundantR2 [Finite K] : RedundantR2 (Φ n K hn) (plusDatum n K hn).rootGroup :=
  redundantR2_of rfl (fun O => ⟨commC, commutatorFormula hn O⟩)
    (fun O C hC => chevalleyExtras hn O C hC)
    (bijective_stPi_of (D := plusDatum n K hn) (isCTGroupDatum hn)
      (plusDatum_steinbergExtras hn)).2

theorem conclusionB [Finite K] : ConclusionB (plusDatum n K hn) K (x n K hn) :=
  conclusionB_of (D := plusDatum n K hn) rfl (isCTGroupDatum hn) (plusDatum_steinbergExtras hn)
    (isParametrization hn) (fun O => ⟨commC, commC_natAbs_mem hn, commutatorFormula hn O⟩)
    (fun O C hC => chevalleyExtras hn O C hC)

end CFSG.LieType.Steinberg.SpinPlus
