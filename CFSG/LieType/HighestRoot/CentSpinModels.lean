module

public import CFSG.LieType.HighestRoot.CentSpinThree
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.LieType.HighestRoot

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts

variable {K : Type} [Field K]

theorem highestRootCZ_oddDatum (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    HighestRootCZ (oddDatum n K) K := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set k₀ : Fin n := ⟨0, by omega⟩
  have hk : k₀.val + 1 < n := by simp [k₀]; omega
  have hij : k₀ ≠ ⟨k₀.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  have hlong := isLongest_single_cartanB (m := n) (by omega) rfl (oddDatum n K).isFiniteType hk
  refine ⟨Pi.single k₀ 1, hlong.1, hlong.2, ?_⟩
  have hR : rankOneGroup (oddDatum n K) (Pi.single k₀ 1) =
      ((oddFrame n K).longSL2 hij true false).range := by
    have h1 : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n K) k₀ = (rankOneB K k₀).range :=
      le_antisymm (OddCT.rankOne_le_range _) (by
        rintro _ ⟨M, rfl⟩
        exact OddCT.rankOneB_mem_rankOne _ M)
    rw [rankOneB_of_lt K hk rfl hij] at h1
    exact h1
  rw [hR]
  exact centralizerCondition_longSL2 (oddFrame n K).toHypFrame hij true false h2
    (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n K h2)) (l := ⟨2, by omega⟩)
    (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    (fun r => ⟨(oddFrame n K).polar_vec_z _ r, (oddFrame n K).polar_vec_z _ r,
      (oddFrame n K).polar_vec_z _ r⟩)
    (by rw [(oddFrame n K).map_z]; exact one_ne_zero)

theorem highestRootCZ_plusDatum (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n) :
    HighestRootCZ (plusDatum n K hn3) K := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set k₀ : Fin n := ⟨0, by omega⟩
  have hk : k₀.val + 1 < n := by simp [k₀]; omega
  have hi : rootIdxD n k₀ = ⟨0, by omega⟩ := rootIdxD_of_lt n hk
  have hj : rootIdxD' n k₀ = ⟨1, by omega⟩ := rootIdxD'_of_lt n hk
  refine ⟨Pi.single k₀ 1, (isLongest_single_cartanD hn3 rfl (plusDatum n K hn3).isFiniteType
    k₀).1, (isLongest_single_cartanD hn3 rfl (plusDatum n K hn3).isFiniteType k₀).2, ?_⟩
  have hR : rankOneGroup (plusDatum n K hn3) (Pi.single k₀ 1) =
      ((plusFrame n K hn3).longSL2 (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀)).range :=
    PlusCT.rankOne_plusRootGroup hn3 k₀
  rw [hR]
  set F₀ := plusFrame n K hn3
  have hw₀ : ∀ (a : Fin n) (r : Bool), a ≠ ⟨3, by omega⟩ →
      polar (quadPlus n K) (F₀.vec a r) (F₀.vec ⟨3, by omega⟩ true + F₀.vec ⟨3, by omega⟩ false) =
        0 := fun a r ha => by
    rw [polar_add_right, F₀.polar_vec_of_ne ha, F₀.polar_vec_of_ne ha, add_zero]
  refine centralizerCondition_longSL2 F₀ (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀) h2
    (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus n K)) (l := ⟨2, by omega⟩)
    (by rw [hi]; exact Fin.ne_of_val_ne (by simp)) (by rw [hj]; exact Fin.ne_of_val_ne (by simp))
    (fun r => ⟨hw₀ _ r (by rw [hi]; exact Fin.ne_of_val_ne (by simp)),
      hw₀ _ r (by rw [hj]; exact Fin.ne_of_val_ne (by simp)),
      hw₀ _ r (Fin.ne_of_val_ne (by simp))⟩) ?_
  rw [QuadraticMap.map_add (quadPlus n K), F₀.map_vec, F₀.map_vec,
    show polar (quadPlus n K) (F₀.vec ⟨3, by omega⟩ true) (F₀.vec ⟨3, by omega⟩ false) = 1 from
      F₀.polar_vec_not _ true, zero_add, zero_add]
  exact one_ne_zero

theorem highestRootCZ_minusDatum [Finite K] (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HighestRootCZ (Twisted.minusDatum n hirr) K := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩
  have hk : k₀.val + 1 < n - 1 := by simp [k₀]; omega
  have hlong := isLongest_single_cartanB (m := n - 1) (by omega) rfl
    (Twisted.minusDatum n hirr).isFiniteType hk
  refine ⟨Pi.single k₀ 1, hlong.1, hlong.2, ?_⟩
  have hR : rankOneGroup (Twisted.minusDatum n hirr) (Pi.single k₀ 1) =
      ((Twisted.minusFrame n b c).longSL2 (Twisted.succ_ne_of_lt n hk) true false).range :=
    Twisted.rankOne_minusRootGroup_of_lt n hirr hk
  rw [hR]
  exact centralizerCondition_longSL2 (Twisted.minusFrame n b c).toHypFrame
    (Twisted.succ_ne_of_lt n hk) true false h2
    (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadMinus_of_finite n K hirr))
    (l := ⟨2, by omega⟩) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    (fun r => ⟨(Twisted.minusFrame n b c).polar_vec_z _ r,
      (Twisted.minusFrame n b c).polar_vec_z _ r, (Twisted.minusFrame n b c).polar_vec_z _ r⟩)
    (by rw [(Twisted.minusFrame n b c).map_z]; exact one_ne_zero)

variable {n p e : ℕ}

theorem highestRootCZ_modelUniv_POmegaOdd
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    HighestRootCZ (modelUniv .POmegaOdd n p e hp.out).D (GaloisField p e) :=
  highestRootCZ_oddDatum (two_ne_zero_galoisField e hp2) hadm.2.2.1

theorem highestRootCZ_modelUniv_POmegaPlus
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    HighestRootCZ (modelUniv .POmegaPlus n p e hp.out).D (GaloisField p e) := by
  have hn3 : 3 ≤ n := by have := hadm.2.2; omega
  rw [modelUniv_POmegaPlus hn3]
  exact highestRootCZ_plusDatum (two_ne_zero_galoisField e hp2) hadm.2.2 hn3

theorem highestRootCZ_modelUniv_POmegaMinus
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    HighestRootCZ (modelUniv .POmegaMinus n p e hp.out).D (GaloisField p e) :=
  highestRootCZ_minusDatum (two_ne_zero_galoisField e hp2) hadm.2.2 (minusCoeffs_irr p e)

theorem highestRootCZ_genericModelUniv_POmegaOdd
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaOdd n p e hp.out).D
      (GaloisField p e) :=
  highestRootCZ_modelUniv_POmegaOdd hp2 hadm

theorem highestRootCZ_genericModelUniv_POmegaPlus
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaPlus n p e hp.out).D
      (GaloisField p e) :=
  highestRootCZ_modelUniv_POmegaPlus hp2 hadm

theorem highestRootCZ_genericModelUniv_POmegaMinus
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaMinus n p e hp.out).D
      (GaloisField p e) :=
  highestRootCZ_modelUniv_POmegaMinus hp2 hadm

end CFSG.LieType.HighestRoot
