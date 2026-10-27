module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Central
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin

@[expose] def RowDA : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (m p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    5 ≤ p ^ f → 4 ≤ m → ∀ t : spinGroup (quadPlus m K),
      (t : CliffordAlgebra (quadPlus m K)) = -1 → ConclZ p f (spinGroup (quadPlus m K)) t) ∧
  (∀ (K : Type) [Field K] [Finite K] (m p f : ℕ) (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    p.Prime → p ≠ 2 → Nat.card K = p ^ f → 5 ≤ p ^ f → 4 ≤ m →
    ∀ t : spinGroup (quadMinus m K b c), (t : CliffordAlgebra (quadMinus m K b c)) = -1 →
      ConclZ p f (spinGroup (quadMinus m K b c)) t)

@[expose] def RowDB : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (m p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    5 ≤ p ^ f → 4 ≤ m → ∀ t ∈ center (spinGroup (quadPlus m K)), t ≠ 1 →
      (t : CliffordAlgebra (quadPlus m K)) ≠ -1 → ConclZ p f (spinGroup (quadPlus m K)) t) ∧
  (∀ (K : Type) [Field K] [Finite K] (m p f : ℕ) (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    p.Prime → p ≠ 2 → Nat.card K = p ^ f → 5 ≤ p ^ f → 4 ≤ m →
    ∀ t ∈ center (spinGroup (quadMinus m K b c)), t ≠ 1 →
      (t : CliffordAlgebra (quadMinus m K b c)) ≠ -1 →
        ConclZ p f (spinGroup (quadMinus m K b c)) t)

theorem rowD_of_parts
    (hA : RowDA) (hB : RowDB) : RowD := by
  intro Y _ _ hq hZ p hp hp2 τ n f hτ hlie h5 hpsl hc t ht htZ
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  rcases hτ with rfl | rfl
  ·
    rcases hlie with ⟨-, ⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    rotate_left
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    have : NeZero n := ⟨by omega⟩
    have : Finite (spinGroup (quadPlus n K)) :=
      LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n))
    obtain ⟨hβs, -, hβk⟩ := spinToStatedProj_quadPlus (K := K) (by omega : 3 ≤ n)
    obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover hβs
      (fun E _ _ π hπ hcen _ =>
        LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
          (by omega) (by rw [hK]; omega) hπ hcen) hq hZ e
    rw [hβk] at hαZ hαk
    obtain ⟨t', ht'Z, rfl⟩ := (show t ∈ (center (spinGroup (quadPlus n K))).map α from
      hαZ ▸ htZ)
    have ht'1 : t' ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hcZ : ConclZ p f (spinGroup (quadPlus n K)) t' := by
      by_cases hneg : (t' : CliffordAlgebra (quadPlus n K)) = -1
      · exact hA.1 K n p f hp hp2 hK h5 hn t' hneg
      · exact hB.1 K n p f hp hp2 hK h5 hn t' ht'Z ht'1 hneg
    exact ConclZ.map (isQuasisimple_spinGroup_quadPlus (by omega)) hαs hαk hp hp2 h5 hcZ
  ·
    rcases hlie with ⟨-, ⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩
    rotate_left
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    have : Finite (spinGroup (quadMinus n K b c)) :=
      LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := n) hirr)
    obtain ⟨hβs, -, hβk⟩ := spinToStatedProj_quadMinus (K := K) hn hirr
    obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover hβs
      (fun E _ _ π hπ hcen _ =>
        LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central hirr hn
          (by rw [hK]; omega) hπ hcen) hq hZ e
    rw [hβk] at hαZ hαk
    obtain ⟨t', ht'Z, rfl⟩ := (show t ∈ (center (spinGroup (quadMinus n K b c))).map α from
      hαZ ▸ htZ)
    have ht'1 : t' ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hcZ : ConclZ p f (spinGroup (quadMinus n K b c)) t' := by
      by_cases hneg : (t' : CliffordAlgebra (quadMinus n K b c)) = -1
      · exact hA.2 K n p f b c hirr hp hp2 hK h5 hn t' hneg
      · exact hB.2 K n p f b c hirr hp hp2 hK h5 hn t' ht'Z ht'1 hneg
    exact ConclZ.map (isQuasisimple_spinGroup_quadMinus hn hirr) hαs hαk hp hp2 h5 hcZ

end CFSG.ComponentClassification.HarrisLit.T1.P54
