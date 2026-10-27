module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Defs
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54SL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin

@[expose] def RowDAThree : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 3 → 4 ≤ m →
    ∀ (Y : Type) [Group Y] [Finite Y] (α : spinGroup (quadPlus m K) →* Y),
      Function.Surjective α → α.ker ≤ center (spinGroup (quadPlus m K)) →
      ∀ t : spinGroup (quadPlus m K), (t : CliffordAlgebra (quadPlus m K)) = -1 →
        orderOf (α t) = 2 → Concl3 Y (α t)) ∧
  (∀ (K : Type) [Field K] [Finite K] (m : ℕ) (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    Nat.card K = 3 → 4 ≤ m →
    ∀ (Y : Type) [Group Y] [Finite Y] (α : spinGroup (quadMinus m K b c) →* Y),
      Function.Surjective α → α.ker ≤ center (spinGroup (quadMinus m K b c)) →
      ∀ t : spinGroup (quadMinus m K b c), (t : CliffordAlgebra (quadMinus m K b c)) = -1 →
        orderOf (α t) = 2 → Concl3 Y (α t))

@[expose] def RowDBThree : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 3 → 4 ≤ m →
    ∀ (Y : Type) [Group Y] [Finite Y] (α : spinGroup (quadPlus m K) →* Y),
      Function.Surjective α → α.ker ≤ center (spinGroup (quadPlus m K)) →
      ∀ t ∈ center (spinGroup (quadPlus m K)), (t : CliffordAlgebra (quadPlus m K)) ≠ -1 →
        orderOf (α t) = 2 → Concl3 Y (α t)) ∧
  (∀ (K : Type) [Field K] [Finite K] (m : ℕ) (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    Nat.card K = 3 → 4 ≤ m →
    ∀ (Y : Type) [Group Y] [Finite Y] (α : spinGroup (quadMinus m K b c) →* Y),
      Function.Surjective α → α.ker ≤ center (spinGroup (quadMinus m K b c)) →
      ∀ t ∈ center (spinGroup (quadMinus m K b c)),
        (t : CliffordAlgebra (quadMinus m K b c)) ≠ -1 → orderOf (α t) = 2 → Concl3 Y (α t))

theorem rowD3_of_parts
    (hA : RowDAThree) (hB : RowDBThree) : RowDThree := by
  intro Y _ _ hq hZ τ n hτ hlie hc t ht htZ
  rcases hτ with rfl | rfl
  ·
    rcases hlie with ⟨-, ⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    rotate_left
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
    have : NeZero n := ⟨by omega⟩
    have : Finite (spinGroup (quadPlus n K)) :=
      LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n))
    obtain ⟨hβs, -, hβk⟩ := spinToStatedProj_quadPlus (K := K) (by omega : 3 ≤ n)
    obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover hβs
      (fun E _ _ π hπ hcen _ =>
        LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_three_exists_section_of_central
          (by omega) hK3 hn hπ hcen) hq hZ e
    rw [hβk] at hαZ hαk
    obtain ⟨t', ht'Z, rfl⟩ := (show t ∈ (center (spinGroup (quadPlus n K))).map α from
      hαZ ▸ htZ)
    by_cases hneg : (t' : CliffordAlgebra (quadPlus n K)) = -1
    · exact hA.1 K n hK3 hn Y α hαs hαk t' hneg ht
    · exact hB.1 K n hK3 hn Y α hαs hαk t' ht'Z hneg ht
  ·
    rcases hlie with ⟨-, ⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
      ⟨-, h, -⟩
    rotate_left
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
    have : Finite (spinGroup (quadMinus n K b c)) :=
      LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := n) hirr)
    obtain ⟨hβs, -, hβk⟩ := spinToStatedProj_quadMinus (K := K) hn hirr
    obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover hβs
      (fun E _ _ π hπ hcen _ =>
        LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_three_exists_section_of_central'
          hirr hK3 hn hπ hcen) hq hZ e
    rw [hβk] at hαZ hαk
    obtain ⟨t', ht'Z, rfl⟩ := (show t ∈ (center (spinGroup (quadMinus n K b c))).map α from
      hαZ ▸ htZ)
    by_cases hneg : (t' : CliffordAlgebra (quadMinus n K b c)) = -1
    · exact hA.2 K n b c hirr hK3 hn Y α hαs hαk t' hneg ht
    · exact hB.2 K n b c hirr hK3 hn Y α hαs hαk t' ht'Z hneg ht

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
