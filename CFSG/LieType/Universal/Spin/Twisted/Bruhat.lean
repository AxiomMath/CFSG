module

public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.PlusCT.RankOne

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
open CFSG.LieType.Universal.Spin.PlusCT

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem minusDatum_rankOne_bruhat [Finite K] (k : Fin (n - 1)) (g : spinGroup (quadMinus n K b c))
    (hg : g ∈ rankOne (minusRootGroup n hirr) k) :
    (∃ h ∈ minusTorus n hirr k, ∃ u ∈ minusRootGroup n hirr (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ minusRootGroup n hirr (Pi.single k 1), ∃ h ∈ minusTorus n hirr k,
        ∃ v ∈ minusRootGroup n hirr (Pi.single k 1), g = u * minusWeyl n hirr k * h * v := by
  by_cases hk : k.val + 1 < n - 1
  · rw [rankOne_minusRootGroup_of_lt n hirr hk] at hg
    obtain ⟨M, rfl⟩ := hg
    rw [minusTorus_of_lt n hirr hk, minusWeyl_of_lt n hirr hk,
      minusRootGroup_single_of_lt n hirr hk]
    have hU : ∀ x : K, (minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false (upperSL2 x) ∈
        ((minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false).range := fun x => by
      rw [HypFrame.longSL2_upperSL2]
      exact ⟨_, rfl⟩
    rcases exists_eq_diagSL2_mul_upperSL2_or M with ⟨τ, d, rfl⟩ | ⟨a, τ, d, rfl⟩
    · exact Or.inl ⟨_, ⟨τ, rfl⟩, _, hU d, map_mul _ _ _⟩
    · refine Or.inr ⟨_, hU a, _, ⟨τ, rfl⟩, _, hU d, ?_⟩
      rw [map_mul, map_mul, map_mul, HypFrame.longTorus_apply]
      rfl
  · rw [rankOne_minusRootGroup_of_not_lt n hirr hk] at hg
    rw [minusTorus_of_not_lt n hirr hk, minusWeyl_of_not_lt n hirr hk,
      minusRootGroup_single_of_not_lt n hirr hk]
    exact shortRankOne_bruhat n hirr k hg

theorem minusDatum_eq_one_of_mem_normalizer (k : Fin (n - 1)) (u : spinGroup (quadMinus n K b c))
    (hu : u ∈ minusRootGroup n hirr (Pi.single k 1))
    (hN : u ∈ Subgroup.normalizer
      (minusRootGroup n hirr (-Pi.single k 1) : Set (spinGroup (quadMinus n K b c)))) :
    u = 1 := by
  by_cases hk : k.val + 1 < n - 1
  · rw [minusRootGroup_single_of_lt n hirr hk] at hu
    rw [minusRootGroup_neg_single_of_lt n hirr hk] at hN
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨d, hd⟩ := (Subgroup.mem_normalizer_iff.mp hN
      ((minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false (.ofAdd 1))).mp ⟨_, rfl⟩
    have h0 : Multiplicative.toAdd a = 0 :=
      eq_zero_of_conj_longRoot (minusFrame n b c).toHypFrame (succ_ne_of_lt n hk) true false
        (d := Multiplicative.toAdd d) hd.symm
    rw [← ofAdd_toAdd a, h0, ofAdd_zero, map_one]
  · rw [minusRootGroup_single_of_not_lt n hirr hk] at hu
    rw [minusRootGroup_neg_single_of_not_lt n hirr hk] at hN
    exact shortPos_eq_one_of_mem_normalizer n hirr k hu hN

end CFSG.LieType.Universal.Spin.Twisted
