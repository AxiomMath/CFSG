module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.AutOrthInner
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSixOdd
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem n5_autU42_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : MulAut ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 (ZMod 2) 1 1)))
    (h : σ ^ p = 1) : ∃ y, σ = MulAut.conj y := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, hu, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      hK hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : Finite E := hu.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [hu.card_eq_sq]
  have hsimpleT : IsSimpleGroup (StatedSU 4 (2 ^ 1) E) := by
    have := hsimple
    exact eSU.symm.isSimpleGroup
  have hnaT : ¬ ∀ x y : StatedSU 4 (2 ^ 1) E, x * y = y * x := fun hc =>
    hna fun x y => eSU.injective (by rw [map_mul, map_mul, hc])
  have hcenter : Subgroup.center (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    have := hsimpleT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedSU 4 (2 ^ 1) E))
      with h0 | h1
    · exact h0
    · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hnaT
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, hcenter]
  let ψ : unitaryPSU hu 4 ≃* StatedSU 4 (2 ^ 1) E :=
    (unitaryPSUEquiv hu (n := 4) (by norm_num)).trans
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  have hout : Nat.card (Outer (unitaryPSU hu 4)) = 2 := by
    have := (UnitaryHigher.unitary_full_diagonal_outer_order hu (n := 4) (by norm_num)
      (by norm_num)).2.2.2.2.1
    rw [this]
    norm_num
  have hinner : ∀ τ : MulAut (unitaryPSU hu 4), τ ^ p = 1 →
      τ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU hu 4) := by
    intro τ hτ
    have h1 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU hu 4)) ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one])
    have h2 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU hu 4)) ∣ 2 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk τ : Outer (unitaryPSU hu 4))
      rwa [hout] at this
    have h3 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU hu 4)) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_conj_of_mulEquiv
    (eSU.trans ψ.symm) p hinner σ h

theorem n5_aut_omegaTwo_inner {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : Bool} {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Group K] (hK : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo ε n K)
    (σ : MulAut K) (h : σ ^ p = 1) : ∃ y : K, σ = MulAut.conj y := by
  have hp2 : p ≠ 2 := by omega
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · obtain rfl : n = 3 := by omega
    cases ε with
    | true =>
      obtain ⟨e⟩ := hK
      exact aut_odd_inner_of_mulEquiv e p (statedOmega_quadPlus_three_aut_odd_inner hp hp2) σ h
    | false =>
      obtain ⟨e⟩ := hK
      exact aut_odd_inner_of_mulEquiv e p (n5_autU42_odd hp hp2) σ h
  · cases ε with
    | true =>
      obtain ⟨e⟩ := hK
      exact aut_odd_inner_of_mulEquiv e p
        (statedOmega_quadPlus_aut_odd_inner n p h4 hp hp2 (by rintro ⟨h3, -⟩; omega)) σ h
    | false =>
      obtain ⟨e⟩ := hK
      exact aut_odd_inner_of_mulEquiv e p
        (statedOmega_quadMinus_aut_odd_inner n p h4 hp hp2) σ h

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
