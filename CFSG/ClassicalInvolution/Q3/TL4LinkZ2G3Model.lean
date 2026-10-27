module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes Commutes.symm conjSub fundamentalSubgroups
  FundamentalSingleClass)
open CFSG.ClassicalInvolution.RouteD

theorem threeCommuting_of_singleClass {t : StatedLieTag} {K : Type} [Group K]
    {D : UniversalRootDatum K} (hsc : FundamentalSingleClass t D) {A B C : Subgroup K}
    (hA : A ∈ fundamentalSubgroups t D) (hB : B ∈ fundamentalSubgroups t D)
    (hC : C ∈ fundamentalSubgroups t D) (hAB : Commutes A B) (hAC : Commutes A C)
    (hBC : Commutes B C) :
    ∀ R ∈ fundamentalSubgroups t D, ∃ g : Fin 3 → K,
      ∀ i j, i ≠ j → ∀ x ∈ conjSub (g i) R, ∀ y ∈ conjSub (g j) R, x * y = y * x := by
  intro R hR
  obtain ⟨a, ha⟩ := hsc R hR A hA
  obtain ⟨b, hb⟩ := hsc R hR B hB
  obtain ⟨c, hc⟩ := hsc R hR C hC
  have key : ∀ i j : Fin 3, i ≠ j → Commutes (![A, B, C] i) (![A, B, C] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hAB
    · exact hAC
    · exact hAB.symm
    · exact absurd rfl hij
    · exact hBC
    · exact hAC.symm
    · exact hBC.symm
    · exact absurd rfl hij
  have hM : ∀ i : Fin 3, conjSub (![a, b, c] i) R = ![A, B, C] i := by
    intro i
    fin_cases i
    · exact ha.symm
    · exact hb.symm
    · exact hc.symm
  refine ⟨![a, b, c], fun i j hij x hx y hy => ?_⟩
  rw [hM] at hx hy
  exact key i j hij x hx y hy

section Cit3


theorem orthThreeCommuting_odd {n : ℕ} (hn : 4 ≤ n) : OrthThreeCommuting .POmegaOdd n := by
  have hn3 : 3 ≤ n := by omega
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 :=
    ⟨Nat.prime_three, le_rfl, hn3, by norm_num⟩
  have hsc : FundamentalSingleClass .POmegaOdd (oddDatum n (GaloisField 3 1)) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide)
  exact threeCommuting_of_singleClass hsc (rootθB_mem_fundamentalSubgroups hn3)
    (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := ⟨0, by omega⟩)
      (by show 0 + 1 < n; omega))
    (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := ⟨2, by omega⟩)
      (by show 2 + 1 < n; omega))
    (commutes_rootθB_rankOne hn3 h2 (k := ⟨0, by omega⟩) (by show (0 : ℕ) ≠ 1; omega))
    (commutes_rootθB_rankOne hn3 h2 (k := ⟨2, by omega⟩) (by show (2 : ℕ) ≠ 1; omega))
    (commutes_rankOne_oddDatum hn3 h2
      (cartanB_eq_zero_of_far (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩)
        (Or.inl (by show 0 + 1 < 2; omega))))

theorem cartanD_zero_two {n : ℕ} (hn : 4 ≤ n) :
    cartanD n ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 := by
  simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem orthThreeCommuting_plus {n : ℕ} (hn : 4 ≤ n) : OrthThreeCommuting .POmegaPlus n := by
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaPlus n 3 1 := ⟨Nat.prime_three, le_rfl, hn⟩
  have hsc0 : FundamentalSingleClass .POmegaPlus
      (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaPlus n 3 1 Nat.prime_three).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus n 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide)
  have heq : CFSG.ClassicalInvolution.Generic.modelUniv .POmegaPlus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ := by
    simp only [CFSG.ClassicalInvolution.Generic.modelUniv, lieUniversal, hn3, ↓reduceDIte]
  unfold OrthThreeCommuting
  revert hsc0
  rw [heq]
  intro hsc
  exact threeCommuting_of_singleClass hsc (rootθD_mem_fundamentalSubgroups hn3 hn)
    (rankOne_mem_fundamentalSubgroups_plusDatum hn3 ⟨0, by omega⟩)
    (rankOne_mem_fundamentalSubgroups_plusDatum hn3 ⟨2, by omega⟩)
    (commutes_rootθD_rankOne hn3 hn (k := ⟨0, by omega⟩) (by show (0 : ℕ) ≠ 1; omega))
    (commutes_rootθD_rankOne hn3 hn (k := ⟨2, by omega⟩) (by show (2 : ℕ) ≠ 1; omega))
    (commutes_rankOne_plusDatum hn3 (cartanD_zero_two hn))

theorem orthThreeCommuting_minus {n : ℕ} (hn : 5 ≤ n) : OrthThreeCommuting .POmegaMinus n := by
  have hn3 : 3 ≤ n := by omega
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 := ⟨Nat.prime_three, le_rfl, by omega⟩
  have hsc : FundamentalSingleClass .POmegaMinus (minusDatum n hirr) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus n 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide)
  have hlong0 : (twIdx0 hn3).val + 1 < n - 1 := by
    show 0 + 1 < n - 1
    omega
  have hlong2 : (⟨2, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by
    show 2 + 1 < n - 1
    omega
  exact threeCommuting_of_singleClass hsc (rankOneHiMinus_mem_fund hirr hn3)
    (rankOne_mem_fund_minus hirr hlong0) (rankOne_mem_fund_minus hirr hlong2)
    (commutes_hiMinus_twin hirr hn3)
    (commutes_rankOneHiMinus hirr hn3 (j := ⟨2, by omega⟩) (by show 2 ≤ 2; omega))
    (commutes_rankOne_of_cartan_eq_zero_of_longest (minusDatum n hirr)
      (minusDatum_steinbergExtras n hirr) (isLongestRoot_node_minus hirr hlong0).2
      (cartanB_eq_zero_of_far (n := n - 1) (i := twIdx0 hn3) (j := ⟨2, by omega⟩)
        (Or.inl (by show 0 + 1 < 2; omega))))

theorem orthThreeCommutingFacts_proved : OrthThreeCommutingFacts :=
  ⟨fun _ hn => orthThreeCommuting_odd hn, fun _ hn => orthThreeCommuting_plus hn,
    fun _ hn => orthThreeCommuting_minus hn⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
