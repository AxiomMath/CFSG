module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Five
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowTools

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 M)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section KD264



theorem exists_comp_five :
    ∃ w : CFSG.Sporadic.Fi24.J, orderOf w = 5 ∧
      ∃ J₀ : Subgroup CFSG.Sporadic.Fi24.J, GLAPComponent 5 (Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi24.J)) J₀ := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e, he, f, hf, h5e, he1, -, -, -, hcM⟩ := fi24FiveMoore_parts
  obtain ⟨w, hwe⟩ : ∃ w : J, (w : GL (Fin 781) (ZMod 3)) = e := ⟨⟨e, he⟩, rfl⟩
  obtain ⟨h36, m, hmoore, hm1, hmc⟩ := hcM 1 (by norm_num) 0 (by norm_num) (by norm_num) w
    (by rw [pow_one, pow_zero, mul_one, hwe])
  have hw5 : w ^ 5 = 1 := Subtype.ext (by simp [hwe, h5e])
  have hw1 : w ≠ 1 := fun h1 => he1 (by rw [← hwe, h1]; rfl)
  have hwo : orderOf w = 5 := orderOf_eq_prime hw5 hw1
  obtain ⟨-, ⟨eL⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
    (by norm_num) m hmoore).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hm1⟩
  have hLC : Subgroup.closure (m '' Set.Icc 1 (9 - 2)) ≤ Subgroup.centralizer ({w} : Set J) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hmc j hj1 (by omega))
  obtain ⟨hs, hnab, hcardL⟩ := alt9_data eL
  refine ⟨w, hwo, KD264Gen.exists_glaPComponent_of_bound Nat.prime_five hw1 hw5 hLC hs hnab
    (by rw [hcardL]; norm_num) ?_⟩
  rw [hcardL]
  exact (Fi24FiveBound.card_centralizer_le_of_ncard w hwo
    ((Fi24FiveBound.ncard_fixD24_jR w).trans h36)).trans (by norm_num)

theorem kd264SporAt_Fi24 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .Fi24Prime := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .Fi24Prime ↥J _ hfin hs hnc b ?_
  intro hk2 _ hsq
  have hcard := CFSG.Sporadic.Fi24.card_J
  have hmem := KD264Gen.prime_sq_dvd_mem hp (by rw [hcard]; norm_num) hsq
  rw [hcard] at hmem
  have hsub : ∀ q ∈ (Nat.primeFactorsList 1255205709190661721292800).filter
      (fun q => q ^ 2 ∣ 1255205709190661721292800), q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ (p = 3 ∨ p = 7) := hk2
  rcases hsub p hmem with h | h | h | h
  · exact absurd h hp2
  · exact absurd (Or.inl h) hk2'
  · subst h
    obtain ⟨w, hwo, J₀, hJ₀⟩ := exists_comp_five
    exact KD264Gen.kd264RowData_of_sq Nat.prime_five (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num) w hwo hJ₀
  · exact absurd (Or.inr h) hk2'

end KD264

end CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows
