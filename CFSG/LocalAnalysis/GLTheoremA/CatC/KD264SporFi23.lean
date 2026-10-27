module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23FiveRow
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowTools
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24Seven
public import Certificates.Certificate10137

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi23_moore_A7 :
    ∃ m : ℕ → CFSG.Sporadic.Fi23.J, CFSG.Sporadic.SchreierLemmas.IsMooreFamily 5 m ∧ m 1 ≠ 1 ∧
      ∀ j, 1 ≤ j → j < 6 → m j * eFive = eFive * m j := by
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  have h := Certificates.certificate10137
  unfold fi23FiveMooreOK mooreAt23OK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hall⟩, hrel⟩, hne⟩, hcomm⟩ := h
  set P := mooreChain23 orb (dTable orb) (genTables orb (-2)) (eTab orb) 6
  have hall' : P.all (· < 31671) = true :=
    List.all_eq_true.2 fun x hx => decide_eq_true (hall x hx)
  set m : ℕ → J := fun j => ((mooreWord P j).map conjPt).prod with hmdef
  have hm : ∀ j, Rep 31671 (mooreTab23 orb (dTable orb) (genTables orb (-2)) P j) (m j) :=
    fun j => rep_starWordTab_dTable (mooreWord P j)
  unfold mooreRelOK23 at hrel
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at hrel
  obtain ⟨⟨h1, h2⟩, h3⟩ := hrel
  refine ⟨m, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact eq_of_eqTab ((hm 1).powT hn 3) (Rep.idT hn) h1
  · intro j hj2 hjk
    rcases h2 j (by omega) with h | ⟨h, -⟩
    · exact absurd h (by omega)
    · exact eq_of_eqTab ((hm j).powT hn 2) (Rep.idT hn) h
  · intro j hj2 hjk
    rcases h2 j (by omega) with h | ⟨-, h⟩
    · exact absurd h (by omega)
    · exact eq_of_eqTab (((hm (j - 1)).compT (hm j)).powT hn 3) (Rep.idT hn) h
  · intro i j hi hij hjk
    rcases h3 i (by omega) j (by omega) with (h | h) | h
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact eq_of_eqTab (((hm i).compT (hm j)).powT hn 2) (Rep.idT hn) h
  · exact ne_one_of_rep (hm 1) hne
  · intro j hj1 hjk
    rcases hcomm j hjk with h | h
    · exact absurd h (by omega)
    · exact eq_of_eqTab ((hm j).compT rep_eFive) (rep_eFive.compT (hm j)) h

theorem exists_comp_five :
    ∃ w : CFSG.Sporadic.Fi23.J, orderOf w = 5 ∧
      ∃ J₀ : Subgroup CFSG.Sporadic.Fi23.J, GLAPComponent 5 (Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi23.J)) J₀ := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, hc⟩ := fi23Five_parts
  unfold fi23FiveCore at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h5e', he1'⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have h5e := eq_of_eqTab (rep_eFive.powT hn 5) (Rep.idT hn) h5e'
  have he1 := ne_one_of_rep rep_eFive he1'
  have heo : orderOf eFive = 5 := orderOf_eq_prime h5e he1
  obtain ⟨m, hmoore, hm1, hmc⟩ := fi23_moore_A7
  obtain ⟨-, ⟨eL⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 7)
    (by norm_num) m hmoore).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hm1⟩
  have hLC : Subgroup.closure (m '' Set.Icc 1 (7 - 2)) ≤
      Subgroup.centralizer ({eFive} : Set J) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, ⟨hj1, hj5⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hmc j hj1 (by omega))
  obtain ⟨hs, hnab, hcardL⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.Fi24Seven.alt7_subgroup_data eL
  obtain ⟨k, hk, hk21, -⟩ := card_centralizer_five eFive heo
  refine ⟨eFive, heo, KD264Gen.exists_glaPComponent_of_index2 Nat.prime_five he1 h5e hLC hs hnab
    (by rw [hcardL]; norm_num) ?_⟩
  rw [hk, hcardL]
  omega

theorem kd264SporAt_Fi23 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : KD264Gen.KD264SporAt p .Fi23 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi23_model hbr
  refine @KD264Gen.kd264SporAt_of_model hOut p hp hp2 .Fi23 J _ hfin hs hnc b ?_
  intro hk2 _ hsq
  have hmem := KD264Gen.prime_sq_dvd_mem hp (by rw [card_J]; norm_num) hsq
  rw [card_J] at hmem
  have hsub : ∀ q ∈ (Nat.primeFactorsList 4089470473293004800).filter
      (fun q => q ^ 2 ∣ 4089470473293004800), q = 2 ∨ q = 3 ∨ q = 5 := by
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel
  have hk2' : ¬ p = 3 := hk2
  rcases hsub p hmem with h | h | h
  · exact absurd h hp2
  · exact absurd h hk2'
  · subst h
    obtain ⟨w, hwo, J₀, hJ₀⟩ := exists_comp_five
    exact KD264Gen.kd264RowData_of_sq Nat.prime_five (by rw [card_J]; norm_num)
      (by rw [card_J]; norm_num) w hwo hJ₀

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
