module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.ClassSpec
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import Certificates.Certificate10138

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.KD264M23

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native


theorem evalCodes_mem_M23 (w : List ℤ) : evalCodes m23S w ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [← m23Certificate_originalSubgroup]
  exact evalCodes_mem _ m23_gens_mem w

@[expose] noncomputable def mooreM23 (j : ℕ) : Equiv.Perm (Fin 23) :=
  if j = 1 then evalCodes m23S m1W else if j = 2 then evalCodes m23S m2W
  else if j = 3 then evalCodes m23S m3W else 1

theorem mooreM23_mem (j : ℕ) : mooreM23 j ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  unfold mooreM23
  split_ifs
  · exact evalCodes_mem_M23 _
  · exact evalCodes_mem_M23 _
  · exact evalCodes_mem_M23 _
  · exact Subgroup.one_mem _

theorem m23_three_facts :
    orderOf (evalCodes m23S zW) = 3 ∧
      CFSG.Sporadic.SchreierLemmas.IsMooreFamily 3 mooreM23 ∧ mooreM23 1 ≠ 1 ∧
      (∀ j, mooreM23 j * evalCodes m23S zW = evalCodes m23S zW * mooreM23 j) ∧
      56672 ≤ (conjClass CFSG.Blueprint.NativeSporadic.M23 (evalCodes m23S zW)).ncard := by
  obtain ⟨hz3, hz1, h13, h22, h32, h123, h233, h132, hm1, hc1, hc2, hc3, hcl⟩ :=
    Certificates.certificate10138
  set z := evalCodes m23S zW with hzdef
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨orderOf_eq_prime hz3 hz1, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [mooreM23] using h13
  · intro j hj2 hj3
    interval_cases j
    · simpa [mooreM23] using h22
    · simpa [mooreM23] using h32
  · intro j hj2 hj3
    interval_cases j
    · simpa [mooreM23] using h123
    · simpa [mooreM23] using h233
  · intro i j hi hij hj3
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 3 := by omega
    simpa [mooreM23] using h132
  · simpa [mooreM23] using hm1
  · intro j
    unfold mooreM23
    split_ifs
    · exact hc1
    · exact hc2
    · exact hc3
    · rw [one_mul, mul_one]
  · exact hcl

theorem card_centralizer_z_le :
    Nat.card ↥(Subgroup.centralizer ({evalCodes m23S zW} : Set (Equiv.Perm (Fin 23))) ⊓
      CFSG.Blueprint.NativeSporadic.M23) ≤ 180 := by
  obtain ⟨-, -, -, -, hcl⟩ := m23_three_facts
  have h := ncard_conjClass_mul_card CFSG.Blueprint.NativeSporadic.M23 (evalCodes m23S zW)
  rw [CFSG.Sporadic.Schreier.m23_card] at h
  have hc : Nat.card ↥(Subgroup.centralizer ({evalCodes m23S zW} : Set (Equiv.Perm (Fin 23))) ⊓
      CFSG.Blueprint.NativeSporadic.M23) = Nat.card (centralizerIn CFSG.Blueprint.NativeSporadic.M23
        (evalCodes m23S zW)) := by
    rw [centralizerIn, inf_comm]
  rw [hc]
  by_contra hgt
  push Not at hgt
  have : 56672 * 181 ≤ (conjClass CFSG.Blueprint.NativeSporadic.M23 (evalCodes m23S zW)).ncard *
      Nat.card (centralizerIn CFSG.Blueprint.NativeSporadic.M23 (evalCodes m23S zW)) :=
    Nat.mul_le_mul hcl hgt
  omega

theorem kd264RowData_M23_three : KD264Gen.KD264RowData 3 ↥CFSG.Blueprint.NativeSporadic.M23 := by
  obtain ⟨hzo, hmoore, hm1, hcomm, -⟩ := m23_three_facts
  obtain ⟨-, ⟨eL⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 5)
    (by norm_num) mooreM23 hmoore).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hm1⟩
  set D : Subgroup (Equiv.Perm (Fin 23)) := Subgroup.closure (mooreM23 '' Set.Icc 1 (5 - 2))
  have hDP : D ≤ CFSG.Blueprint.NativeSporadic.M23 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, -, rfl⟩
    exact mooreM23_mem j
  have hxD : evalCodes m23S zW ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin 23))) := by
    show evalCodes m23S zW ∈ Subgroup.centralizer
      ((Subgroup.closure (mooreM23 '' Set.Icc 1 (5 - 2)) : Subgroup _) : Set (Equiv.Perm (Fin 23)))
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, -, rfl⟩
    exact hcomm j
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥D := eL.symm.isSimpleGroup
  have hDcard : Nat.card ↥D = 60 := by
    rw [← Nat.card_congr eL.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g := by
    have hx : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.2 (by decide)
    have hy : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.2 (by decide)
    refine ⟨eL ⟨_, hx⟩, (eL ⟨_, hx⟩).2, eL ⟨_, hy⟩, (eL ⟨_, hy⟩).2, fun h => ?_⟩
    have h1 : eL (⟨_, hx⟩ * ⟨_, hy⟩) = eL (⟨_, hy⟩ * ⟨_, hx⟩) := by
      rw [map_mul, map_mul]; exact Subtype.ext h
    have h2 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) * (Equiv.swap (0 : Fin 5) 1 *
        Equiv.swap 2 3) = (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) *
        (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) := congrArg Subtype.val (eL.injective h1)
    exact absurd h2 (by decide)
  have hcard : Nat.card ↥CFSG.Blueprint.NativeSporadic.M23 = 10200960 := m23_card
  exact KD264Gen.kd264RowData_of_record_sq Nat.prime_three (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num) (evalCodes_mem_M23 zW) hzo hDP hs hnab (by rw [hDcard]; norm_num)
    hxD le_rfl card_centralizer_z_le (by rw [hDcard]; norm_num)

theorem kd264SporAt_M23_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hfs : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M23) ∧
      IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M23)) :
    KD264Gen.KD264SporAt 3 .M23 :=
  KD264Gen.kd264SporAt_of_carrier hOut hbr hOrd hfs (by decide) (by decide) Nat.prime_three
    (by norm_num) fun _ _ _ => kd264RowData_M23_three

end CFSG.LocalAnalysis.GLTheoremA.KD264M23
