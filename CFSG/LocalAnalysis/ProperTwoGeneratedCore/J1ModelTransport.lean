module

public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
import all CFSG.Blueprint.NativeSporadic
import all Init.Data.String.Basic
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.Blueprint.NativeSporadic Matrix

@[expose] def j1_first_matrix : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 7, 9, 9, 10, 7, 9;
     7, 0, 1, 4, 3, 3, 4;
     9, 1, 2, 8, 3, 6, 2;
     9, 4, 8, 10, 1, 6, 0;
     10, 3, 3, 1, 8, 9, 1;
     7, 3, 6, 6, 9, 1, 3;
     9, 4, 2, 0, 1, 3, 0]

@[expose] def j1_second_matrix : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![5, 7, 1, 8, 5, 8, 2;
     10, 4, 10, 0, 3, 3, 8;
     5, 10, 8, 9, 1, 2, 1;
     2, 3, 3, 6, 1, 2, 9;
     7, 4, 7, 2, 10, 7, 3;
     3, 9, 0, 4, 2, 3, 5;
     3, 4, 3, 3, 9, 4, 9]

private def decimalEntries (s : String) : List ℕ :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  ((String.ofList (body.map fun c => if asciiWhitespace c then ' ' else c)).splitOn " ").filter
    (· != "") |>.map fun token =>
      if token.toList.all (fun c => '0' ≤ c && c ≤ '9') then token.toNat?.getD 0 else 0

private theorem decimal_digit_check (s : String)
    (hs : s ∈ ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]) :
    s.toList.all (fun c => '0' ≤ c && c ≤ '9') = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first_entries : decimalEntries J1Seed1 =
    [0, 7, 9, 9, 10, 7, 9, 7, 0, 1, 4, 3, 3, 4, 9, 1, 2, 8, 3, 6, 2,
     9, 4, 8, 10, 1, 6, 0, 10, 3, 3, 1, 8, 9, 1, 7, 3, 6, 6, 9, 1, 3,
     9, 4, 2, 0, 1, 3, 0] := by
  unfold decimalEntries
  cbv
  simp (disch := decide) only [decimal_digit_check, ite_true]
  cbv

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem second_entries : decimalEntries J1Seed2 =
    [5, 7, 1, 8, 5, 8, 2, 10, 4, 10, 0, 3, 3, 8, 5, 10, 8, 9, 1, 2, 1,
     2, 3, 3, 6, 1, 2, 9, 7, 4, 7, 2, 10, 7, 3, 3, 9, 0, 4, 2, 3, 5,
     3, 4, 3, 3, 9, 4, 9] := by
  unfold decimalEntries
  cbv
  simp (disch := decide) only [decimal_digit_check, ite_true]
  cbv

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem j1_first_decode_eq : decode 11 7 3 J1Seed1 = j1_first_matrix := by
  change (fun i j : Fin 7 => ((decimalEntries J1Seed1)[i.val * 7 + j.val]?.getD 0 : ZMod 11)) = _
  rw [first_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem j1_second_decode_eq : decode 11 7 3 J1Seed2 = j1_second_matrix := by
  change (fun i j : Fin 7 => ((decimalEntries J1Seed2)[i.val * 7 + j.val]?.getD 0 : ZMod 11)) = _
  rw [second_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem j1_first_pow_two : j1_first_matrix ^ 2 = 1 := by
  decide +kernel

theorem j1_second_pow_three : j1_second_matrix ^ 3 = 1 := by
  decide +kernel

@[expose] def j1_first_unit : GL (Fin 7) (ZMod 11) :=
  Units.ofPowEqOne j1_first_matrix 2 j1_first_pow_two (by decide)

@[expose] def j1_second_unit : GL (Fin 7) (ZMod 11) :=
  Units.ofPowEqOne j1_second_matrix 3 j1_second_pow_three (by decide)

theorem j1_literal_generators_eq :
    properTwoGenCoreJ1Gens = {j1_first_matrix, j1_second_matrix} := rfl

theorem j1_gl_seed_set_eq :
    {A : GL (Fin 7) (ZMod 11) | (A : Matrix (Fin 7) (Fin 7) (ZMod 11)) ∈
      properTwoGenCoreJ1Gens} = {j1_first_unit, j1_second_unit} := by
  ext A
  simp only [Set.mem_ofPred_eq, j1_literal_generators_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem j1_canonical_subgroup_eq :
    properTwoGenCoreJ1 = Subgroup.closure {j1_first_unit, j1_second_unit} := by
  unfold properTwoGenCoreJ1
  rw [j1_gl_seed_set_eq]

theorem j1_seed_monoid_eq :
    seedMonoid 11 7 3 J1Seed1 J1Seed2 =
      Submonoid.closure {j1_first_matrix, j1_second_matrix} := by
  unfold seedMonoid
  rw [j1_first_decode_eq, j1_second_decode_eq]

@[expose] def j1_exact_model_equiv : properTwoGenCoreJ1 ≃* J1 := by
  change properTwoGenCoreJ1 ≃* (seedMonoid 11 7 3 J1Seed1 J1Seed2)ˣ
  rw [j1_canonical_subgroup_eq, j1_seed_monoid_eq]
  exact (unitSeedEquiv j1_first_unit j1_second_unit).symm

end CFSG.ProperTwoGeneratedCore
