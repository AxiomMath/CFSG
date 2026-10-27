module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftSplit

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem oddSchurTrivial_specialLinearGroup
    (m : ℕ) (F : Type) [Field F]
    [Finite F] [CharP F 2] : OddSchurTrivial (SpecialLinearGroup (Fin (m + 1)) F) :=
  oddSchurTrivial_of_oddCentralSplit LinearPilot.oddCentralSplit_specialLinearGroup

theorem oddSchurTrivial_statedSU
    {F : Type} [Field F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {m : ℕ} (hm : 2 ≤ m) (hmq : (m, 2 ^ f) ≠ (3, 2)) :
    OddSchurTrivial (StatedSU m (2 ^ f) F) :=
  oddSchurTrivial_of_oddCentralSplit (UnitaryPilot.oddCentralSplit_statedSU hF hm hmq)

section Quotients

theorem exists_surjective_of_psl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {P : Type}
    [Group P] [Finite P] [Group.IsPerfect P] {η : P →* ProjectiveSpecialLinearGroup (Fin (m + 1)) F}
    (hη : Function.Surjective η) (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    ∃ α : SpecialLinearGroup (Fin (m + 1)) F →* P,
      (∀ s, η (α s) = (s : ProjectiveSpecialLinearGroup (Fin (m + 1)) F)) ∧
        Function.Surjective α ∧ η.ker = (center (SpecialLinearGroup (Fin (m + 1)) F)).map α := by
  obtain ⟨α, hα, hs, hker⟩ := exists_surjective_of_oddCentralSplit
    LinearPilot.oddCentralSplit_specialLinearGroup (QuotientGroup.mk'_surjective _) hη hcen hodd
  rw [QuotientGroup.ker_mk'] at hker
  exact ⟨α, hα, hs, hker⟩

theorem card_ker_dvd_psl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {P : Type}
    [Group P] [Finite P] [Group.IsPerfect P] {η : P →* ProjectiveSpecialLinearGroup (Fin (m + 1)) F}
    (hη : Function.Surjective η) (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    Nat.card η.ker ∣ Nat.gcd (m + 1) (Nat.card F - 1) := by
  let := Fintype.ofFinite F
  have h := card_ker_dvd_of_oddCentralSplit LinearPilot.oddCentralSplit_specialLinearGroup
    (QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin (m + 1)) F))) hη hcen hodd
  rw [QuotientGroup.ker_mk',
    Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin (m + 1))
      (R := F)).toEquiv] at h
  have hmax : max (Fintype.card (Fin (m + 1))) 1 = m + 1 := by simp
  rw [hmax, CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd,
    ← Nat.card_eq_fintype_card] at h
  exact h

theorem exists_surjective_of_psu {F : Type} [Field F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {m : ℕ} (hm : 2 ≤ m) (hmq : (m, 2 ^ f) ≠ (3, 2)) {P : Type} [Group P] [Finite P]
    [Group.IsPerfect P] {η : P →* StatedProj (StatedSU m (2 ^ f) F)}
    (hη : Function.Surjective η) (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    ∃ α : StatedSU m (2 ^ f) F →* P,
      (∀ s, η (α s) = (s : StatedProj (StatedSU m (2 ^ f) F))) ∧ Function.Surjective α ∧
        η.ker = ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (2 ^ f) F)).map α := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  obtain ⟨α, hα, hs, hker⟩ := exists_surjective_of_oddCentralSplit
    (UnitaryPilot.oddCentralSplit_statedSU hF hm hmq) (QuotientGroup.mk'_surjective _) hη hcen
    hodd
  rw [QuotientGroup.ker_mk'] at hker
  exact ⟨α, hα, hs, hker⟩

theorem card_ker_dvd_psu {F : Type} [Field F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {m : ℕ} (hm : 2 ≤ m) (hmq : (m, 2 ^ f) ≠ (3, 2)) {P : Type} [Group P] [Finite P]
    [Group.IsPerfect P] {η : P →* StatedProj (StatedSU m (2 ^ f) F)}
    (hη : Function.Surjective η) (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    Nat.card η.ker ∣ Nat.gcd m (2 ^ f + 1) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have h := card_ker_dvd_of_oddCentralSplit (UnitaryPilot.oddCentralSplit_statedSU hF hm hmq)
    (QuotientGroup.mk'_surjective
      ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (2 ^ f) F))) hη hcen hodd
  rwa [QuotientGroup.ker_mk',
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (by omega)).2.2] at h

end Quotients

end CFSG.SeitzReduction.SeitzQ2
