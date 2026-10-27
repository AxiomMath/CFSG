module

public import CFSG.Quasithin.Background.SylowOddCentralKernel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryTrans

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem unitaryFieldDataOfCard (hFc : Nat.card F = (2 ^ n) ^ 2) : UnitaryFieldData 2 n F where
  prime := Nat.prime_two
  one_le := by
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      exfalso
      haveI : Fintype F := Fintype.ofFinite F
      have h2 : 1 < Fintype.card F := Fintype.one_lt_card
      rw [← Nat.card_eq_fintype_card, hFc] at h2
      simpa using h2
    · exact hn
  card := by
    rw [hFc, ← pow_mul, Nat.mul_comm n 2]

noncomputable def unitaryPSUEquivStated (hFc : Nat.card F = (2 ^ n) ^ 2) :
    unitaryPSU (unitaryFieldDataOfCard hFc) 3 ≃* StatedProj (StatedSU 3 (2 ^ n) F) :=
  unitaryPSUEquiv (unitaryFieldDataOfCard hFc) (n := 3) (by norm_num)

theorem ker_unitaryProj_odd {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) :
    Odd (Nat.card (unitaryProj h 3).ker) := by
  rw [ker_unitaryProj, card_unitaryScalars h (n := 3) (by norm_num)]
  exact Odd.of_dvd_nat (⟨1, rfl⟩ : Odd 3) (Nat.gcd_dvd_left 3 (2 ^ m + 1))

noncomputable def sylowMapUnitaryProj {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) :
    Sylow 2 ↥(unitarySU 2 m K 3) → Sylow 2 (unitaryPSU h 3) :=
  fun T =>
    letI : Finite ↥(unitarySU 2 m K 3) := model3U4_finite_group h
    letI : Finite (unitaryPSU h 3) :=
      Finite.of_surjective (unitaryProj h 3) (unitaryProj_surjective h 3)
    Sylow.mapSurjective (unitaryProj_surjective h 3) T

theorem sylowMapUnitaryProj_bijective {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : Function.Bijective (sylowMapUnitaryProj h) := by
  haveI : Finite K := h.finite
  haveI : Finite ↥(unitarySU 2 m K 3) := model3U4_finite_group h
  haveI : Finite (unitaryPSU h 3) :=
    Finite.of_surjective (unitaryProj h 3) (unitaryProj_surjective h 3)
  exact sylow_mapSurjective_bijective_of_odd_central_ker (unitaryProj h 3)
    (unitaryProj_surjective h 3)
    (by rw [ker_unitaryProj]; exact unitaryScalars_le_center h 3)
    (ker_unitaryProj_odd h)

theorem omegaOneOf_map_sylowMapUnitaryProj {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (T : Sylow 2 ↥(unitarySU 2 m K 3)) :
    (omegaOneOf (T : Subgroup ↥(unitarySU 2 m K 3))).map (unitaryProj h 3) =
      omegaOneOf ((sylowMapUnitaryProj h T : Sylow 2 (unitaryPSU h 3)) :
        Subgroup (unitaryPSU h 3)) := by
  haveI : Finite K := h.finite
  haveI : Finite ↥(unitarySU 2 m K 3) := model3U4_finite_group h
  haveI : Finite (unitaryPSU h 3) :=
    Finite.of_surjective (unitaryProj h 3) (unitaryProj_surjective h 3)
  dsimp only [sylowMapUnitaryProj]
  rw [Sylow.coe_mapSurjective]
  exact omegaOneOf_map_of_odd_ker (unitaryProj h 3) (ker_unitaryProj_odd h) T.isPGroup'

