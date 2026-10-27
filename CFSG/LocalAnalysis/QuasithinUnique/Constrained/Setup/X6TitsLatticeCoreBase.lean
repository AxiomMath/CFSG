
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeAbs
public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Certificates.NativeInvariantMerge
public import CFSG.Sporadic.Schreier.TitsLocal
public import CFSG.Sporadic.Schreier.TitsPrim
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Sporadic.Schreier.TitsStab
public import Mathlib.Algebra.AffineMonoid.Basic

@[expose] public noncomputable section

namespace CFSG.QuasithinUnique.Setup.X6.TitsLat

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

theorem titsFlagStab_le_point
    : titsFlagStab ≤ titsPointStab := by
  intro g hg
  have h1 : titsDFlagAct g 0 = 0 := hg
  have hb := titsBeta_dflag g 0
  rw [h1, titsBeta_zero] at hb
  exact hb.symm

theorem card_subgroupOf_le {P : Type*} [Group P] {X Y : Subgroup P} (h : X ≤ Y) :
    Nat.card (X.subgroupOf Y) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem index_flag_point
    : (titsFlagStab.subgroupOf titsPointStab).index = 5 := by
  have h := Subgroup.card_mul_index (titsFlagStab.subgroupOf titsPointStab)
  rw [card_subgroupOf_le titsFlagStab_le_point, card_titsFlagStab, card_titsPointStab] at h
  have h' : 2048 * (titsFlagStab.subgroupOf titsPointStab).index = 2048 * 5 := by omega
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem titsFlagStab_index
    : titsFlagStab.index = 8775 := by
  have h := Subgroup.card_mul_index titsFlagStab
  rw [card_titsFlagStab, card_titsD] at h
  have h' : 2048 * titsFlagStab.index = 2048 * 8775 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem kappa_eq_zero_iff
    (y : Fin 8775) : titsKappa y = 0 ↔ y = 0 ∨ y = 1 ∨ y = 3 := by
  have h : y ∈ titsF3 ↔ y ∈ ((({0, 1, 3} : Finset (Fin 8775))) : Set (Fin 8775)) := by
    rw [titsF3_eq]
  simpa [titsF3] using h

theorem beta_eq_zero_iff
    (y : Fin 8775) :
    titsBeta y = 0 ↔ y = 0 ∨ y = 2 ∨ y = 5 ∨ y = 10 ∨ y = 20 := by
  have h : y ∈ titsF5 ↔ y ∈ ((({0, 2, 5, 10, 20} : Finset (Fin 8775))) : Set (Fin 8775)) := by
    rw [titsF5_eq]
  simpa [titsF5] using h

end CFSG.QuasithinUnique.Setup.X6.TitsLat
