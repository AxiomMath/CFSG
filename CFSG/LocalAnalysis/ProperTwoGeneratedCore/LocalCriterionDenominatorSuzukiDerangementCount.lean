module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiIrreducibleAction
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.InvariantComplement
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "Omega" => {p : Projectivization K (Fin 4 → K) // p ∈ suzukiOvoidSet m}
local notation "q" => 2 ^ (2 * m + 1)

local instance : MulAction SzG Omega := suzukiOvoidAction m

theorem suzuki_derangement_burnside_count (hm : 0 < m) :
    2 * Nat.card {g : SzG // suzukiDerangement m g} + 2 * (q ^ 2) ^ 2 =
      (q ^ 2 + 1) * q ^ 2 * ((q - 1) + 1) := by
  classical
  let : Fintype Omega := Fintype.ofFinite _
  have hq : 0 < q := pow_pos (by norm_num) _
  have hcard : Fintype.card Omega = q ^ 2 + 1 := by
    rw [← Nat.card_eq_fintype_card, suzuki_ovoid_card]
  have htwo : 1 < Fintype.card Omega := by
    rw [hcard]
    have hsq : 0 < q ^ 2 := pow_pos hq _
    omega
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp htwo
  exact zassenhaus_derangement_count
    (suzuki_ovoid_two_transitive m) (suzuki_ovoid_three_point_free m hm)
    a b hab (q ^ 2) (q - 1) hcard (lemma114_suzukiMatrixGroup_card_formula m hm)

theorem suzuki_derangement_count (hm : 0 < m) :
    2 * Nat.card {g : SzG // suzukiDerangement m g} = q ^ 3 * (q - 1) ^ 2 := by
  have hq : 0 < q := pow_pos (by norm_num) _
  have hsub : (q - 1) + 1 = q := Nat.sub_add_cancel (by omega)
  have hcount := suzuki_derangement_burnside_count m hm
  rw [hsub] at hcount
  let d := q - 1
  have hqd : q = d + 1 := hsub.symm
  have hpoly : q ^ 3 * d ^ 2 + 2 * (q ^ 2) ^ 2 = (q ^ 2 + 1) * q ^ 2 * q := by
    rw [hqd]
    ring
  exact Nat.add_right_cancel (hcount.trans hpoly.symm)

theorem suzuki_derangement_count_mul_degree (hm : 0 < m) :
    2 * (q ^ 2 + 1) * Nat.card {g : SzG // suzukiDerangement m g} =
      q * (q - 1) * Nat.card SzG := by
  rw [lemma114_suzukiMatrixGroup_card_formula m hm]
  calc
    2 * (q ^ 2 + 1) * Nat.card {g : SzG // suzukiDerangement m g} =
        (q ^ 2 + 1) * (2 * Nat.card {g : SzG // suzukiDerangement m g}) := by ring
    _ = (q ^ 2 + 1) * (q ^ 3 * (q - 1) ^ 2) := by rw [suzuki_derangement_count m hm]
    _ = q * (q - 1) * ((q ^ 2 + 1) * q ^ 2 * (q - 1)) := by ring

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
