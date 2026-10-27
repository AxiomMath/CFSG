module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Six
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwA5Full
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Certs

variable {f : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 f F)

namespace TwA5Big

theorem five_two_pow_ne_three_two {f : ℕ} (hf : 2 ≤ f) : (5, 2 ^ f) ≠ (3, 2) := by
  intro hc
  have h2 : 2 ^ f = 2 := (Prod.ext_iff.1 hc).2
  have h1 : f = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
  omega

theorem hasLabel_unitarySU_twA (h : UnitaryFieldData 2 f F) {m r : ℕ} (hm : 3 ≤ m)
    (hr : r + 1 = m) (hmq : (m, 2 ^ f) ≠ (3, 2)) :
    HasLabel (unitarySU 2 f F m) (· = (⟨.twA, r, f⟩ : GLALabel)) := by
  obtain rfl : m = r + 1 := hr.symm
  refine hasLabel_of_statedClassicalModel_PSU (r := r) (n := f)
    (isQuasisimple_unitarySU h hm hmq) ?_
  have hStated : StatedClassicalModel (unitaryPSU h (r + 1)) .PSU (r + 1) 2 f := by
    refine ⟨⟨Nat.prime_two, h.one_le, by omega, hmq⟩, ?_⟩
    exact ⟨F, inferInstance, inferInstance,
      by rw [h.card, show 2 * f = f * 2 by omega, pow_mul],
      ⟨unitaryPSUEquiv h (by omega)⟩⟩
  have hiso : unitarySU 2 f F (r + 1) ⧸
      Subgroup.center (unitarySU 2 f F (r + 1)) ≃* unitaryPSU h (r + 1) :=
    QuotientGroup.quotientMulEquivOfEq (center_unitarySU_eq_unitaryScalars h (r + 1))
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv hiso.symm hStated

theorem hasLabel_blockSU_suFiveIndex (hf : 2 ≤ f) :
    HasLabel ↥(blockSU h suFiveIndex) (· = (⟨.twA, 4, f⟩ : GLALabel)) := by
  have hI : suFiveIndex.card < 6 := by rw [card_suFiveIndex]; norm_num
  have hlab := hasLabel_unitarySU_twA h (m := suFiveIndex.card) (r := 4)
    (by rw [card_suFiveIndex]; norm_num) (by rw [card_suFiveIndex]) (by
      rw [card_suFiveIndex]
      exact five_two_pow_ne_three_two hf)
  exact (hasLabel_congr (blockSUEquiv h hI) _).1 hlab

theorem evenRank_unitaryPSU_six_le (hf : 4 ≤ f) : evenRank (unitaryPSU h 6) ≤ 4 :=
  rk2_up_twa5_full (lab := (⟨.twA, 5, f⟩ : GLALabel))
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    (twoLocalPrimeRank_statedSU_quot_le_of_dvd 3 Nat.prime_three (by norm_num))
    (hasLabel_unitaryPSU_six h (by omega)) ⟨rfl, rfl⟩ (by show 2 ≤ f; omega)
    (center_unitaryPSU_six h (by omega))

end TwA5Big

theorem exists_mulEquiv_unitaryPSU_of_hasLabel_twA {X : Type} [Group X] [Finite X]
    {lab : GLALabel} (hX : HasLabel X (fun l => l = lab)) (hz : Subgroup.center X = ⊥)
    (ht : lab.tag = .twA) (hn : 2 ≤ lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (h : UnitaryFieldData 2 lab.n F),
      Nonempty (X ≃* unitaryPSU h (lab.rank + 1)) := by
  classical
  obtain ⟨F, hFld, hFin, hChar, C, hCn, hFcard, hCcen, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSU_quot_of_isLabel
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hX ht hn
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : CharP F 2 := hChar
  haveI : C.Normal := hCn
  have hcard2 : Nat.card F = 2 ^ (2 * lab.n) := by
    rw [hFcard, show 2 * lab.n = lab.n * 2 by omega, pow_mul]
  let h' : UnitaryFieldData 2 lab.n F := ⟨Nat.prime_two, by omega, hcard2⟩
  have hZeq : C = Subgroup.center (unitarySU 2 lab.n F (lab.rank + 1)) := by
    refine le_antisymm hCcen ?_
    intro z hzZ
    by_contra hzC
    have hcent : (QuotientGroup.mk z : unitarySU 2 lab.n F (lab.rank + 1) ⧸ C) ∈
        Subgroup.center (unitarySU 2 lab.n F (lab.rank + 1) ⧸ C) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
      show QuotientGroup.mk y * QuotientGroup.mk z = QuotientGroup.mk z * QuotientGroup.mk y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hzZ y]
    have hbot : Subgroup.center (unitarySU 2 lab.n F (lab.rank + 1) ⧸ C) = ⊥ := by
      rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
    rw [hbot, Subgroup.mem_bot] at hcent
    exact hzC ((QuotientGroup.eq_one_iff z).1 hcent)
  refine ⟨F, hFld, hFin, h', ?_⟩
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZeq).trans
    (QuotientGroup.quotientMulEquivOfEq (center_unitarySU_eq_unitaryScalars h' (lab.rank + 1))))⟩

end Certs
