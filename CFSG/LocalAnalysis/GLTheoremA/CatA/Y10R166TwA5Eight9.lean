module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial

section Certs


theorem evenRank_le_pRank_twA5Bar_inf_layers {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 3 F) :
    evenRank (unitaryPSU h 6) ≤
      CFSG.Open.pRank 3 ((twA5Hom h).range.map (unitaryProj h 6) ⊓
        blockSU h suFiveIndex) + 2 := by
  haveI : Finite F := h.finite
  have h2 : 2 ≤ CFSG.Open.pRank 3 ((twA5Hom h).range.map (unitaryProj h 6) ⊓
      blockSU h suFiveIndex) := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) ?_ (twA5Jrange_isElemAbelian h) ?_
    · exact le_inf (twA5Jrange_le_B h) (twA5Jrange_le_J h)
    · rw [card_twA5JHom_range h]; norm_num
  rw [evenRank_unitaryPSU_six h]
  omega

theorem concl166S_twA5Eight_model {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 3 F) :
    ∃ (q : ℕ) (B' : Subgroup (unitaryPSU h 6)) (x' : unitaryPSU h 6)
      (J : Subgroup (unitaryPSU h 6)), Concl166S (unitaryPSU h 6) 7 q B' x' J := by
  refine ⟨3, (twA5Hom h).range.map (unitaryProj h 6), twA5X h, blockSU h suFiveIndex, ?_⟩
  refine concl166S_of_witness (K := unitaryPSU h 6) (p := 7) (q := 3)
    (B := (twA5Hom h).range.map (unitaryProj h 6)) (x := twA5X h)
    (J := blockSU h suFiveIndex) (by norm_num) (by norm_num)
    (twA5Bar_isElemAbelian h (twA5_card_F h)) (twA5X_mem_B h) (twA5X_ne_one h) ?_ ?_
    (blockSU_five_le_centralizer_X h) (isQuasisimple_blockSU_five h)
    (fun g hg k hk => commutator_mem_blockSU_five_of_centralizer_X h hg hk) ⟨.twA, 4, 3⟩
    (hasLabel_blockSU_five h) ?_ ?_ ?_ ?_ ?_
    (twA5EHom h).range (twA5E_le_B h) (twA5E_isElemAbelian h) ?_ (twA5X_mem_E h)
    (twA5_e3_range h) (twA5Bar_le_sup h) (evenRank_le_pRank_twA5Bar_inf_layers h)
    (twA5S h) (twA5S_le_blockSU_five h) (twA5S_isPGroup h) (twA5Bar_le_normalizer_S h) ?_ ?_
  · rw [card_twA5Bar h (twA5_card_F h), evenRank_unitaryPSU_six h]
    norm_num
  · rw [evenRank_unitaryPSU_six h]
  · intro lab hlab
    have he : 4 ≤ evenRank (unitaryPSU h 6) := by
      rw [evenRank_unitaryPSU_six h]
    have hEq : lab = (⟨.twA, 5, 3⟩ : GLALabel) := by
      rcases label_eq_or_BC (K := unitaryPSU h 6) he
        (hasLabel_unitaryPSU_six h (by norm_num)) hlab with
        h | ⟨hB, -, -, -⟩
      · exact h.symm
      · simp at hB
    subst hEq
    simp [JShape, center_unitaryPSU_six h (by norm_num)]
  · have h12 := (twA5_mult_five h).2.2.1
    rw [evenRank_unitaryPSU_six h]
    omega
  · exact (twA5_mult_five h).2.1
  · have hd := (twA5_mult_five h).2.2.2
    have h7 : 7 ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸
        Subgroup.center ↥(blockSU h suFiveIndex)) :=
      hd 7 Nat.prime_seven (by norm_num) (by norm_num)
    have h3 : 3 ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸
        Subgroup.center ↥(blockSU h suFiveIndex)) :=
      hd 3 Nat.prime_three (by norm_num) (by norm_num)
    simpa using (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 7 3) h7 h3)
  · exact Or.inl (twA5_mult_five h).1
  · rw [card_twA5E h]
    norm_num
  · rw [← twA5Bar_inf_centralizer_eq_zpowers h]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  · intro h3 _
    rw [center_unitaryPSU_six h (by norm_num)] at h3
    exact absurd h3 (by simp)

end Certs

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
