module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGU
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6Lay
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestTriple
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

private theorem false_of_tyF_three_card {X : Type} [Group X] (h : catalogIs X (tyF 3))
    (hX : Nat.card X ∣ 360 ∨ Nat.card X = 25920 ∨ Nat.card X = 1451520) : False := by
  obtain ⟨n, hn, hN⟩ : ∃ n, 2 ≤ n ∧
      (Nat.card X = ordA 2 (2 ^ n) ∨ Nat.card X = ordTwistedA 2 (2 ^ n)) := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _ <;> try exact (hi : False).elim
    cases l
    case A r q =>
      obtain ⟨hr, hq2, h3⟩ := (hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1)
      obtain rfl : r = 2 := by omega
      have hm := (CFSG.Models.lieModel_A 2 q hv e).2.resolve_right
        fun h => absurd h.1 (by norm_num)
      rw [hq2] at hm
      refine ⟨q.exponent, ?_, .inl ((CFSG.Timmesfeld.card_statedClassicalModel_two hm).1 rfl)⟩
      rw [TauCeti.PrimePower.card_def, hq2] at h3
      have := q.exponent_pos
      by_contra h1
      rw [show q.exponent = 1 by omega] at h3
      norm_num at h3
    case twistedA r q =>
      obtain ⟨hr, hq2, -⟩ := (hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1)
      obtain rfl : r = 2 := by omega
      have hc := CFSG.AGLEmbedding.card_catGroup_twistedA (d := ⟨_, hv⟩) rfl
      rw [hq2] at hc
      refine ⟨q.exponent, ?_, .inr ((Nat.card_congr e.toEquiv).trans hc)⟩
      have h3 : 3 ≤ q.card := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
      rw [TauCeti.PrimePower.card_def, hq2] at h3
      have := q.exponent_pos
      by_contra h1
      rw [show q.exponent = 1 by omega] at h3
      norm_num at h3
    all_goals exact (hi : False).elim
  have hpos : 0 < Nat.card X := by
    rcases hX with h | h | h
    · exact Nat.pos_of_dvd_of_pos h (by norm_num)
    all_goals omega
  have hle : (2 ^ n) ^ 3 ≤ 1451520 := by
    refine (Nat.le_of_dvd hpos ?_).trans ?_
    · rcases hN with h | h <;> rw [h]
      · exact CFSG.StandardType.LinModel.pow_three_dvd_ordA le_rfl
      · exact CFSG.AGLEmbedding.pow_dvd_ordTwistedA_two _ Nat.one_le_two_pow
    · rcases hX with h | h | h
      · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
      all_goals omega
  have hn6 : n ≤ 6 := by
    by_contra h6
    have h7 : (2 ^ 7) ^ 3 ≤ (2 ^ n) ^ 3 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 3
    exact absurd (h7.trans hle) (by norm_num)
  interval_cases n <;> rcases hN with h | h <;> rw [h] at hX <;> revert hX <;> decide +kernel

theorem SG.false_of_comp_sp_two {ℓ : ℕ} (hℓ : ℓ = 3 ∨ ℓ = 4) {s : StatedSp ℓ (ZMod 2)}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) {L : Subgroup (StatedSp ℓ (ZMod 2))}
    (hL : IsComponentOf L (Subgroup.centralizer {s}))
    (hty : catalogIs (↥L ⧸ Subgroup.center ↥L) (tyF 3)) : False := by
  have hdvd : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card L :=
    Subgroup.card_quotient_dvd_card _
  rcases hℓ with rfl | rfl
  · obtain ⟨s₀, m, A₀, A₁, hc⟩ := S265A.exists_sp6Class hs3 hs1
    have hsum := hc.sum_eq
    rcases (by have := hc.one_le; omega : m = 1 ∨ 2 ≤ m) with rfl | hm
    · obtain ⟨-, ⟨e₀⟩⟩ := hc.fixed.resolve_left fun h => by omega
      obtain rfl : s₀ = 2 := by omega
      have hLC : IsComponentOf L (A₀ ⊔ A₁) := by rw [← hc.centralizer_eq]; exact hL
      rcases HSubT.comp_le_or_le hc.commute hLC with hLA | hLA
      · obtain ⟨eK⟩ := HSubT.sp2_component_alt e₀
          (HSubT.isComponentOf_top_subgroupOf (HSubT.isComponentOf_of_le_factor hLC hLA))
        refine false_of_tyF_three_card hty (.inl (hdvd.trans ?_))
        rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hLA).symm.trans eK).toEquiv,
          nat_card_alternatingGroup, Nat.card_fin]
        decide
      · obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hfr, ⟨eA⟩⟩ := hc.unitary
        haveI := (HSubT.guBlockFacts_holds E hE W Hf hsymm hsep).1 (by omega)
        have hLC' : IsComponentOf L (A₁ ⊔ A₀) := by rw [sup_comm]; exact hLC
        exact HSubT.not_isComponentOf_of_solvable
          (Group.isSolvable_of_surjective (f := eA.symm.toMonoidHom) eA.symm.surjective)
          (HSubT.isComponentOf_of_le_factor hLC' hLA)
    · exact HSubT.not_isComponentOf_of_solvable (hc.layer.2 hm).1 hL
  · obtain ⟨⟨i, hi, ⟨e⟩⟩, -⟩ := HSubT.sp8_comp HSubT.guBlockFacts_holds hs3 hs1 hL
    refine false_of_tyF_three_card hty ?_
    rcases hi with hi | hi | hi
    · exact .inr (.inl (CatB.card_of_catalogIs_u4two ⟨i, hi, ⟨e⟩⟩))
    · obtain ⟨e'⟩ := CatB.bridge_sp6two ⟨i, hi, ⟨e⟩⟩
      exact .inr (.inr ((Nat.card_congr e'.toEquiv).trans
        CFSG.Sporadic.Schreier.Co3.card_statedSp_three_two))
    · exact .inl (dvd_of_eq (HSubT.card_of_catalogIs_alt6 ⟨i, hi, ⟨e⟩⟩))

end CFSG.LocalAnalysis.GLTheoremA.S265

end
