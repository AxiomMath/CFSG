module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClWit
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ARank
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA TauCeti
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem p_eq_two_of_card_eq_two {q : PrimePower} (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 :=
  (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by rw [← PrimePower.card_def]; exact h)

private theorem center_pQuot_eq_bot_of_oddSchur {X J : Subgroup Ω} (hJ : GLAPComponent 3 X J)
    (hS : OddSchurTrivial (PSimple 3 J)) : Subgroup.center (PQuot 3 J) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hodd : Odd (Nat.card ↥(QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (I2611.isPGroup_center_pQuot' Nat.prime_three J).exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hinj := hS (PQuot 3 J) ⟨hq.1⟩ (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le hodd
  rw [← QuotientGroup.ker_mk' (Subgroup.center (PQuot 3 J))]
  exact (MonoidHom.ker_eq_bot_iff _).2 hinj


theorem card_mul_le_rank_d4two {X J D : Subgroup Ω} (hJ : GLAPComponent 3 X J)
    (hD : IsElemAbelian 3 D) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hcat : catalogIs (PSimple 3 J) S9.isD4two) : 27 * Nat.card D ≤ 3 ^ GLATwoLocalRank 3 Ω := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isD4two hcat
  obtain ⟨h1, h2⟩ := p_eq_two_of_card_eq_two hq
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  have hZ := center_pQuot_eq_bot_of_oddSchur hJ
    (CFSG.SeitzReduction.SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus
      (hm.toBlueprint (by decide)))
  obtain ⟨E, W, hE, hEc, hW2, hW1, hEW⟩ := D4XF.d4two_rank3 hcat
  have h := card_mul_card_le_rank hZ hD hDJ hE hW2 hW1 hEW
  rw [hEc] at h
  exact h

theorem card_mul_le_rank_om10minus {X J D : Subgroup Ω} (hJ : GLAPComponent 3 X J)
    (hD : IsElemAbelian 3 D) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hcat : catalogIs (PSimple 3 J) S265.tyOm10m) :
    81 * Nat.card D ≤ 3 ^ GLATwoLocalRank 3 Ω := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ : ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedD 5 q).Valid),
      q.card = 2 ∧ Nonempty (PSimple 3 J ≃* ValidLieTypeIndex.Group ⟨.twistedD 5 q, hv⟩) := by
    obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
    cases d with
    | twistedD r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨q, hv, hP, ⟨e⟩⟩
      · exact hP.elim
    | _ => exact hP.elim
  obtain ⟨h1, h2⟩ := p_eq_two_of_card_eq_two hq
  have hm := CFSG.Models.lieModel_twistedD 5 q hv e
  rw [h1, h2] at hm
  have hZ := center_pQuot_eq_bot_of_oddSchur hJ
    (CFSG.SeitzReduction.SeitzQ2.oddSchurTrivial_of_lieModel_POmegaMinus
      (hm.toBlueprint (by decide)))
  obtain ⟨U, hU2, hU1, E, hEU, hE, hEc⟩ :=
    I1431C2.Local81.congr e.symm (I1431C2.local81_twistedD 5 q hv h1 h2 le_rfl)
  have h := card_mul_card_le_rank hZ hD hDJ hE hU2 hU1 hEU
  rw [hEc] at h
  calc 81 * Nat.card D = 3 ^ 4 * Nat.card D := by norm_num
    _ ≤ 3 ^ GLATwoLocalRank 3 Ω := h

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
