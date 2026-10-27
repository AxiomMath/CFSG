module

public import CFSG.GH74.KGroups.U33
import CFSG.Models.Blueprint
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallRed
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem i141f_autRank_u3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S rsU3) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  have h35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 5 with hlt | hge
    · left
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by norm_num)
    · exact Or.inr hge
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact absurd hi (by simp [onLie])
      · exact absurd hi (by simp [onLie])
      · have hc : q.card = 3 := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_three (s := 1) (by norm_num)
          (hc.trans (by norm_num))
        have hm := lieModel_twistedA' 2 q hv e
        rw [h1, h2] at hm
        obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
          (CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) hm)
        have hR : CFSG.GH74.KGroups.ElemAb p E :=
          ⟨fun a ha b hb => isElemAbelian_commute hE ha hb, hE.2⟩
        rcases h35 with rfl | hp5
        · have h9 := CFSG.GH74.KGroups.U33.autRank3_le_two e' E hR
          norm_num at h3
          omega
        · have hle := CFSG.GH74.KGroups.U33.autRank_ge5 e' p hp hp5 E hR
          have h13 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
          rw [pow_one] at h13
          omega
      · exact absurd hi (by simp [onLie])
    | _ => exact absurd hi (by simp [onLie])
  | _ => exact absurd hi (by simp [onLie])

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
