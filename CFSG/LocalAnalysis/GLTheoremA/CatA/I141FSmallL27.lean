module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i141f_autRank_l27 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S rsL27) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact absurd hi (by simp [onLie])
      · have hc : q.card = 7 := hi
        have hl := CFSG.Models.lieModel_A 1 q hv f
        rcases hl.2 with hcl | ⟨h0, -⟩
        · obtain ⟨-, K, _, _, hKc, ⟨e'⟩⟩ := hcl
          have hK7 : Nat.card K = 7 :=
            hKc.trans ((TauCeti.PrimePower.card_def q).symm.trans hc)
          exact no_L27 hp hp2 hK7
            (e'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
              (1 + 1) K).symm) hE h3
        · exact absurd h0 (by norm_num)
      · exact absurd hi (by simp [onLie])
    | _ => exact absurd hi (by simp [onLie])
  | _ => exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.GLTheoremA.I141F
