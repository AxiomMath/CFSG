module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem t158IdentU6_of (hU : T158CompUni) : T158IdentU6 := by
  intro G _ _ L J A d b n hpre hcat hodd
  obtain ⟨i, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
  cases i with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    obtain ⟨hq2, hqe⟩ := hP
    have hcard : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def, hq2, hqe]
    have hsh : I171.I171LieShape 3 (.twistedA 5 q) := by
      refine ⟨hq2, Nat.dvd_gcd (by norm_num) ?_⟩
      rw [hcard]
      exact FullCover.three_dvd_two_pow_add_one_of_odd hodd
    obtain ⟨-, -, hJ⟩ :=
      hU G 3 L J A d b 6 n hpre ⟨.lie ⟨.twistedA 5 q, hv⟩, ⟨q, rfl, hqe, hsh⟩, ⟨e⟩⟩
    refine S9.catalogIs_mono (fun c hc => ?_) hJ
    cases c with
    | lie j =>
      obtain ⟨jd, hjv⟩ := j
      obtain ⟨q', hq2', hqe', ⟨-, hj⟩ | ⟨h3, -⟩⟩ := hc
      · subst hj
        exact ⟨hq2', by rw [hqe', Nat.mul_comm]⟩
      · exact absurd h3 (by norm_num)
    | _ => exact hc.elim
  | _ => exact hP.elim

end CFSG.LocalAnalysis.GLTheoremA.T158

end
