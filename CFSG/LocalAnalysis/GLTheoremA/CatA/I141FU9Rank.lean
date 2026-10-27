module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FRank
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318LocalU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

section


theorem i141U9Rank_holds : I141U9Rank := by
  intro H _ _ hq hcat
  unfold isU9two at hcat
  obtain ⟨d0, hv0, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d0 with
  | twistedA r q =>
    by_cases h8 : r = 8
    · subst h8
      have hq2 : q.card = 2 := hP
      obtain ⟨hqp, hqe⟩ :=
        (Nat.Prime.pow_eq_iff (p := 2) Nat.prime_two).1 (by
          simpa only [TauCeti.PrimePower.card_def] using hq2)
      have hgen : Gen2318Index (TauCeti.LieTypeIndex.twistedA 8 q) :=
        ⟨Or.inl ⟨hqp, hqe⟩, 3, by norm_num, by norm_num⟩
      let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA 8 q, hv0⟩
      obtain ⟨E, P, _, _, hrho, hPne, hP2, hEnorm⟩ :=
        gen2318Residual_U H hq d hgen ⟨8, q, rfl⟩ ⟨e⟩
      refine ⟨Subgroup.normalizer (P : Set H), ⟨P, hPne, hP2, rfl⟩, ?_⟩
      have hmono := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hEnorm
      have hrho6 : 6 ≤ CFSG.Open.pRank 3 E := by
        simpa [rho2318, d] using hrho
      omega
    · exfalso
      simpa [h8] using hP
  | _ => exact hP.elim

end

end CFSG.LocalAnalysis.GLTheoremA.I141F
