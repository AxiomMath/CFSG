module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXWFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRk2
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

theorem five_le_and_not_dvd_of_not_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) (hpq : ¬ p ∣ q.card ^ 2 - 1) :
    5 ≤ p ∧ ¬ p ∣ 2 ^ q.exponent - 1 := by
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have h3 : 3 ∣ q.card ^ 2 - 1 := by
    have h4 : q.card ^ 2 = 4 ^ q.exponent := by
      rw [hqc, ← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 q.exponent
  have hp3 : p ≠ 3 := fun h => hpq (h ▸ h3)
  refine ⟨?_, fun h => hpq ?_⟩
  · have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hp) (by decide)
    · exact h
  · rw [hqc]
    exact h.trans (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ q.exponent) 1 2)

theorem t263SelWP_td4Hard :
    T263SelWP t263GTD4Hard := by
  refine DXW.t263SelWP_of_innerRank (fun p hp hp2 Ω _ _ S hSn hSq hSp hcat b _ hInn => ?_)
    (fun p hp hp2 X _ hcat E U hE hU2 hU hEU => ?_)
  · obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d
      case trialityD4 q =>
        obtain ⟨hq2, -⟩ : q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 := hi
        exact CFSG.LocalAnalysis.GLTheoremA.I167.inducesInnerMod_of_rk2 hp hp2 hSq
          ⟨.lie ⟨.trialityD4 q, hv⟩, hq2, ⟨(pSimpleEquiv hSp).trans e⟩⟩ hInn
      all_goals exact False.elim hi
    | cyclic r hr => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi
  · obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d
      case trialityD4 q =>
        obtain ⟨hq2, hpq⟩ : q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 := hi
        obtain ⟨hp5, hpf⟩ := five_le_and_not_dvd_of_not_dvd_sq_sub_one hp hp2 hq2 hpq
        haveI : Finite X :=
          @Finite.of_equiv _ _ (CFSG.Assembly.lie_finite_simple ⟨.trialityD4 q, hv⟩).1
            e.symm.toEquiv
        have hrank := CFSG.RankThree.PartOne.kf123ExcD4NoRankTwo X q.exponent
          (CFSG.HardMathSupport.Cooperstein.Coordinator.chevalleyExceptionalModel_trialityD4_of_lie
            hv hq2 e) p hp hp5 hpf
        have h1 := CFSG.RankThree.OddKernel.card_le_pow_pRank_of_le hp hE hEU
        have h2 := CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt
          (X := Subgroup.normalizer (U : Set X)) ⟨U, hU, hU2, rfl⟩
        calc Nat.card E ≤ p ^ CFSG.Open.pRank p (Subgroup.normalizer (U : Set X)) := h1
          _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (h2.trans hrank)
          _ = p := pow_one p
      all_goals exact False.elim hi
    | cyclic r hr => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
