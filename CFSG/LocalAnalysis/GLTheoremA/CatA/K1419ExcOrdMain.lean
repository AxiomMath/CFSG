module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcOrdBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem l3u3Ord_card_alternating_le {S : Type} [Group S] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) : Nat.card S ≤ 20160 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases hn with rfl | rfl | rfl <;> norm_num [Nat.factorial]

theorem l3u3Ord_not_three_dvd_orderSuzuki (m : ℕ) : ¬ 3 ∣ orderSuzuki (2 ^ (2 * m + 1)) := by
  have h2 : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  unfold orderSuzuki
  generalize 2 ^ (2 * m + 1) = q at h2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · have h3 : (q ^ 2 + 1) % 3 = 2 := by
        rw [Nat.add_mod, Nat.pow_mod, h2]
      omega
  · omega

theorem l3u3Ord_orderTits : ¬ 7 ∣ orderTits ∧ orderTits ≤ 366157135872 := by
  unfold orderTits
  constructor <;> norm_num

section Bridge


theorem l3u3Ord_card_ambiguous_le {S : Type} [Group S] [Finite S]
    (h : catalogIs S (ambiguousChev 2)) : Nat.card S ≤ 20160 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | sporadic n => exact hi.elim
  | alternating n hn =>
    refine l3u3Ord_card_alternating_le ?_ e
    simp only [ambiguousChev] at hi
    omega
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 7 := by
          simp only [ambiguousChev] at hi
          omega
        rw [hcard]
        simp only [lieOrderFormula, hq]
        decide +kernel
      · exact hi.elim
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      · have hq : q.card = 3 := by
          simp only [ambiguousChev] at hi
          omega
        rw [hcard]
        simp only [lieOrderFormula, hq]
        decide +kernel
      · rcases r with _ | r
        · exact absurd hi.2 (by norm_num)
        · exact hi.elim
    | _ => exact hi.elim

theorem excOrderRes_holds (hF : L3U3Facts) : ExcOrderRes := by
  intro S _ _ _ _ hS β
  rcases hS with hamb | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · exact not_l3u3Pumpup_of_card_le hF β (l3u3Ord_card_ambiguous_le hamb)
  · have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
    cases d with
    | suzuki m =>
      refine not_l3u3Pumpup_of_not_three_dvd hF β ?_
      rw [hcard]
      exact l3u3Ord_not_three_dvd_orderSuzuki m
    | tits =>
      obtain ⟨h7, hle⟩ := l3u3Ord_orderTits
      exact not_l3u3Pumpup_of_not_seven_dvd hF β (by rw [hcard]; exact h7)
        (by rw [hcard]; exact hle)
    | _ => rcases hd with hd | hd <;> exact hd.elim

end Bridge

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
