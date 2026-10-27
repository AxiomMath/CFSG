module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FFam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.LocalAnalysis.GLTheoremA

theorem tyU38_imp_tyF3 (i : TauCeti.CFSGIndex) (h : tyU38 i) : tyF 3 i := by
  cases i with
  | cyclic _ _ => exact h.elim
  | alternating _ _ => exact h.elim
  | sporadic _ => exact h.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact h.elim
      · exact h.elim
      · have hq : q.card = 8 := h
        have h8 : q.p ^ q.exponent = 2 ^ 3 := by
          rw [← TauCeti.PrimePower.card_def, hq]
          norm_num
        have hdvd : q.p ∣ 2 ^ 3 := h8 ▸ dvd_pow_self q.p q.exponent_pos.ne'
        have hp : q.p = 2 :=
          (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp (q.prime_p.dvd_of_dvd_pow hdvd)
        show 2 + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1
        exact ⟨rfl, hp, by rw [hq]; norm_num⟩
      · exact h.elim
    | _ => exact h.elim

theorem quFamDU3_of_f3 (h : QUFamF3) : QUFamDU3 := by
  intro p Ω _ _ S B T x b hN hp3 hU
  subst hp3
  exact h 3 Ω S B T x b hN rfl (S10.catalogIs_imp tyU38_imp_tyF3 hU)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
