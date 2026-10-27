module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430AltEmbed
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i1430M23Alt_holds : I1430M23Alt := by
  intro H _ _ hq hz n hn hA
  obtain ⟨i, hi, ⟨e⟩⟩ := hA
  cases i with
  | cyclic p hp => exact (show False from hi).elim
  | alternating m hm =>
    have hmn : m = n := hi
    subst hmn
    have hAn : CFSG.LocalAnalysis.GLTheoremB.MovingAround.IsAltType m (H ⧸ Subgroup.center H) :=
      Nonempty.intro e
    have hdvd := CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.card_center_dvd_of_isAltType hq hAn
    rw [if_neg (show ¬(m = 6 ∨ m = 7) by omega)] at hdvd
    have hcen : Subgroup.center H = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hzc
      obtain ⟨k, hk⟩ := hz z hzc
      have h1 : orderOf (⟨z, hzc⟩ : Subgroup.center H) ∣ 2 := (orderOf_dvd_natCard _).trans hdvd
      have h2 : z ^ 2 = 1 := by
        have h := orderOf_dvd_iff_pow_eq_one.1 h1
        simpa using congrArg Subtype.val h
      have h3 : z ^ Nat.gcd 2 (3 ^ k) = 1 := pow_gcd_eq_one.2 ⟨h2, hk⟩
      have hcop : Nat.gcd 2 (3 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
      rw [hcop, pow_one] at h3
      exact h3
    have e' : H ≃* alternatingGroup (Fin m) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcen.symm)).trans e
    rw [hcen, pRank_bot_eq_zero 3 (by norm_num), add_zero]
    exact CFSG.LocalAnalysis.GLTheoremA.S8.L84.i1430TwoLocal_of_injective e'.symm.toMonoidHom
      e'.symm.injective (CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430AltEmbed.i1430TwoLocal_alt m (by omega))
  | lie _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
