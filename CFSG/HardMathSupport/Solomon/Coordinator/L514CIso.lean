module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem l514c_card_psl {r : ℕ} {Y : Type} [Group Y] (h : IsPSLn 3 r Y) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ r = p ^ a ∧
      Nat.card Y * Nat.gcd 3 (r - 1) = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  obtain ⟨p, a, hK⟩ := exists_piField_true F
  have hr : r = p ^ a := by
    have := hK.card
    rw [piCard, Bool.cond_true] at this
    rw [← hcard, this]
  refine ⟨p, a, hK.prime, hK.one_le, hr, ?_⟩
  have h1 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) * Nat.gcd 3 (Nat.card F - 1) =
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
    CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul
  rw [hcard, mul_assoc] at h1
  rw [Nat.card_congr e.toEquiv]
  exact h1

theorem l514c_card_psu {r : ℕ} {Y : Type} [Group Y] (h : IsPSUn 3 r Y) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ r = p ^ a ∧
      Nat.card Y * Nat.gcd 3 (r + 1) = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  obtain ⟨p, a, hrp, ⟨hFd⟩⟩ := exists_unitaryFieldData hcard
  refine ⟨p, a, hFd.prime, hFd.one_le, hrp, ?_⟩
  have h1 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ a) F)) *
      Nat.gcd 3 (p ^ a + 1) = (p ^ a) ^ 3 * ((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1) :=
    CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hFd
  subst hrp
  rw [mul_assoc] at h1
  rw [Nat.card_congr e.toEquiv]
  exact h1

theorem l514c_not_psl_psu {r r' : ℕ} {Y : Type} [Group Y] (h : IsPSLn 3 r Y) (h' : IsPSUn 3 r' Y) :
    False := by
  obtain ⟨p, a, hp, ha, rfl, h1⟩ := l514c_card_psl h
  obtain ⟨ℓ, b, hℓ, hb, rfl, h2⟩ := l514c_card_psu h'
  refine CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith.order_psl3_ne_psu3 hp hℓ ha hb ?_
  rw [← h1, ← h2]
  ring

end CFSG.HardMathSupport.Solomon.Coordinator
