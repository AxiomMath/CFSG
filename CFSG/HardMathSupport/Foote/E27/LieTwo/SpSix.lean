module

public import CFSG.Timmesfeld.Orders.Classical
public import Certificates.Certificate131002
public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill
public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatChecks

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.Sporadic.He.Native

section Certificates


theorem sp6_S0 : ∃ S : Subgroup (SpJ 3), Nat.card S = 3 ^ 4 ∧
    (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) → FpfM (matJ 3 c)) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
      ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ ¬ FpfM (matJ 3 (a ^ i * b ^ j))) :=
  Certificates.certificate131002

theorem E27Config.false_of_psp_six {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hcl : StatedClassicalModel (↥K) .PSp 3 2 1) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_spJ (by norm_num) hcl
  have hcard : Nat.card (SpJ 3) = 3 ^ 4 * 17920 := by
    rw [← Nat.card_congr e.toEquiv, (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl]
    decide
  have hfac : (Nat.card (SpJ 3)).factorization 3 = 4 :=
    factorization_three_of_eq hcard (by norm_num)
  obtain ⟨S, hS, hC, hno⟩ := sp6_S0
  refine h.false_of_central_T e S (by rw [hS, hfac]) (fun x => FpfM (matJ 3 x))
    (fun g x => fpfM_conj (matJ 3) g x) {p | p} (fun c hc h1 hcen => hC c hc h1 hcen)
    (fun a ha b hb ha3 hb3 hab ha1 hbz => ?_)
  obtain ⟨i, j, hne, hf⟩ := hno a ha b hb ha3 hb3 hab ha1 hbz
  exact ⟨i, j, hne, hf⟩

end Certificates

end CFSG.HardMathSupport.Foote.E27
