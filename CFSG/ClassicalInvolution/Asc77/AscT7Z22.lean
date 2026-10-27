module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z21
public import CFSG.ClassicalInvolution.Asc77.AscT7Z17
public import CFSG.ClassicalInvolution.Asc77.AscT7Z12

public section

namespace CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_chainNeg : Prop :=
  p ^ f % 4 = 3 → C23_chainX p f

variable {p f}

theorem c23_chainX_of_one_mod_four (hq1 : p ^ f % 4 = 1) (hodd : T7Z.OddCenterClassical) :
    C23_chainX p f :=
  c23_chainX_of_chain56 p f (T7Z.c23_chain5_of_inputs hq1 hodd)
    (T7Z.c23_chain6_of_inputs hq1 hodd)

theorem c23_chainX_of_inputs (hodd : T7Z.OddCenterClassical) (hneg : C23_chainNeg p f) :
    C23_chainX p f := by
  rcases (Fact.out : p.Prime).eq_two_or_odd' with h2 | hp
  ·
    intro G _ _ _ Ω K K' W z u e g hs
    exact absurd h2 hs.stand.odd
  · have hodd' : Odd (p ^ f) := hp.pow
    have hmod : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd'
    have hcases : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
    rcases hcases with h1 | h3
    · exact c23_chainX_of_one_mod_four h1 hodd
    · exact hneg h3

theorem c23_chainX_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hneg : C23_chainNeg p f) : C23_chainX p f :=
  c23_chainX_of_inputs (T7Z.oddCenterClassical_of_griess hGA) hneg

end CFSG.ClassicalInvolution.Asc77
