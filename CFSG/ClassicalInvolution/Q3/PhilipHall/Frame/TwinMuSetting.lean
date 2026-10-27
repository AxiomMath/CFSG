module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscMuTabHub
public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Alg

variable {G : Type} [Group G]

theorem orderOf_four_of_sq {w z : G} (hw : w * w = z) (hz : z * z = 1) (hz1 : z ≠ 1) :
    orderOf w = 4 := by
  have h2 : ¬ w ^ 2 ^ 1 = 1 := by
    intro h
    apply hz1
    rw [← hw]
    simpa [pow_two] using h
  have h4' : w ^ (4 : ℕ) = 1 := by
    calc w ^ (4 : ℕ) = (w * w) * (w * w) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hw]; exact hz
  have h4 : w ^ 2 ^ (1 + 1) = 1 := by simpa using h4'
  have := orderOf_eq_prime_pow h2 h4
  simpa using this

end Alg

section Setting

@[expose] def ThompsonWitness {G : Type} [Group G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) : Prop :=
  ∃ (W' : Subgroup G) (_ : W' ∈ WSet Ω) (ρa ρb ρc : Rep Ω W') (w v : G),
    ρa.K = K ∧ ρb.K = K' ∧ ρc.K = J ∧ w ∈ K ⊓ W' ∧ v ∈ K' ⊓ W' ∧ w * w = z ∧ v * v = z ∧
      w * v = u

end Setting

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
