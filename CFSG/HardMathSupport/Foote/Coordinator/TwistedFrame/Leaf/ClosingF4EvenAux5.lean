module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section StepD

open T7

@[expose] def x1110n : Fin Tag.F4.rank → ℤ := ![-1, -1, -1, 0]
@[expose] def z0122 : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 2]
@[expose] def w1221n : Fin Tag.F4.rank → ℤ := ![-1, -2, -2, -1]
@[expose] def v0100n : Fin Tag.F4.rank → ℤ := ![0, -1, 0, 0]
@[expose] def negT : Fin Tag.F4.rank → ℤ := ![-2, -3, -4, -2]

theorem negT_eq : -highRoot Tag.F4 = negT := by decide

theorem x1110n_root : x1110n ∈ rootFinset Tag.F4 := by decide +kernel
theorem z0122_root : z0122 ∈ rootFinset Tag.F4 := by decide +kernel
theorem w1221n_root : w1221n ∈ rootFinset Tag.F4 := by decide +kernel
theorem v0100n_root : v0100n ∈ rootFinset Tag.F4 := by decide +kernel
theorem pB23_root' : pB23 ∈ rootFinset Tag.F4 := by decide +kernel
theorem rB23_root' : rB23 ∈ rootFinset Tag.F4 := rB23_root
theorem negT_root : negT ∈ rootFinset Tag.F4 := by decide +kernel

theorem commPairs_pB23_negT : commPairs Tag.F4 pB23 negT = [(1, 1), (2, 1)] :=
  commPairs_eq_of (by decide +kernel)
theorem commPairs_rB23_negT : commPairs Tag.F4 rB23 negT = [(1, 1), (2, 1)] :=
  commPairs_eq_of (by decide +kernel)
theorem commPairs_rB23_x1110n : commPairs Tag.F4 rB23 x1110n = [(1, 1)] :=
  commPairs_eq_of (by decide +kernel)
theorem commPairs_rB23_z0122 : commPairs Tag.F4 rB23 z0122 = [] :=
  commPairs_eq_of (by decide +kernel)

variable {L : Type} [Field L] [CharP L 2]

theorem comm_two_pairs {β γ δ ε : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hγ : IsRoot Tag.F4 γ)
    (hne : β ≠ γ) (hne' : β ≠ -γ) (hp : commPairs Tag.F4 β γ = [(1, 1), (2, 1)])
    (h11 : γ - β ∉ rootFinset Tag.F4) (e1 : β + γ = δ) (e2 : 2 • β + γ = ε) (c d : L) :
    pinnedX Tag.F4 L β c * pinnedX Tag.F4 L γ d * pinnedX Tag.F4 L β c * pinnedX Tag.F4 L γ d =
      pinnedX Tag.F4 L δ (c * d) * pinnedX Tag.F4 L ε (c ^ 2 * d) := by
  have h := comm_char2 (L := L) hβ hγ hne hne' c d
  rw [hp] at h
  have n1 : (if True ∧ γ - β ∈ rootFinset Tag.F4 then (0 : L) else 1) = 1 :=
    if_neg (fun h => h11 h.2)
  have n2 : (if ((2 : ℕ), (1 : ℕ)) = (1, 1) ∧ γ - β ∈ rootFinset Tag.F4 then (0 : L) else 1) = 1 :=
    if_neg (fun h => absurd h.1 (by decide))
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [n1, n2] at h
  simp only [one_smul, one_mul, pow_one, pow_one, e1, e2] at h
  rw [h]

theorem comm_one_pair {β γ δ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hγ : IsRoot Tag.F4 γ)
    (hne : β ≠ γ) (hne' : β ≠ -γ) (hp : commPairs Tag.F4 β γ = [(1, 1)])
    (h11 : γ - β ∉ rootFinset Tag.F4) (e1 : β + γ = δ) (c d : L) :
    pinnedX Tag.F4 L β c * pinnedX Tag.F4 L γ d * pinnedX Tag.F4 L β c * pinnedX Tag.F4 L γ d =
      pinnedX Tag.F4 L δ (c * d) := by
  have h := comm_char2 (L := L) hβ hγ hne hne' c d
  rw [hp] at h
  have n1 : (if True ∧ γ - β ∈ rootFinset Tag.F4 then (0 : L) else 1) = 1 :=
    if_neg (fun h => h11 h.2)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [n1] at h
  simp only [one_smul, one_mul, pow_one, e1] at h
  rw [h]

theorem rel_pB23_negT (b t : L) :
    pinnedX Tag.F4 L pB23 b * pinnedX Tag.F4 L negT t * pinnedX Tag.F4 L pB23 b *
        pinnedX Tag.F4 L negT t =
      pinnedX Tag.F4 L x1110n (b * t) * pinnedX Tag.F4 L z0122 (b ^ 2 * t) :=
  comm_two_pairs (mem_rootFinset.1 pB23_root') (mem_rootFinset.1 negT_root) (by decide)
    (by decide) commPairs_pB23_negT (by decide +kernel) (by decide) (by decide) b t

theorem rel_rB23_negT (a t : L) :
    pinnedX Tag.F4 L rB23 a * pinnedX Tag.F4 L negT t * pinnedX Tag.F4 L rB23 a *
        pinnedX Tag.F4 L negT t =
      pinnedX Tag.F4 L w1221n (a * t) * pinnedX Tag.F4 L v0100n (a ^ 2 * t) :=
  comm_two_pairs (mem_rootFinset.1 rB23_root') (mem_rootFinset.1 negT_root) (by decide)
    (by decide) commPairs_rB23_negT (by decide +kernel) (by decide) (by decide) a t

theorem rel_rB23_x1110n (a s : L) :
    pinnedX Tag.F4 L rB23 a * pinnedX Tag.F4 L x1110n s * pinnedX Tag.F4 L rB23 a *
        pinnedX Tag.F4 L x1110n s = pinnedX Tag.F4 L g5 (a * s) :=
  comm_one_pair (mem_rootFinset.1 rB23_root') (mem_rootFinset.1 x1110n_root) (by decide)
    (by decide) commPairs_rB23_x1110n (by decide +kernel) (by decide) a s

theorem commute_rB23_z0122 (a s : L) :
    Commute (pinnedX Tag.F4 L rB23 a) (pinnedX Tag.F4 L z0122 s) :=
  commute_pinnedX_of_commPairs_nil Tag.F4 L (mem_rootFinset.1 rB23_root')
    (mem_rootFinset.1 z0122_root) (by decide) (by decide) commPairs_rB23_z0122 a s

end StepD

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
