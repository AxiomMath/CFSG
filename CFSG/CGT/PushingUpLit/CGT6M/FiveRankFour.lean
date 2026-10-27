module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataJ2
public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataM12
public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataJ1
public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataPSL
public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataPSU
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Blueprint

theorem not_dvd_of_coprime_fifty_five {n : ℕ} (h : Nat.Coprime n 55) : ¬ 5 ∣ n ∧ ¬ 11 ∣ n := by
  refine ⟨fun h5 => ?_, fun h11 => ?_⟩
  · have := Nat.dvd_gcd h5 (by norm_num : 5 ∣ 55)
    rw [h] at this
    omega
  · have := Nat.dvd_gcd h11 (by norm_num : 11 ∣ 55)
    rw [h] at this
    omega

section Statements

variable {V : Type} [CommGroup V] [Finite V] {L Q : Type} [Group L] [Finite L] [Group Q]
  (ρ : L →* MulAut V) (hρ : Function.Injective ρ) (hV : ∀ v : V, v ^ 2 = 1) (π : L →* Q)
  (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L) {y : L} (hy1 : y ≠ 1)
  (hy5 : y ^ 5 = 1) (h16 : Nat.card V ≤ 2 ^ 4 * Nat.card ↥(fixSub (ρ y)))

include hρ hV hπ hK hy1 hy5 h16

theorem false_of_rank_four_psl2_25 (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hQ : CFSG.Open.StatedClassicalModel Q .PSL 2 5 2) : False :=
  false_of_linesData ρ hρ hV π hπ hK hK5 (linesData_PSL2_25 hQ) hy1 hy5 h16

theorem false_of_rank_four_psl3_5 (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hQ : CFSG.Open.StatedClassicalModel Q .PSL 3 5 1) : False :=
  false_of_heisData ρ hρ hV π hπ hK hK5 (heisData_PSL3_5 hQ) hy1 hy5 h16

theorem false_of_rank_four_psu3_5 (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hQ : CFSG.Open.StatedClassicalModel Q .PSU 3 5 1) : False :=
  false_of_heisData ρ hρ hV π hπ hK hK5 (heisData_PSU3_5 hQ) hy1 hy5 h16

theorem false_of_rank_four_j2 (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hQ : NativeSporadic.IsSporadic Q .J2) : False :=
  false_of_linesData ρ hρ hV π hπ hK hK5 (linesData_J2 hQ) hy1 hy5 h16

theorem false_of_rank_four_m12 (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hK11 : ¬ 11 ∣ Nat.card π.ker) (hQ : NativeSporadic.IsSporadic Q .M12) : False :=
  false_of_frobData ρ hρ hV π hπ hK hK5 hK11 (frobData_M12 hQ) hy1 hy5 h16

theorem false_of_rank_four_j1 (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hK11 : ¬ 11 ∣ Nat.card π.ker) (hQ : NativeSporadic.IsSporadic Q .J1) : False :=
  false_of_frobData ρ hρ hV π hπ hK hK5 hK11 (frobData_J1 hQ) hy1 hy5 h16

end Statements

end CFSG.CGT.PushingUpLit.CGT6M
