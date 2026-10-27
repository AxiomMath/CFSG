module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AAE7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWMMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23E8ZSigX0_of_normal_two (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hA6 : SecAE R e 6) {x : Y}
    (hne : conjSub x (rLayer (Om R) e) ≠ rLayer (Om R) e)
    (htwo : ∀ J ∈ Om R, IsPGroup 2 J)
    (heb : ∀ J ∈ Om R, J ≤ conjSub x (rLayer (Om R) e) →
      ∃ y ∈ p23XE R e x, conjSub y (tightCore R) = J)
    {V : Subgroup Y} (hV2 : IsPGroup 2 V) (htV : t ∈ V)
    (hVn : ∀ y ∈ p23XE R e x, ∀ v ∈ V, y * v * y⁻¹ ∈ V) :
    ∃ x₀ ∈ p23XE R e x, x₀ * t = t * x₀ ∧ IsPGroup 3 (Subgroup.zpowers x₀) ∧
      x₀ * e * x₀⁻¹ ≠ e := by
  have H : AAE7.Hyp n Y R S t K' W u e g x V := ⟨hc, htwo, hA6, hVn, hV2, htV, hne, heb⟩
  obtain ⟨I⟩ := H.nonempty_aeIdent hP hT
  obtain ⟨x₀, hx₀X, hx₀t, ⟨k, hk⟩, hx₀e⟩ := AWM.exists_x0 hc x H.K_le_X I
  refine ⟨x₀, hx₀X, hx₀t, ?_, fun h => hx₀e 1 (oddCoreOf _).one_mem (by simpa using h)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
