module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHMain2
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTwinAll
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHG2
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHNT

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

structure T5Residuals (p f : ℕ) [Fact p.Prime] : Prop where
  twinSmall : TwinSmallInner p
  td4OddCore : TD4OddCoreAll p
  td4Generate : TD4GenerateAll p
  ntSp : ∀ k e : ℕ, k ≠ 2 → T5BaseAt p f .PSp k e Not
  ntOrth : ∀ (t : StatedLieTag) (k e : ℕ),
    (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → T5BaseAt p f t k e Not
  ntExc : ∀ (t : StatedLieTag) (k e : ℕ),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → T5BaseAt p f t k e Not

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_of_not_fund {t : StatedLieTag} (ht : ¬ IsFundTag t) {k e : ℕ} (P : Prop → Prop) :
    T5BaseAt p f t k e P := fun _ _ hfund => absurd hfund ht

theorem t5BaseTwin_shapes_of_residuals (h : T5Residuals p f) (t : StatedLieTag) (k e : ℕ)
    (ht : TwinShape t k ∨ t = .G2 ∨ t = .trialityD4) : T5BaseTwin p f t k e := by
  rcases ht with hsh | rfl | rfl
  · exact t5BaseAt_twin_of_shape h.twinSmall hsh
  · exact t5BaseAt_g2 id
  · exact t5BaseAt_td4 h.td4OddCore h.td4Generate id

theorem t5BaseNT_of_residuals (h : T5Residuals p f) (t : StatedLieTag) (k e : ℕ) :
    T5BaseNT p f t k e := by
  cases t with
  | PSL => exact t5BaseAt_nt_psl
  | PSU => exact t5BaseAt_nt_psu
  | PSp =>
      by_cases hk : k = 2
      · subst hk
        exact t5BaseAt_nt_psp_two
      · exact h.ntSp k e hk
  | POmegaOdd => exact h.ntOrth _ k e (Or.inl rfl)
  | POmegaPlus => exact h.ntOrth _ k e (Or.inr (Or.inl rfl))
  | POmegaMinus => exact h.ntOrth _ k e (Or.inr (Or.inr rfl))
  | G2 => exact t5BaseAt_g2 Not
  | F4 => exact h.ntExc _ k e (Or.inl rfl)
  | E6 => exact h.ntExc _ k e (Or.inr (Or.inl rfl))
  | E7 => exact h.ntExc _ k e (Or.inr (Or.inr (Or.inl rfl)))
  | E8 => exact h.ntExc _ k e (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedE6 => exact h.ntExc _ k e (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | trialityD4 => exact t5BaseAt_td4 h.td4OddCore h.td4Generate Not
  | twistedB2 => exact t5BaseAt_of_not_fund (t := .twistedB2) (fun h => h) Not
  | twistedF4 => exact t5BaseAt_of_not_fund (t := .twistedF4) (fun h => h) Not
  | twistedG2 => exact t5BaseAt_of_not_fund (t := .twistedG2) (fun h => h) Not
  | Tits => exact t5BaseAt_of_not_fund (t := .Tits) (fun h => h) Not

theorem ih8Thm5_of_residuals (h : T5Residuals p f) : Ih8Thm5 p f :=
  thm5IH_of_base_shapes (t5BaseTwin_shapes_of_residuals h) (t5BaseNT_of_residuals h)

end CFSG.ClassicalInvolution.Asc77
