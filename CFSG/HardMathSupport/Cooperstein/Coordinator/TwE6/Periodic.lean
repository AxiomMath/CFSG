module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Indep

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

variable {G : Type*} [Group G] [Finite G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} (D : CurtisDatum G cs 2) {k : Type*} [Field k] [CharP k 2] {m : ℕ}

theorem chi_pow_of_entries_datum (δ : ℕ) {ρ : Representation k G (Fin m → k)}
    (hρ : IsSimpleRep ρ)
    (hent : ∀ s i j, (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i)
    {y : Fin m → k} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) :
    ∀ h ∈ D.H, χ h ^ (2 ^ δ) = χ h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ty : Fin m → k := fun i => (y i) ^ (2 ^ δ) with hty
  have hy : ∀ g, ρ g ty = fun i => (ρ g y i) ^ (2 ^ δ) := fun g => (frob_act δ ρ hent g y).symm
  have hty_fix : ty ∈ D.fixU ρ := by
    intro u hu
    rw [hy, ht.1 u hu]
  have hty0 : ty ≠ 0 := by
    intro h0
    apply ht.2.1
    funext i
    have := congrFun h0 i
    simp only [hty, Pi.zero_apply] at this
    exact pow_eq_zero_iff (by positivity) |>.1 this
  obtain ⟨c, hc⟩ := D.fixU_eq_smul hρ ht hty_fix
  intro h hh
  have e1 : ρ h ty = (χ h ^ (2 ^ δ)) • ty := by
    rw [hy, ht.2.2.1 h hh]
    funext i
    simp [hty, mul_pow]
  have e2 : ρ h ty = χ h • ty := by
    rw [hc, map_smul, ht.2.2.1 h hh, smul_comm]
  have := e1.symm.trans e2
  exact smul_left_injective k hty0 this

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
