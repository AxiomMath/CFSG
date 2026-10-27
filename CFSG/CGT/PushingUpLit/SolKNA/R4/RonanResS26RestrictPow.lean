module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Red

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

section Restrict

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal]

theorem restrictAut_one (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) :
    TwinSocF4.restrictAut hT hab hC (1 : MulAut A) = 1 := by
  ext x
  simp

theorem restrictAut_mul (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ ψ : MulAut A) :
    TwinSocF4.restrictAut hT hab hC (φ * ψ) =
      TwinSocF4.restrictAut hT hab hC φ * TwinSocF4.restrictAut hT hab hC ψ := by
  ext x
  simp [MulAut.mul_apply]

theorem restrictAut_pow (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : MulAut A) (n : ℕ) :
    TwinSocF4.restrictAut hT hab hC (φ ^ n) = (TwinSocF4.restrictAut hT hab hC φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, restrictAut_one hT hab hC]
  | succ k ih => rw [pow_succ, pow_succ, restrictAut_mul, ih]

end Restrict

section Quot

theorem quotCenterAut_pow {Q : Type} [Group Q] (φ : MulAut Q) (n : ℕ) (y : Q ⧸ Subgroup.center Q) :
    Perp22Rest.quotCenterAut (φ ^ n) y =
      ((Perp22Rest.quotCenterAut φ : MulAut (Q ⧸ Subgroup.center Q)) ^ n) y := by
  induction n generalizing y with
  | zero =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    simp
  | succ k ih =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [pow_succ, MulAut.mul_apply, Perp22Rest.quotCenterAut_mk]
    rw [← ih, Perp22Rest.quotCenterAut_mk]

end Quot

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
