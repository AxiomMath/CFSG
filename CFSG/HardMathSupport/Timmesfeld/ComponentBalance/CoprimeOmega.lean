module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.SectionRank.Ccomm

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

theorem mulAut_eq_one_of_coprime_of_fix_omega (hodd : p ≠ 2) (hP : IsPGroup p P) {α : MulAut P}
    (hα : Nat.Coprime (orderOf α) p) (hfix : ∀ x : P, x ^ p = 1 → α x = x) : α = 1 := by
  rcases subsingleton_or_nontrivial P with hs | hnt
  · exact MulEquiv.ext fun x => Subsingleton.elim _ _
  · obtain ⟨D, -, -, -, hD, hstab⟩ := odd_critical_exponent_subgroup hodd hP
    have hmem : α ∈ fixingSubgroup (MulAut P) (D : Set P) := by
      rw [mem_fixingSubgroup_iff]
      exact fun x hx => hfix x (hD x hx)
    have hp1 : IsPGroup p (fixingSubgroup (MulAut P) (D : Set P)) := hstab
    obtain ⟨k, hk⟩ := hp1 ⟨α, hmem⟩
    have hord : orderOf α ∣ p ^ k := by
      have := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
      simpa [Subgroup.orderOf_mk] using this
    have h1 : orderOf α = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k hα) dvd_rfl hord
    exact orderOf_eq_one_iff.1 h1

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
