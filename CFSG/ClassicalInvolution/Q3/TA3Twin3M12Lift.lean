module

public import CFSG.ClassicalInvolution.Q3.TA3Twin3Core
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Twin3

open CFSG CFSG.Blueprint CFSG.ComponentClassification
open scoped commutatorElement

section Square

variable {L : Type*} [Group L]

@[expose] def E (c : L) (b : Bool) : L := if b then c else 1

variable {c : L}

theorem E_mul (hcc : c * c = 1) (a b : Bool) : E c a * E c b = E c (a ^^ b) := by
  cases a <;> cases b <;> simp [E, hcc]

theorem E_inv (hcc : c * c = 1) (a : Bool) : (E c a)⁻¹ = E c a := by
  cases a <;> simp [E, inv_eq_of_mul_eq_one_right hcc]

theorem E_comm (hc : c ∈ Subgroup.center L) (a : Bool) (g : L) : g * E c a = E c a * g := by
  cases a
  · simp [E]
  · exact Subgroup.mem_center_iff.1 hc g

variable {π : L →* NativeSporadic.M12}

theorem sq_lift (hker : π.ker = Subgroup.zpowers c) (hc2 : orderOf c = 2)
    (h40 : ∀ q : NativeSporadic.M12, orderOf q = 2 →
      M12Cover.fixedCount q = 4 ∨ M12Cover.fixedCount q = 0)
    (h4 : ∀ v : L, orderOf (π v) = 2 → M12Cover.fixedCount (π v) = 4 → orderOf v = 2)
    (h0 : ∀ v : L, orderOf (π v) = 2 → M12Cover.fixedCount (π v) = 0 → v ^ 2 = c ∧ orderOf v = 4)
    {v : L} (hv : π v * π v = 1) : v * v = E c (M12Cover.fixedCount (π v) == 0) := by
  by_cases h1 : π v = 1
  · have hvZ : v ∈ Subgroup.zpowers c := hker ▸ MonoidHom.mem_ker.2 h1
    have hcard : Nat.card (Subgroup.zpowers c) = 2 := by rw [Nat.card_zpowers, hc2]
    have h2 : (⟨v, hvZ⟩ : Subgroup.zpowers c) ^ 2 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have h12 : M12Cover.fixedCount (π v) = 12 := by rw [h1]; decide
    rw [h12]
    simpa [E, sq] using congrArg Subtype.val h2
  · have ho : orderOf (π v) = 2 := orderOf_eq_prime (by rw [sq]; exact hv) h1
    rcases h40 _ ho with h | h
    · rw [h, ← sq, ← h4 v ho h, pow_orderOf_eq_one]
      rfl
    · rw [h, ← sq, (h0 v ho h).1]
      rfl

theorem commutator_lift (hπk : π.ker = Subgroup.center L) (hcc : c * c = 1)
    (hsq : ∀ v : L, π v * π v = 1 → v * v = E c (M12Cover.fixedCount (π v) == 0))
    {a b : L} (ha : π a * π a = 1) (hb : π b * π b = 1) (hab : π a * π b = π b * π a) :
    ⁅a, b⁆ = E c ((M12Cover.fixedCount (π a) == 0) ^^ (M12Cover.fixedCount (π b) == 0) ^^
      (M12Cover.fixedCount (π a * π b) == 0)) := by
  have hcen : ∀ g : L, g * ⁅a, b⁆ = ⁅a, b⁆ * g := by
    have h : ⁅a, b⁆ ∈ Subgroup.center L := by
      rw [← hπk, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
        map_inv, hab]
      group
    exact fun g => Subgroup.mem_center_iff.1 h g
  have hab2 : π (a * b) * π (a * b) = 1 := by
    rw [map_mul]
    calc π a * π b * (π a * π b) = π a * (π b * π a) * π b := by group
      _ = π a * (π a * π b) * π b := by rw [hab]
      _ = (π a * π a) * (π b * π b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  rw [commutatorElement_eq_of_central hcen, hsq a ha, hsq b hb, hsq _ hab2, map_mul, E_inv hcc,
    E_mul hcc, E_mul hcc]

end Square

end CFSG.ClassicalInvolution.Q3.TA3.Twin3
