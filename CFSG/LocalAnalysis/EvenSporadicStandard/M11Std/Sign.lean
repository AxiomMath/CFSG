module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Equiv Equiv.Perm

theorem four_dvd_card_support_of_sign_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (h2 : σ * σ = 1) (hs : sign σ = 1) : 4 ∣ σ.support.card := by
  by_cases h1 : σ = 1
  · simp [h1]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
    obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two)
    rw [hord] at hn
    have hsum : σ.support.card = 2 * (n + 1) := by
      rw [← sum_cycleType, hn]
      simp [Multiset.sum_replicate]
      ring
    have hsign := sign_of_cycleType σ
    rw [hn, hs] at hsign
    simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even hne).1 hsign.symm
    rw [hsum]
    omega

variable {G : Type*} [Group G]

@[expose] def conjClassHom (t : G) : G →* Perm {x : G // IsConj t x} where
  toFun g :=
    { toFun := fun x => ⟨g * x.1 * g⁻¹, by
        obtain ⟨c, hc⟩ := isConj_iff.1 x.2
        exact isConj_iff.2 ⟨g * c, by rw [← hc]; group⟩⟩
      invFun := fun x => ⟨g⁻¹ * x.1 * g, by
        obtain ⟨c, hc⟩ := isConj_iff.1 x.2
        exact isConj_iff.2 ⟨g⁻¹ * c, by rw [← hc]; group⟩⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g h => by ext; simp [mul_assoc]

theorem conjClassHom_apply (t g : G) (x : {x : G // IsConj t x}) :
    ((conjClassHom t g x : {x : G // IsConj t x}) : G) = g * x.1 * g⁻¹ := rfl

theorem four_dvd_card_sub_card_inf_centralizer [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) {t : G} (ht : t * t = 1) :
    4 ∣ Nat.card {x : G // IsConj t x} - Nat.card {x : G // IsConj t x ∧ t * x = x * t} := by
  classical
  have := Fintype.ofFinite G
  set φ : G →* ℤˣ := (sign : Perm {x : G // IsConj t x} →* ℤˣ).comp (conjClassHom t) with hφ
  have hker : φ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hinj (by rw [map_mul, map_mul, mul_comm]))
    · exact h
  have hsign : sign (conjClassHom t t) = 1 := by
    have : t ∈ φ.ker := by rw [hker]; trivial
    exact this
  have h2 : conjClassHom t t * conjClassHom t t = 1 := by rw [← map_mul, ht, map_one]
  have hsup := four_dvd_card_support_of_sign_eq_one h2 hsign
  have hcard := card_fixedPoints (conjClassHom t t)
  rw [sum_cycleType] at hcard
  have hle := Finset.card_le_univ (conjClassHom t t).support
  have e : Function.fixedPoints (conjClassHom t t) ≃ {x : G // IsConj t x ∧ t * x = x * t} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        have h := congrArg Subtype.val x.2
        rw [conjClassHom_apply] at h
        calc t * x.1.1 = (t * x.1.1 * t⁻¹) * t := by group
          _ = x.1.1 * t := by rw [h]⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        apply Subtype.ext
        rw [conjClassHom_apply]
        calc t * x.1 * t⁻¹ = (x.1 * t) * t⁻¹ := by rw [x.2.2]
          _ = x.1 := by group⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hfix : Fintype.card (Function.fixedPoints (conjClassHom t t)) =
      Nat.card {x : G // IsConj t x ∧ t * x = x * t} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  rw [← hfix, Nat.card_eq_fintype_card (α := {x : G // IsConj t x})]
  convert hsup using 1
  omega

end CFSG.EvenSporadicStandard.M11Std
