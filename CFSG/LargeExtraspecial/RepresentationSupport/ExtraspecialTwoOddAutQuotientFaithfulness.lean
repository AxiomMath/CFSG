module


public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutQuotientFaithfulness

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

theorem injective {E : Type*} [Group E] [Finite E] {q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (hE : CFSG.IsExtraspecialPGroup 2 E)
    (C : Subgroup (MulAut E)) (hC : IsPGroup q C) :
    Function.Injective ((quotientHom E).comp C.subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have ha' : quotientHom E (a : MulAut E) = 1 := ha
  have hquot : ∀ x : E, (a : MulAut E) x * x⁻¹ ∈ Subgroup.center E := by
    intro x
    have h := congrArg (fun f => f (x : E ⧸ Subgroup.center E)) ha'
    simp only [quotientHom_mk] at h
    have h2 : (((a : MulAut E) x : E) : E ⧸ Subgroup.center E) = (x : E ⧸ Subgroup.center E) := h
    rw [QuotientGroup.eq_iff_div_mem] at h2
    simpa [div_eq_mul_inv] using h2
  have hcomm : commutator E = Subgroup.center E := hE.2.1
  have hcen := CFSG.GroupTheory.AutomorphismAction.fixes_center_of_derived_eq
    (a : MulAut E) hquot hcomm
  have hdev : ∀ x : E, ((a : MulAut E) x * x⁻¹) ^ 2 = 1 := by
    intro x
    have h := pow_card_eq_one' (G := Subgroup.center E) (x := ⟨_, hquot x⟩)
    rw [hE.2.2.2] at h
    simpa using congrArg Subtype.val h
  have hpow := CFSG.GroupTheory.AutomorphismAction.pow_eq_one_of_deviation_exponent
    (p := 2) (a : MulAut E) hcen hquot hdev
  have hpow' : a ^ 2 = 1 := Subtype.ext (by simpa using hpow)
  obtain ⟨n, hn⟩ := hC a
  have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one hpow'
  have h2 : orderOf a ∣ q ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime 2 (q ^ n) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  have : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutQuotientFaithfulness
