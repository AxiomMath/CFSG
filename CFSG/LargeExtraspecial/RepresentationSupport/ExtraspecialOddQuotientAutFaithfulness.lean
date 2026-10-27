module


public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.AutomorphismAction.CentralDeviation

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

open scoped Pointwise

@[expose] noncomputable def quotientHom (E : Type*) [Group E] :
    MulAut E →* MulAut (E ⧸ Subgroup.center E) where
  toFun α := QuotientGroup.congr (Subgroup.center E) (Subgroup.center E) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem quotientHom_mk {E : Type*} [Group E] (α : MulAut E) (x : E) :
    quotientHom E α (x : E ⧸ Subgroup.center E) = ((α x : E) : E ⧸ Subgroup.center E) := rfl

theorem injective {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hE : CFSG.IsExtraspecialPGroup p E) (hexp : Monoid.exponent E = p)
    (C : Subgroup (MulAut E)) (hC : IsPGroup 2 C) :
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
  have hpow := CFSG.GroupTheory.AutomorphismAction.pow_eq_one_of_exponent_of_fixes_center
    (p := p) (fun x => by rw [← hexp]; exact Monoid.pow_exponent_eq_one x) (a : MulAut E) hcen hquot
  have hpow' : a ^ p = 1 := Subtype.ext (by simpa using hpow)
  obtain ⟨n, hn⟩ := hC a
  have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hpow'
  have h2 : orderOf a ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime p (2 ^ n) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness
