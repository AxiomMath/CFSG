module


public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeQuotientFaithfulness

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

theorem injective {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : Nat.Prime p)
    (hE : CFSG.IsExtraspecialPGroup p E) (hexp : Monoid.exponent E = p)
    (C : Subgroup (MulAut E)) (hC : Nat.Coprime (Nat.card C) p) :
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
  have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hpow'
  have h2 : orderOf a ∣ Nat.card C := orderOf_dvd_natCard a
  have : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hC h2 h1
  exact orderOf_eq_one_iff.mp this

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeQuotientFaithfulness
