module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.RstarCoprime
public import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.QuotientJoinFaithful

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

variable {G : Type} [Group G] [Finite G]

theorem quotientHom_injective_of_coprime {E : Type*} [Group E] [Finite E] {p : ℕ}
    (hE : CFSG.IsExtraspecialPGroup p E) (hexp : Monoid.exponent E = p)
    (C : Subgroup (MulAut E)) (hC : Nat.Coprime p (Nat.card C)) :
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
  have : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hC h1 h2
  exact orderOf_eq_one_iff.mp this

theorem injective {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    Function.Injective ((sigma p P).comp (Sstar P T B ⊔ Bstar P A).subtype) := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  have hnorm : Bstar P A ≤ Subgroup.normalizer (Sstar P T B : Set (MulAut ↥P)) :=
    (RstarCoprime.Bstar_mono hAB).trans
      (RstarCoprime.Bstar_le_normalizer_Sstar hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction)
  have hdvd := CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product _ _ hnorm
  obtain ⟨n, hn⟩ := (SstarQuotientFaithful.isPGroup hc).exists_card_eq
  have hqp : q ≠ p := PrimeActionFixedFree.q_ne_p hc hq hAB hA
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hc.oddPrimeClassTwoAction.setting.odd (by decide)
  have hcop : Nat.Coprime p (Nat.card (Sstar P T B ⊔ Bstar P A : Subgroup (MulAut ↥P))) := by
    refine Nat.Coprime.coprime_dvd_right hdvd ?_
    rw [hn, PrimeActionFixedFree.card_image hc hq hAB hA]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) ?_
    · exact (Nat.coprime_primes hc.oddPrimeClassTwoAction.setting.prime Nat.prime_two).mpr hp2
    · exact (Nat.coprime_primes hc.oddPrimeClassTwoAction.setting.prime hq).mpr hqp.symm
  have hq' := quotientHom_injective_of_coprime hc.extraspecial hc.oddPrimeClassTwoAction.setting.exponent _ hcop
  rw [injective_iff_map_eq_one] at hq' ⊢
  intro g hg
  apply hq'
  ext x
  have := congrArg (fun f => Additive.toMul (f (Additive.ofMul x))) hg
  exact this

end CFSG.LocalAnalysis.RankThreeUC.Section5.QuotientJoinFaithful
