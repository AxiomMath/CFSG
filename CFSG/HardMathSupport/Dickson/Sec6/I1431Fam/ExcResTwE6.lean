module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDispatch
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.RecipeExcLang CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false

section TwE6


theorem excres_noField_twE6 (hKac : ExcKac Tag.E6) (hTLin : ExcTLInner Tag.E6)
    (hTLin2 : ExcTLInnerTwo Tag.E6) (hTLout : ExcTLOther Tag.E6) {P : Type} [Group P] [Finite P]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp3 : p ≠ 3)
    (hE : TwistedChevalleyModel P TwistTag.E6 (p ^ f)) {x y : P} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) {J : Subgroup P} {q : ℕ}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J) (hq : IsTypeL2 q (barOf 3 J))
    (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) (hq10 : 10 ≤ q) :
    ¬ (FieldBar 2 J (MulAut.conj y) ∧ ¬ TrivBar J (MulAut.conj y)) := by
  classical
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv hp hf hE
  haveI : CharP K p := finite_field_prime_power_characteristic hp (k := f * 2) (by omega)
    (by rw [hK, ← pow_mul])
  obtain ⟨p₀, hp₀, hp₀5, hp₀p⟩ : ∃ p₀ : ℕ, p₀.Prime ∧ 5 ≤ p₀ ∧ p₀ ≠ p := by
    by_cases h5 : p = 5
    · exact ⟨7, by norm_num, by norm_num, by omega⟩
    · exact ⟨5, by norm_num, le_rfl, fun h => h5 h.symm⟩
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Nat.prime_three (by norm_num)
  set x' : ↥(twistedE6RootGroup K σ) := e.symm x with hx'
  set β : MulAut ↥(twistedE6RootGroup K σ) := MulAut.conj x' with hβdef
  have hx'3 : x' ^ 3 = 1 := by rw [hx', ← map_pow, hx3, map_one]
  have hx'1 : (x' : ModGL TwistTag.E6.tag K) ≠ 1 := fun h1 => hx1 (e.symm.injective (by
    rw [map_one]; exact Subtype.ext h1))
  obtain ⟨S, a, ι₀, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hp hf hK σ hσ Nat.prime_three (Ne.symm hp3) hp₀
      hp₀p (Or.inl hp₀5) hmon β (x' : ModGL TwistTag.E6.tag K) (Subgroup.mem_sup_left x'.2)
      (fun c => by simp [hβdef, MulAut.conj_apply]) (by rw [← Subgroup.coe_pow, hx'3]; rfl) hx'1
  have hL3 : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by
      apply (algebraMap K (AlgebraicClosure K)).injective
      rw [map_natCast, map_zero]
      exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K p 3).1 h'))
  refine excres_noField_of_lang (Or.inr (Or.inl rfl)) hKac hTLin hTLin2 hTLout hL3 S
    (ι₀.comp e.symm.toMonoidHom) (hinj.comp e.symm.injective) ?_ hT hap h1 (x := x) hy3 ?_ hJ hq
    hq3 hq8 hq10
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top]
    exact hrange
  · intro c
    have h := hconj (e.symm c)
    rw [hβdef, MulAut.conj_apply] at h
    simpa [map_mul, map_inv, hx'] using h

end TwE6

end CFSG.HardMathSupport.Dickson.Sec6.I1431
