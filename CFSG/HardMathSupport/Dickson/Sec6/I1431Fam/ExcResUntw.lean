module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDispatch
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

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

section Untw


theorem excres_noField_untw {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hKac : ExcKac τ) (hTLin : ExcTLInner τ) (hTLin2 : ExcTLInnerTwo τ)
    (hTLout : ExcTLOther τ) {P : Type} [Group P] [Finite P] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hp3 : p ≠ 3) (hU : UntwistedChevalleyModel P τ (p ^ f)) {x y : P}
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) {J : Subgroup P} {q : ℕ}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J) (hq : IsTypeL2 q (barOf 3 J))
    (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) (hq10 : 10 ≤ q) :
    ¬ (FieldBar 2 J (MulAut.conj y) ∧ ¬ TrivBar J (MulAut.conj y)) := by
  classical
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  haveI : CharP F p := finite_field_prime_power_characteristic hp hf hFcard
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [hFcard]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨p₀, hp₀, hp₀5, hp₀p⟩ : ∃ p₀ : ℕ, p₀.Prime ∧ 5 ≤ p₀ ∧ p₀ ≠ p := by
    by_cases h5 : p = 5
    · exact ⟨7, by norm_num, by norm_num, by omega⟩
    · exact ⟨5, by norm_num, le_rfl, fun h => h5 h.symm⟩
  have hp₀F : ¬ p₀ ∣ Nat.card F := by
    rw [hFcard]
    intro h
    exact hp₀p ((Nat.prime_dvd_prime_iff_eq hp₀ hp).1 (hp₀.dvd_of_dvd_pow h))
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup τ F) = ⊤ := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact single_edge_perfect Tag.F4 F (Or.inl rfl)
    · exact single_edge_perfect Tag.E6 F (Or.inr (Or.inr (Or.inl rfl)))
    · exact single_edge_perfect Tag.E7 F (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact single_edge_perfect Tag.E8 F (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  set x' : ↥(adjointGroup τ F) := θ x with hx'
  set β : MulAut ↥(adjointGroup τ F) := MulAut.conj x' with hβdef
  have hx'3 : x' ^ 3 = 1 := by rw [hx', ← map_pow, hx3, map_one]
  have hx'1 : (x' : ModGL τ F) ≠ 1 := fun h1 => hx1 (θ.injective (by
    rw [map_one]; exact Subtype.ext h1))
  obtain ⟨S, a, ι₀, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' Nat.prime_three h3F hp₀ hp₀F (Or.inl hp₀5) hmon
      hperf β (x' : ModGL τ F)
      (baseChange_mem_adjointGroup_of_mem_inndiag (adjointGroup_le_inndiagGroup x'.2))
      (fun c => by simp [hβdef, MulAut.conj_apply]) (by rw [← Subgroup.coe_pow, hx'3]; rfl) hx'1
  have hL3 : (3 : AlgebraicClosure F) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : F) = 0 := by
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [map_natCast, map_zero]
      exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      ((CharP.cast_eq_zero_iff F p 3).1 h'))
  refine excres_noField_of_lang hτ hKac hTLin hTLin2 hTLout hL3 S (ι₀.comp θ.toMonoidHom)
    (hinj.comp θ.injective) ?_ hT hap h1 (x := x) hy3 ?_ hJ hq hq3 hq8 hq10
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 θ.surjective, Subgroup.map_top]
    exact hrange
  · intro c
    have h := hconj (θ c)
    rw [hβdef, MulAut.conj_apply] at h
    simpa [map_mul, map_inv, hx'] using h

end Untw

end CFSG.HardMathSupport.Dickson.Sec6.I1431
