module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResInnerTL
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.Reduction
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResRank1Lang

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

set_option linter.unusedSectionVars false

section Dispatch


theorem excres_noField_of_lang {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hKac : ExcKac τ) (hTLin : ExcTLInner τ) (hTLin2 : ExcTLInnerTwo τ)
    (hTLout : ExcTLOther τ) {L : Type} [Field L] [IsAlgClosed L] (hL3 : (3 : L) ≠ 0)
    {p₀ : ℕ} (S : LangSetup τ L p₀) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) {x y : C} (hy3 : y ^ 3 = 1)
    (hx : ∀ c, ι (x * c * x⁻¹) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    {J : Subgroup C} {q : ℕ} (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J)
    (hq : IsTypeL2 q (barOf 3 J)) (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) (hq10 : 10 ≤ q) :
    ¬ (FieldBar 2 J (MulAut.conj y) ∧ ¬ TrivBar J (MulAut.conj y)) := by
  classical
  rintro ⟨hfld, hnt⟩
  obtain ⟨hst, hfld'⟩ := hfld
  set β : MulAut C := MulAut.conj x with hβdef
  have hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := fun c => by
    rw [hβdef, MulAut.conj_apply]
    exact hx c
  have hτG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hTame := langSetup_hTame_of_prime S Nat.prime_three (by exact_mod_cast hL3)
    (fun h => absurd h hτG2) hT ha3 h1
  have hPIL := perfectInLayer_of_langSetup_of_prime S Nat.prime_three ι hι hrange β hβ hT ha3 h1
    hTame
  obtain ⟨hcomp, hJ2⟩ := excres_isTypeL2_of_glaPComponent hPIL hJ hq
  obtain ⟨i, hQi, hJi⟩ := excres_component_eq_rational S Nat.prime_three ι hι hrange β hβ hT ha3
    hTame hcomp
  have hRi : IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    refine p6_isTypeL2_of_equiv ?_ hJ2
    exact (Subgroup.equivMapOfInjective J ι hι).trans (MulEquiv.subgroupCongr hJi)
  obtain ⟨hK1, hK2, hK3⟩ := hKac L hL3 a ha3 h1
  by_cases hn : (componentRoots (rootCharHom a) i).ncard = 2
  ·
    have hF48 : ¬ (τ = .F4 ∨ τ = .E8) := fun h => hK2 h i hn
    have hE67 : τ = .E6 ∨ τ = .E7 := by
      rcases hτ with h | h | h | h
      · exact absurd (Or.inl h) hF48
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inr h) hF48
    have hs1 : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := by
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i 1
      have hnj : (componentRoots (rootCharHom a) j).ncard = 2 := by
        rw [hj, Function.iterate_one, Set.ncard_image_of_injective _ S.ρ.injective]
        exact hn
      have hij := hK3 hE67 i j hn hnj
      subst hij
      simpa using hj.symm
    obtain ⟨K', hfin, β', z, hβ', hK4, hθR⟩ := excres_rankOne_explicit S hT i hn hs1 hQi
    have hτE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hE67 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range :=
      hrange ▸ ((langSubnormal_of_mem_torus S hT i).1.trans inf_le_left)
    obtain ⟨w, hw, hwj⟩ := excres_inner_on_rankOne hτE K' β' z ι hι
      (fun g => hRΓ (hθR ▸ ⟨g, rfl⟩))
      (J := J) (fun p => by
        rw [hθR, ← hJi]
        exact (Subgroup.mem_map_iff_mem hι).symm)
      hy3 (fun p => by
        have := mem_stabAut.1 hst p
        simpa [MulAut.conj_apply] using this)
    exact false_of_inner_on_fieldBar hst (by rw [← map_pow, hy3, map_one]) hfld' hnt
      ⟨w, hw, fun y' hy' => by simpa [MulAut.conj_apply] using hwj y' hy'⟩ hJ hq hq3 hq8
  ·
    rcases hK1 i with hn' | hA2
    · exact hn hn'
    · by_cases hk : twistKind S.ρ (rootCharHom a) i = .inner
      · exact excres_inner_not_typeL2 hτ hTLin hTLin2 hL3 S hT i hk hA2 hQi hq10 hRi
      · exact hTLout L p₀ S a hT ha3 h1 i hk hQi q hq10 hRi

end Dispatch

end CFSG.HardMathSupport.Dickson.Sec6.I1431
