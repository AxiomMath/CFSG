module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeE6Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcD4ClassMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


private theorem not_typeA_of_rank_four_card_twentyfour {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
  rintro ⟨-, h⟩
  rw [hrank, hcard] at h
  norm_num at h

theorem false_of_d4Rational_three_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hFr : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    (hE6 : τ = .E6 → S.D.q % 3 = 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ k, a k ^ 3 = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hD4 : catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) isD4any) : False := by
  obtain ⟨hrank, hcard, hstab, hinner⟩ :=
    K155X.l154d4_class_holds τ L p₀ S a i hT hap ha1 hqs hD4
  have hpL3 : ((3 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_three (by rw [ringChar.eq L 2]; norm_num)
  have hTp3 : rootDiagUnit τ a ^ 3 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.false_of_g2Class_nonAP
      Nat.prime_three S hpL3 hTp3 ha1 i
      (not_typeA_of_rank_four_card_twentyfour hrank hcard)).elim
  · exact K155X.l154d4_false_of_excl (K155X.l154d4_excl_f4 S
      ⟨Nat.prime_three, by norm_num, hT, hap, ha1, hqs⟩
      (not_typeA_of_rank_four_card_twentyfour hrank hcard)) hD4
  · have hinner' : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      have hfin : (componentRoots (rootCharHom a) i).Finite :=
        (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
      simpa [componentOrbitLength_eq_one hfin hstab, Function.iterate_one] using hinner
    exact (not_twistInner_d4Class_E6_of_mod S hFr (hE6 rfl) hT hap ha1 i hrank hcard) hinner'
  · exact S265C.DynE.false_of_d4Class_three_E7 S hpL3 hTp3 i hrank hcard
  · exact S265C.DynE.false_of_d4Class_three_E8 S hpL3 hTp3 i hrank hcard

theorem false_of_d4Rational_three_twE6 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) (hq : S.D.q % 3 = 1)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ k, a k ^ 3 = 1)
    (ha1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hD4 : catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) isD4any) : False := by
  obtain ⟨hrank, hcard, hstab, hinner⟩ :=
    K155X.l154d4_class_holds Tag.E6 L p₀ S a i hT hap ha1 hqs hD4
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  refine (not_twistInner_d4Class_twE6_of_mod S hFr hΦ hq hT hap ha1 i hrank hcard) ?_
  simpa [componentOrbitLength_eq_one hfin hstab, Function.iterate_one] using hinner

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
