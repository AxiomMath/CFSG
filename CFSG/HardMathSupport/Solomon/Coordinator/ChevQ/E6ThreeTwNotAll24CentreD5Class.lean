module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Kind
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Datum
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Class


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem d5_class_strongModel (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 40) (i : KernelComponent (rootCharHom a)) :
    ∃ r e : ℕ, ringChar L = r ∧ S.D.q = r ^ e ∧
      DStrongModel (rationalComponent S.ρ S.Γ (rootCharHom a) i) 5 r e := by
  classical
  obtain ⟨u, hu, hρ⟩ := exists_rho_neg_weyl_of_conn S hFr hΦ hT hap h3q (by rw [hk]; simp)
  obtain ⟨v, C, hC, hΨ, hn, hrk⟩ := d5_class_data h3 hap hk i
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  have hΨk : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    Set.eq_of_subset_of_ncard_le (fun γ hγ => hγ.1) (by rw [hk, hn]) hfin
  have hu' : u ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
      ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ} :=
    kernelReflectionGroup_le_closure (by rw [hΨk]) hu
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hΨk] at hγ ⊢
    obtain ⟨hγr, hγ1⟩ := hγ
    refine ⟨(S.frob.isRoot_iff γ).2 hγr, ?_⟩
    have h1 : rootChar a γ = 1 := hγ1
    have h2 := S.frob.rootChar_eq a hT γ hγr
    change rootChar a (S.ρ γ) = 1
    rw [h2, h1, one_pow]
  have hlen : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one (hΨk ▸ hfin) hstab
  have hno := not_exists_neg_D5 hC v
  rw [← hΨ] at hno
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD := by
    unfold twistKind
    rw [hlen]
    have hni : ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : _ → _)^[1]) := by
      rw [Function.iterate_one]
      exact not_twistInner_of_neg hu' (fun γ hγ => hρ γ (hΨk ▸ hγ).1) hno
    rw [if_neg hni, if_neg (by rw [hrk, hn]; omega),
      if_pos ⟨by rw [hrk]; omega, by rw [hrk, hn]⟩]
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h := map_pow (rootDiagUnitHom Tag.E6 L) a 3
    rw [show a ^ 3 = 1 from funext hap, map_one] at h
    exact h.symm
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  have hrc : ringChar L = r := ringChar.eq L r
  have hQ : ringChar L = 2 ∨ 5 ≤ S.D.q := by
    by_cases hr2 : r = 2
    · exact Or.inl (hrc.trans hr2)
    · right
      have hr3 : 3 ≤ r := by
        have := hr.two_le
        omega
      have hq3 : 3 ≤ S.D.q := by
        rw [hq]
        exact le_trans hr3 (Nat.le_self_pow (by omega) r)
      omega
  obtain ⟨r', e', m, hr', hq', hm5, hm, hmodel⟩ := strongModel_of_dClassTwistedG_E6 S
    Nat.prime_three (by exact_mod_cast h3) hT hTp i (by omega) (by rw [hrk, hn]) hkind
    (fun r q => r = 2 ∨ 5 ≤ q) (twoDChainRecogSAll_even_or_five L) hQ
  rw [hrk] at hm
  subst hm
  exact ⟨r', e', hr', hq', hmodel⟩

end Class

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
