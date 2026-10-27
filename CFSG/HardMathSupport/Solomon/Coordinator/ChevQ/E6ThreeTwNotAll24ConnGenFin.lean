module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenRank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open Matrix
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Fin

theorem four_le_of_prime_pow {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hne : r ^ e ≠ 2)
    (h3 : r ≠ 3) : 4 ≤ r ^ e := by
  have hr2 := hr.two_le
  by_cases h2 : r = 2
  · subst h2
    rcases Nat.lt_or_ge e 2 with h | h
    · have : e = 1 := by omega
      subst this
      simp at hne
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h
  · have h4 : r ≠ 4 := fun h => by
      subst h
      exact absurd hr (by decide)
    calc 4 ≤ r := by omega
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ e := Nat.pow_le_pow_right hr.pos he

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem classPeel_of_conn (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hq2 : S.D.q ≠ 2)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨ (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a)) :
    ClassPeel S i ∧ ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  classical
  obtain ⟨m, hm, ψ, σ, π, hψ, hΨ, hπ1, hs1, -, hS1⟩ :=
    KSConn.conn_class_unitary S hFr hΦ h3 hT hap h3q hk i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hΨ] at hγ ⊢
    obtain ⟨x, y, hxy, rfl⟩ := hγ
    exact ⟨π y, π x, fun h => hxy (π.injective h).symm, hπ1 x y hxy⟩
  have hrange : ψ.range = rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    rw [hψ.range, hΨ]
  refine ⟨?_, hstab⟩
  have hr3 : r ≠ 3 := fun h => by
    subst h
    exact h3 (CharP.cast_eq_zero L 3)
  rcases hm with rfl | rfl | rfl
  ·
    obtain ⟨h1, hn, -⟩ := hS1 rfl
    have hq4 : 4 ≤ r ^ e := four_le_of_prime_pow hr he (by rw [← hq]; exact hq2) hr3
    exact ⟨rankOne_class_quasisimple S hT i h1 hn hs1 hr hchar he hq hq4,
      fun Q' hFQ' hHQ' hQQ' x hx hFx =>
        rankOne_class_peel S h3 hT i h1 hn hs1 hr hchar he hq hq4 hFQ' hHQ' hQQ' hx hFx⟩
  ·
    have hnq : (4 + 1, r ^ e) ≠ (3, 2) := fun h => by
      have := congrArg Prod.fst h
      simp at this
    exact ⟨unitary_class_quasisimple S hT i (by norm_num) hψ hΨ π hπ1 hs1 hr hchar he hq hnq,
      fun Q' hFQ' hHQ' hQQ' x hx hFx =>
        unitary_class_peel S h3 hT i (by norm_num) hψ hΨ π hπ1 hr hchar he hq hnq hFQ' hHQ'
          (by rw [hrange]; exact hQQ') (by rw [hrange]; exact hx) hFx⟩
  ·
    have hnq : (5 + 1, r ^ e) ≠ (3, 2) := fun h => by
      have := congrArg Prod.fst h
      simp at this
    exact ⟨unitary_class_quasisimple S hT i (by norm_num) hψ hΨ π hπ1 hs1 hr hchar he hq hnq,
      fun Q' hFQ' hHQ' hQQ' x hx hFx =>
        unitary_class_peel S h3 hT i (by norm_num) hψ hΨ π hπ1 hr hchar he hq hnq hFQ' hHQ'
          (by rw [hrange]; exact hQQ') (by rw [hrange]; exact hx) hFx⟩

theorem twE6ConnFixed_A {n : ℕ} (hn : n = 22 ∨ n = 30) : TwE6ConnFixed n := by
  intro L _ _ p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk x hx hFx
  have hk' : (kernelRoots (rootCharHom a)).ncard = 22 ∨
      (kernelRoots (rootCharHom a)).ncard = 30 := by
    rw [hk]
    exact hn
  have hall : ∀ i : KernelComponent (rootCharHom a), ClassPeel S i := fun i =>
    (classPeel_of_conn S hFr hΦ h3 hT hap h3q hq2 hk' i).1
  have hstab := fun i : KernelComponent (rootCharHom a) =>
    (classPeel_of_conn S hFr hΦ h3 hT hap h3q hq2 hk' i).2
  exact fixed_of_classPeel S hall hstab x hx hFx

end Fin

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
