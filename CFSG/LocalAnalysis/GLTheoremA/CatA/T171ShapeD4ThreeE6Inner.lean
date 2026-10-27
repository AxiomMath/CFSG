module

public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoE6D4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.ExcThreeAtTwo
open CFSG.RankThree.PartOne.KE (d4Nodes)
open CFSG.RankThree.Chevalley (rootChar_pow_eq_one)

set_option linter.unusedSectionVars false

variable {L : Type} [Field L]
  [IsAlgClosed L] {p₀ : ℕ}

theorem rootDiagUnit_eq_one_of_inv_weyl_d4 {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    {u : WeylGroup Tag.E6}
    (hinv : ∀ β, IsRoot Tag.E6 β → rootChar a (u • β) = (rootChar a β)⁻¹)
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} {v : WeylGroup Tag.E6}
    (hv : Ψ = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hker : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ ∧ rootChar a γ = 1) {x : WeylGroup Tag.E6}
    (hx : x ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ})
    (hux : ∀ γ ∈ Ψ, u • γ = x • γ) : rootDiagUnit Tag.E6 a = 1 := by
  have hy : v⁻¹ * (x⁻¹ * u) * v = 1 := by
    have hfix : ∀ j : Fin Tag.E6.rank, j ∈ d4Nodes Tag.E6 →
        (v⁻¹ * (x⁻¹ * u) * v) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
      intro j hj
      have hmem : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ Ψ := by
        rw [hv]
        exact ⟨_, single_mem_parabolicRoots hj, rfl⟩
      rw [mul_smul, mul_smul, mul_smul, hux _ hmem, inv_smul_smul, inv_smul_smul]
    exact eq_one_of_fix_d4Nodes hfix
  have hux' : u = x := by
    have h1' : x⁻¹ * u = 1 := by
      have := congrArg (fun y => v * y * v⁻¹) hy
      simpa [mul_assoc] using this
    exact (inv_mul_eq_one.1 h1').symm
  have hall : ∀ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β → rootChar a β = 1 := by
    intro β hβ
    have e1 := hinv β hβ
    rw [hux', closure_rootReflection_le_rootCharStabilizer hker hx β] at e1
    have h2 : rootChar a β ^ 2 = 1 := by
      rw [eq_inv_iff_mul_eq_one] at e1
      simpa [sq] using e1
    calc rootChar a β = rootChar a β ^ 3 * (rootChar a β ^ 2)⁻¹ := by group
      _ = 1 := by rw [rootChar_pow_eq_one hap β, h2]; simp
  have ha : a = 1 := by
    funext j
    have h := hall (Pi.single j 1) (isRoot_single _ _)
    have h2 := rootChar_nsmul_single a j 1
    rw [one_smul, pow_one] at h2
    rw [h2] at h
    exact h
  rw [ha]
  exact rootDiagUnit_one

theorem d4Neg_smul_single :
    ((simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3) •
        (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 1 1 ∧
      ((simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3) •
        (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 2 1 ∧
      ((simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3) •
        (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 3 1 ∧
      ((simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3) •
        (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = -Pi.single 4 1 := by
  simp only [pow_succ, pow_zero, one_mul, mul_smul, simple_smul]
  decide

theorem d4Neg_mem :
    (simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3 ∈
      parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
  have hs : ∀ j : Fin Tag.E6.rank, j ∈ d4Nodes Tag.E6 →
      simple Tag.E6 j ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) :=
    fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩
  refine pow_mem (mul_mem (mul_mem (mul_mem (hs 1 ?_) (hs 2 ?_)) (hs 4 ?_)) (hs 3 ?_)) 3 <;>
    exact ⟨by decide, by decide⟩

theorem d4Neg_smul_parabolicRoot {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    ((simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3) • α = -α := by
  obtain ⟨h1, h2, h3, h4⟩ := d4Neg_smul_single
  have hr : Tag.E6.rank = 6 := rfl
  have h0 : α 0 = 0 := hα.2 0 (by simp [d4Nodes])
  have h5 : α 5 = 0 := hα.2 5 (by simp [d4Nodes, hr])
  have hdec : α = α 1 • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) + α 2 • Pi.single 2 1 +
      α 3 • Pi.single 3 1 + α 4 • Pi.single 4 1 := by
    funext k
    fin_cases k <;> simp (config := { decide := true }) [h0, h5, Pi.single_apply] <;>
      first | rfl | exact h0 | exact h5
  rw [hdec]
  simp only [smul_add, smul_comm _ (α _), h1, h2, h3, h4, smul_neg, neg_add]


theorem not_twistInner_d4Class_E6_of_mod (S : LangSetup Tag.E6 L p₀)
    (hFr : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    (hq : S.D.q % 3 = 2) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  obtain ⟨v, hv, hρ⟩ := exists_pinned_d4Class_E6 S hT hap h1 i hrank hcard
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one]
  rintro ⟨x, hx, hρx⟩
  obtain ⟨Fr, hFr', hΦ'⟩ := hFr
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ := fun γ hγ =>
    S.rho_eq_smul_of_frob hFr' hΦ' hn hγ
  have hinv : ∀ β, IsRoot Tag.E6 β → rootChar a (w • β) = (rootChar a β)⁻¹ := by
    intro β hβ
    have h3 := rootChar_pow_eq_one hap β
    have hq' : S.D.q = 3 * (S.D.q / 3) + 2 := by omega
    rw [← hρw β hβ, S.frob.rootChar_eq a hT β hβ, hq', pow_add, pow_mul, h3, one_pow, one_mul,
      eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h3
  have hker : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E6 γ ∧ rootChar a γ = 1 :=
    fun γ hγ => ⟨hγ.1.1, hγ.1.2⟩
  exact h1 (rootDiagUnit_eq_one_of_inv_weyl_d4 hap hinv hv hker hx
    fun γ hγ => (hρw γ (hker γ hγ).1).symm.trans (hρx γ hγ))


theorem not_twistInner_d4Class_twE6_of_mod (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hq : S.D.q % 3 = 1) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  obtain ⟨v, hv, hρ⟩ := exists_pinned_d4Class_E6 S hT hap h1 i hrank hcard
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one]
  rintro ⟨x, hx, hρx⟩
  obtain ⟨u, hu⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.exists_weyl_rho_eq_neg S hFr hΦ
  have hinv : ∀ β, IsRoot Tag.E6 β → rootChar a (u • β) = (rootChar a β)⁻¹ := by
    intro β hβ
    have h3 := rootChar_pow_eq_one hap β
    have hq' : S.D.q = 3 * (S.D.q / 3) + 1 := by omega
    have huβ : u • β = -(S.ρ β) := by rw [hu β hβ, neg_neg]
    rw [huβ, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.rootChar_neg_aux,
      S.frob.rootChar_eq a hT β hβ, hq', pow_add, pow_mul, h3, one_pow, one_mul, pow_one]
  have hker : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E6 γ ∧ rootChar a γ = 1 :=
    fun γ hγ => ⟨hγ.1.1, hγ.1.2⟩
  set y0 := (simple Tag.E6 1 * simple Tag.E6 2 * simple Tag.E6 4 * simple Tag.E6 3) ^ 3 with hy0
  have hyΨ : v * y0 * v⁻¹ ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
      ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ} := by
    rw [hv]
    exact conj_mem_closure_rootReflection v d4Neg_mem
  have hyneg : ∀ γ ∈ componentRoots (rootCharHom a) i, (v * y0 * v⁻¹) • γ = -γ := by
    intro γ hγ
    rw [hv] at hγ
    obtain ⟨α, hα, rfl⟩ := hγ
    rw [mul_smul, mul_smul, inv_smul_smul, d4Neg_smul_parabolicRoot hα, smul_neg]
  refine h1 (rootDiagUnit_eq_one_of_inv_weyl_d4 hap hinv hv hker (mul_mem hyΨ hx) ?_)
  intro γ hγ
  have hxγ : x • γ ∈ componentRoots (rootCharHom a) i := by
    rw [← hρx γ hγ]
    exact hρ γ hγ
  rw [mul_smul, hyneg _ hxγ, ← hρx γ hγ, hu γ (hker γ hγ).1, neg_neg]

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
