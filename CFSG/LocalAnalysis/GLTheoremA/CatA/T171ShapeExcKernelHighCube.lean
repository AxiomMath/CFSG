module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelHighBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernel
public import CFSG.GH74.KGroups.BalanceLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions
  CFSG.ComponentClassification.PerfectAutomorphisms
open scoped Pointwise commutatorElement


theorem frobGL_symm_apply {τ : Tag} {L : Type} [Field L] (σ : L ≃+* L) (x : ModGL τ L) :
    frobGL σ.symm (frobGL σ x) = x := by
  apply Units.ext
  change entrywise σ.symm.toRingHom
      (entrywise σ.toRingHom (x : Module.End L (RootModule τ L))) =
    (x : Module.End L (RootModule τ L))
  rw [entrywise_entrywise]
  have h : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id L := by
    ext c; exact σ.symm_apply_apply c
  rw [h, entrywise_id]

theorem frobGL_injective {τ : Tag} {L : Type} [Field L] (σ : L ≃+* L) :
    Function.Injective (frobGL (τ := τ) σ) := by
  intro x y h
  have := congrArg (frobGL σ.symm) h
  rwa [frobGL_symm_apply, frobGL_symm_apply] at this

theorem rationalComponent_le_model {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.D.model := by
  intro x hx
  have h1 : x ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_le_self _ hx
  have h2 : x ∈ S.Γ := (Subgroup.mem_inf.1 h1).2
  exact Subgroup.commutator_le_self _ h2

theorem finite_rationalComponent {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  haveI := S.finite
  exact Finite.of_injective
    (fun x => (⟨(x : ModGL τ L), rationalComponent_le_model S i x.2⟩ : ↥S.D.model))
    (fun x y h => Subtype.ext (congrArg (fun z : ↥S.D.model => (z : ModGL τ L)) h))

theorem commutator_mem_of_twist_mem_centralizer_exp
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    {F : ModGL τ L →* ModGL τ L} {Z : Subgroup (ModGL τ L)}
    (hFmem : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      F x ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hZA : Z ≤ Subgroup.centralizer
      (rootSpan τ L (componentRoots (rootCharHom a) i) : Set (ModGL τ L)))
    {C : Subgroup (ModGL τ L)}
    (hCfull : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i), F x = x → x ∈ C)
    {g₁ g₁' : ModGL τ L}
    (hg₁ : g₁ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hg₁' : g₁' ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hz₁ : F g₁ * g₁⁻¹ ∈ Z) (hz₁' : F g₁' * g₁'⁻¹ ∈ Z) :
    ⁅g₁, g₁'⁆ ∈ C := by
  set z₁ := F g₁ * g₁⁻¹
  set z₁' := F g₁' * g₁'⁻¹
  have hz₁S : z₁ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    mul_mem (hFmem g₁ hg₁) (inv_mem hg₁)
  have hz₁'S : z₁' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    mul_mem (hFmem g₁' hg₁') (inv_mem hg₁')
  have hc₁ : Commute z₁ z₁' := ((hZA hz₁) z₁' hz₁'S).symm
  have hc₂ : Commute z₁ g₁ := ((hZA hz₁) g₁ hg₁).symm
  have hc₃ : Commute z₁ g₁' := ((hZA hz₁) g₁' hg₁').symm
  have hc₄ : Commute z₁' g₁ := ((hZA hz₁') g₁ hg₁).symm
  have hc₅ : Commute z₁' g₁' := ((hZA hz₁') g₁' hg₁').symm
  have hmem : ⁅g₁, g₁'⁆ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₁') (inv_mem hg₁)) (inv_mem hg₁')
  have hfix : F ⁅g₁, g₁'⁆ = ⁅g₁, g₁'⁆ := by
    have hFg₁ : F g₁ = z₁ * g₁ := by
      rw [show z₁ = F g₁ * g₁⁻¹ from rfl]; group
    have hFg₁' : F g₁' = z₁' * g₁' := by
      rw [show z₁' = F g₁' * g₁'⁻¹ from rfl]; group
    rw [map_commutatorElement, hFg₁, hFg₁']
    rw [CFSG.GH74.KGroups.Bal.commutator_mul_mul_of_commute hc₂ hc₃ hc₄ hc₅,
      show ⁅z₁, z₁'⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr hc₁, one_mul]
  exact hCfull _ hmem hfix

theorem iterHom_frobGL_step {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) (s : ℕ) (g : ModGL τ L) :
    iterHom S.D.step s (frobGL (τ := τ) (frobeniusEquiv L 2) g) =
      frobGL (τ := τ) (frobeniusEquiv L 2) (iterHom S.D.step s g) := by
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [iterHom_succ, iterHom_succ, ih]
    exact (frobGL_step S (iterHom S.D.step n g)).symm

theorem step_mul_frobGL_fixed {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {y : ModGL τ L} (hyF : S.D.step y = y) :
    S.D.step (y * frobGL (τ := τ) (frobeniusEquiv L 2) y) =
      y * frobGL (τ := τ) (frobeniusEquiv L 2) y := by
  rw [map_mul, hyF, ← frobGL_step S y, hyF]

theorem frobGL_stab_of_stab {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {y : ModGL τ L}
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    MulAut.conj (frobGL (τ := τ) (frobeniusEquiv L 2) y) ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  haveI hRfin : Finite ↥R := finite_rationalComponent S i
  have hinj : Function.Injective (frobGL (τ := τ) (frobeniusEquiv L 2 : L ≃+* L)) :=
    frobGL_injective (τ := τ) _
  have hmapR : R.map (frobGL (τ := τ) (frobeniusEquiv L 2)) = R := by
    let fR : ↥R → ↥R := fun x =>
      ⟨frobGL (τ := τ) (frobeniusEquiv L 2) x, frobGL_mem_rationalComponent S i x.2⟩
    have hfR : Function.Injective fR := by
      intro x y h
      apply Subtype.ext
      exact hinj (congrArg Subtype.val h)
    have hsurj := Finite.injective_iff_surjective.mp hfR
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact frobGL_mem_rationalComponent S i hx
    · intro x hx
      obtain ⟨s, hs⟩ := hsurj ⟨x, hx⟩
      exact ⟨s, s.2, congrArg Subtype.val hs⟩
  change R.map (MulAut.conj (frobGL (τ := τ) (frobeniusEquiv L 2) y)).toMonoidHom = R
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ R.map (frobGL (τ := τ) (frobeniusEquiv L 2)) := by rw [hmapR]; exact hr
    obtain ⟨t, ht, rfl⟩ := hr'
    have hyt : y * t * y⁻¹ ∈ R := by
      have h := apply_mem_of_mem_subgroupStabAut hyStab ht
      simpa [MulAut.conj_apply] using h
    have hφyt : frobGL (τ := τ) (frobeniusEquiv L 2) (y * t * y⁻¹) ∈ R :=
      frobGL_mem_rationalComponent S i hyt
    simpa [map_mul, map_inv] using hφyt
  · intro r hr
    have hr' : r ∈ R.map (frobGL (τ := τ) (frobeniusEquiv L 2)) := by rw [hmapR]; exact hr
    obtain ⟨t, ht, rfl⟩ := hr'
    have hyt : y⁻¹ * t * y ∈ R := by
      have h := apply_mem_of_mem_subgroupStabAut (inv_mem hyStab) ht
      simpa [MulAut.conj_apply] using h
    refine ⟨frobGL (τ := τ) (frobeniusEquiv L 2) (y⁻¹ * t * y),
      frobGL_mem_rationalComponent S i hyt, ?_⟩
    change frobGL (τ := τ) (frobeniusEquiv L 2) y *
      frobGL (τ := τ) (frobeniusEquiv L 2) (y⁻¹ * t * y) *
        (frobGL (τ := τ) (frobeniusEquiv L 2) y)⁻¹ =
      frobGL (τ := τ) (frobeniusEquiv L 2) t
    simp only [← map_mul, ← map_inv]
    congr 1
    group

theorem excHighRankExpThree_holds :
    ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
      {p₀ p : ℕ} (S : LangSetup τ L p₀), p.Prime → p ≠ 2 →
      (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      ∀ {a : Fin τ.rank → Lˣ}, rootDiagUnit τ a ∈ S.D.torus →
      (∀ j, a j ^ p = 1) → rootDiagUnit τ a ^ p = 1 → rootDiagUnit τ a ≠ 1 →
      (τ = .G2 → 4 ≤ S.D.q) →
      ∀ (i : KernelComponent (rootCharHom a)),
      twistKind S.ρ (rootCharHom a) i = .exc →
      compRank (componentRoots (rootCharHom a) i) ≠ 4 →
      ∀ z : ↥(componentRootSpan L (rootCharHom a) i),
        z ∈ Subgroup.center (componentRootSpan L (rootCharHom a) i) →
        ((z : ModGL τ L) ^ 3 = 1) := by
  intro τ L _ _ _ p₀ p S _ _ _ a _ _ _ _ _ i hkind hr z hz
  obtain ⟨-, hs, hmin⟩ := outer_componentOrbitLength_spec S ‹rootDiagUnit τ a ∈ S.D.torus› i
  have hni : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    intro hi
    unfold twistKind at hkind
    rw [if_pos hi] at hkind
    exact TwistKind.noConfusion hkind
  have h6 : compRank (componentRoots (rootCharHom a) i) = 6 := by
    classical
    unfold twistKind at hkind
    by_cases h1 : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · rw [if_pos h1] at hkind
      cases hkind
    · rw [if_neg h1] at hkind
      by_cases h2 : (compRank (componentRoots (rootCharHom a) i) = 6 ∧
          (componentRoots (rootCharHom a) i).ncard = 72) ∨
          (compRank (componentRoots (rootCharHom a) i) = 4 ∧
            (componentRoots (rootCharHom a) i).ncard = 24 ∧
              ¬ twistInner (componentRoots (rootCharHom a) i)
                ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
                  (componentRoots (rootCharHom a) i)]))
      · rw [if_pos h2] at hkind
        rcases h2 with h | h
        · exact h.1
        · exact absurd h.1 hr
      · rw [if_neg h2] at hkind
        split_ifs at hkind
        all_goals cases hkind
  have h72 : (componentRoots (rootCharHom a) i).ncard = 72 := by
    classical
    unfold twistKind at hkind
    by_cases h1 : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · rw [if_pos h1] at hkind
      cases hkind
    · rw [if_neg h1] at hkind
      by_cases h2 : (compRank (componentRoots (rootCharHom a) i) = 6 ∧
          (componentRoots (rootCharHom a) i).ncard = 72) ∨
          (compRank (componentRoots (rootCharHom a) i) = 4 ∧
            (componentRoots (rootCharHom a) i).ncard = 24 ∧
              ¬ twistInner (componentRoots (rootCharHom a) i)
                ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
                  (componentRoots (rootCharHom a) i)]))
      · rw [if_pos h2] at hkind
        rcases h2 with h | h
        · exact h.2
        · exact absurd h.1 hr
      · rw [if_neg h2] at hkind
        split_ifs at hkind
        all_goals cases hkind
  have hdet : (Matrix.of fun β γ : simpleRoots (componentRoots (rootCharHom a) i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 3 :=
    det_cartan_eq_three_of_rank_six (isRootComponent_componentRoots i) _
      (outer_isIsometry_rho S hs).bijOn (outer_isIsometry_rho S hs).iform_eq
      (outer_isIsometry_rho S hs).neg hni h6 h72
  exact center_pow_three_eq_one_of_cartan_det_eq_three i hdet z hz

@[expose] def ExcHighRankFixedPerfectAll :
    Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀), p.Prime → p ≠ 2 →
    (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ {a : Fin τ.rank → Lˣ}, rootDiagUnit τ a ∈ S.D.torus →
    (∀ j, a j ^ p = 1) → rootDiagUnit τ a ^ p = 1 → rootDiagUnit τ a ≠ 1 →
    (τ = .G2 → 4 ≤ S.D.q) →
    ∀ (i : KernelComponent (rootCharHom a)),
    twistKind S.ρ (rootCharHom a) i = .exc →
    compRank (componentRoots (rootCharHom a) i) ≠ 4 →
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360 →
    Nonempty (TwoDExcFixedData S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))

@[expose] def ExcHighRankCubeTransfer :
    Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ},
    rootDiagUnit τ a ∈ S.D.torus → ∀ (i : KernelComponent (rootCharHom a)),
    (∀ z : ↥(componentRootSpan L (rootCharHom a) i),
      z ∈ Subgroup.center (componentRootSpan L (rootCharHom a) i) →
      ((z : ModGL τ L) ^ 3 = 1)) →
    ∀ {s : ℕ} [NeZero s],
    (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i →
    (∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i) →
    TwoDExcFixedData S a i s →
    ∀ {y : ModGL τ L},
    y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) →
    S.D.step y = y →
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

theorem excHighRankCompAction_of_fixedPerfect
    (hP : ExcHighRankFixedPerfectAll) (hC : ExcHighRankCubeTransfer) :
    ExcHighRankCompAction := by
  intro τ L _ _ _ p₀ p S hp hp2 hτ a hT hap hTp h1 hG2 i hkind hr hQS h360
    y hyZ hyF hyStab
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
    ⟨hs0.ne'⟩
  have hExp := excHighRankExpThree_holds S hp hp2 hτ hT hap hTp h1 hG2 i hkind hr
  exact hC S hT i hExp hs hmin
    (hP S hp hp2 hτ hT hap hTp h1 hG2 i hkind hr hQS h360).some hyZ hyF hyStab

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
