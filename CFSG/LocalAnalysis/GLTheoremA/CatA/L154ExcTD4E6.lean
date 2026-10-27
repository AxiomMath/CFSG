module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Exact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgClass

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenCenterQuot LargeEvenCenterMk
  LargeEvenChevH LargeEvenChevIDImage LargeEvenChevGL LargeEvenIsRoot LargeEvenCartanE
  LargeEvenLabel LargeEvenLieTag LargeEvenRawDatum LargeEvenRecipeChevalley LargeEvenTwistedH)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType (markTag markChar MarkedModel)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup mem_fixedGroup sigma sigma_xm_single)
open CFSG.StandardType.Canonical (largeEvenMarking_mono)
open CFSG.Open (StatedLieTag)

section Marking


theorem l154td4_exact_of_marking {X : Type} [Group X] {P₀ : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X fun lab _ _ _ _ _ => P₀ lab)
    (hP : ∀ lab, P₀ lab → markTag lab ≠ .trialityD4 ∧ markChar lab = 2) :
    L154ExactModel (X ⧸ Subgroup.center X) := by
  obtain ⟨lab, -, R, _, I, F, θ, -, -, hP', hMM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel h
  exact l154td4_exact_of_lieModel (hP lab hP').2 (hP lab hP').1 (MarkedModel.of_mulEquiv θ.symm hMM)

end Marking

section Inner

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K] [Finite K]

theorem l154td4_e6_marking_inner {M : Type} [Group M] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {j : ModGL τ K →* M} (hj : Function.Injective j)
    (hX : CFSG.IsQuasisimple ↥((subsystemGroup τ K (e6Set τ)).map j)) :
    LargeEvenMarking ↥((subsystemGroup τ K (e6Set τ)).map j) fun lab _ _ _ _ _ =>
      lab.tag = .E6 := by
  obtain ⟨hqC, θ, -⟩ := l154_realized_of_map hj hX (e6Ad τ K) e6Ad_surjective e6Ad_ne_one
    (I := (∅ : Set (MulAut (↥(adjointGroup Tag.E6 K) ⧸ Subgroup.center ↥(adjointGroup Tag.E6 K)))))
    (fun φ hφ => absurd hφ (by simp))
  refine ⟨hX.1.commutator_eq_top, ⟨.E6, 0, f⟩, ⟨hf, rfl⟩, ?_⟩
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  exact l154_chev_untransport (τ := Tag.E6)
    (Q := fun R _ I => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ' : ↥((subsystemGroup τ K (e6Set τ)).map j) ⧸
          Subgroup.center ↥((subsystemGroup τ K (e6Set τ)).map j) ≃* R,
        (⟨.E6, 0, f⟩ : LargeEvenLabel).tag = .E6)
    ⟨hqC.2.1, hqC.2.2, θ, rfl⟩

end Inner

section Outer

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ}
  [Finite (K2 L 2 f)]

theorem l154td4_e6_marking_outer {M : Type} [Group M] (hf : 1 ≤ f)
    {j : ModGL τ (K2 L 2 f) →* M} (hj : Function.Injective j)
    (hX : CFSG.IsQuasisimple ↥(j.comp (e6Iota τ L f)).range) :
    LargeEvenMarking ↥(j.comp (e6Iota τ L f)).range fun lab _ _ _ _ _ => lab.tag = .twE6 := by
  obtain ⟨hqC, θ, -⟩ := l154_realized_of_range hj e6Iota_injective hX (e6AdT L f hf)
    (e6AdT_surjective hf) (e6AdT_ne_one hf)
    (I := (∅ : Set (MulAut (LargeEvenCenterQuot
      (twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f))))))
    (fun φ hφ => absurd hφ (by simp))
  refine ⟨hX.1.commutator_eq_top, ⟨.twE6, 0, f⟩, ⟨hf, rfl⟩, ?_⟩
  refine ⟨K2 L 2 f, inferInstance, inferInstance, card_K2_two hf, ?_⟩
  exact l154_tw_untransport (t := TwistTag.E6) (theta2Equiv L f) (fun c => theta2Equiv_pow c)
    (twisted_commutator_eq_C0 hf)
    (Q := fun R _ I => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ' : ↥(j.comp (e6Iota τ L f)).range ⧸ Subgroup.center ↥(j.comp (e6Iota τ L f)).range ≃* R,
        (⟨.twE6, 0, f⟩ : LargeEvenLabel).tag = .twE6)
    ⟨hqC.2.1, hqC.2.2, θ, rfl⟩

end Outer

section Form

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p : ℕ}

theorem l154td4_e6_of_form (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154ExactClass S i := by
  obtain ⟨f, n₁, g, π, hf, hstd, hX⟩ := l154_layer_data S haT i v hΨ
  have key : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6 := by
    rcases hstd.hπ with h1 | h1
    · haveI : Finite (frobeniusFixedField L 2 f) := finite_frobeniusFixedField hf
      have hL := hstd.stdLayer_eq_map_of_one (f := f) h1
      rw [hL, Subgroup.map_map] at hX
      have hj : Function.Injective ((MulAut.conj g).toMonoidHom.comp
          (baseChangeGL (frobeniusFixedField L 2 f).subtype)) :=
        (MulAut.conj g).injective.comp (baseChangeGL_injective _)
      rw [hX] at hqi ⊢
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inl h)
        (l154td4_e6_marking_inner hf (card_frobeniusFixedField_pow hf) hj hqi)
    · haveI : Finite (K2 L 2 f) := finite_frobeniusFixedField (by omega)
      haveI := certificate123_of_kernel
      have hL := hstd.stdLayer_eq_range_of_rho (f := f) h1
      have hpsi : psi2 τ L 2 f = (baseChangeGL (frobeniusFixedField L 2 (2 * f)).subtype).comp
          (e6Iota τ L f) := rfl
      rw [hL, MonoidHom.map_range, hpsi, ← MonoidHom.comp_assoc] at hX
      have hj : Function.Injective ((MulAut.conj g).toMonoidHom.comp
          (baseChangeGL (frobeniusFixedField L 2 (2 * f)).subtype)) :=
        (MulAut.conj g).injective.comp (baseChangeGL_injective _)
      rw [hX] at hqi ⊢
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => Or.inr h)
        (l154td4_e6_marking_outer hf hj hqi)
  refine l154td4_exact_of_marking key ?_
  rintro lab (h | h) <;> simp [markTag, markChar, h]

end Form

section Main

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_e6Class {τ : Tag} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ k, a k ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (h6 : L154E6Class a i) : L154ExactClass S i := by
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := l154_rootDiagUnit_pow hap
  have hle := l154_compRank_le (componentRoots (rootCharHom a) i)
  have h6r := h6.1
  cases τ with
  | G2 =>
    exfalso
    have hr : Tag.G2.rank = 2 := rfl
    omega
  | F4 =>
    exfalso
    have hr : Tag.F4.rank = 4 := rfl
    omega
  | D4 =>
    exfalso
    have hr : Tag.D4.rank = 4 := rfl
    omega
  | E6 => exact (l154_not_E6 ha1 i h6).elim
  | E7 =>
    obtain ⟨v, hv⟩ := l154_form_E7 S hp hpL hTp i h6
    exact l154td4_e6_of_form S hT i v hv hqi
  | E8 =>
    obtain ⟨v, hv⟩ := l154_form_E8 S hp hpL hTp i h6
    exact l154td4_e6_of_form S hT i v hv hqi

end Main

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
