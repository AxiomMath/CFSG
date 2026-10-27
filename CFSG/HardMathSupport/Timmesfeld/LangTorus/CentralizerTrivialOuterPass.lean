module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Pass

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_exists_lang_data {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) (z₀ : ModGL τ L) (φ₁ : ModGL τ L →* ModGL τ L),
      IsIsometry (componentRoots (rootCharHom a) i) f ∧
      (∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
        f γ ∈ posRoots (componentRoots (rootCharHom a) i)) ∧
      OuterPinned φ₁ f (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
      (∀ g, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
        z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i)) ∧
      (∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
          (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹) ∧
      (∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i)) ∧
      (¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
        ∃ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ) := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hπ := outer_isIsometry_rho S hs
  obtain ⟨w, hwW, hwpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hπ
  have hf : IsIsometry (componentRoots (rootCharHom a) i)
      (fun γ => (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (w • γ)) := hπ.comp_smul hΨ hwW
  have hwcl : w ∈ Subgroup.closure {r : WeylGroup τ |
      ∃ γ ∈ componentRoots (rootCharHom a) i, r = rootReflection γ} := by
    refine Subgroup.closure_mono ?_ hwW
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, simpleRoots_subset hβ, rfl⟩
  obtain ⟨c, hcS, hcN, hcw⟩ := exists_lift_mem_closure_reflections (L := L) i hwcl
  have hcK : c ∈ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    rootSpan_mono (fun γ hγ => hγ.1) hcS
  obtain ⟨z₀, hz₀n, hz₀⟩ := outer_exists_lang_conj S hT hs0 hcK
  have hpin : OuterPinned ((iterHom S.D.step s).comp (MulAut.conj c).toMonoidHom)
      (fun γ => (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (w • γ)) (S.D.q ^ s) := by
    have h1 := (outerPinned_conj hcN).comp (outerPinned_step S s)
    rw [weylQuotientHom_eq hcw, one_mul] at h1
    exact h1
  have hρS : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    have hmap : (rootSpan τ L (componentRoots (rootCharHom a) i)).map (iterHom S.D.step s) ≤
        rootSpan τ L (componentRoots (rootCharHom a) i) := by
      refine map_rootSpan_le_of_forall fun γ hγ t => ?_
      obtain ⟨μ, -, hμ⟩ := iter_step_pinnedX S s (hΨ.isRoot γ hγ)
      rw [iterHom_eq_iterate, hμ]
      refine pinnedX_mem_rootSpan ?_ _
      rw [← hs]
      exact Set.mem_image_of_mem _ hγ
    exact fun g hg => hmap ⟨g, hg, rfl⟩
  refine ⟨_, z₀, (iterHom S.D.step s).comp (MulAut.conj c).toMonoidHom, hf, hwpos, hpin,
    hz₀n i, fun g _ => hz₀ g, fun g hg => hρS _ (mul_mem (mul_mem hcS hg) (inv_mem hcS)),
    fun hout => ?_⟩
  by_contra hfix
  push Not at hfix
  apply hout
  refine ⟨w⁻¹, Subgroup.closure_mono ?_ (inv_mem hwW), fun γ hγ => ?_⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, simpleRoots_subset hβ, rfl⟩
  · have hβ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hwW) γ hγ
    have h1 := hfix _ hβ
    simp only [smul_inv_smul] at h1
    exact h1

theorem outer_exists_first_data {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {φ₁ : ModGL τ L →* ModGL τ L}
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ componentRoots (rootCharHom a) i) {m : ℕ} (hm : 0 < m)
    (hper : f^[m] δ = δ) (horth : ∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0) :
    (∀ j < m, ∀ B, (⇑φ₁)^[j] (rootSL2 τ L δ B) ∈ rootRankOneGroup τ L (f^[j] δ)) ∧
    (∀ j l, j < m → l < m → j ≠ l → ∀ x ∈ rootRankOneGroup τ L (f^[j] δ),
      ∀ y ∈ rootRankOneGroup τ L (f^[l] δ), Commute x y) ∧
    ∃ (σm : L ≃+* L) (X P : GL (Fin 2) L), (∀ c, σm c = c ^ (S.D.q ^
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m))) ∧
      (∀ B, (⇑φ₁)^[m] (rootSL2 τ L δ B) =
        rootSL2 τ L δ (conjSL X (Matrix.SpecialLinearGroup.map σm.toRingHom B))) ∧
      P * Matrix.GeneralLinearGroup.map σm.toRingHom P⁻¹ = X := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hδr : IsRoot τ δ := hΨ.isRoot δ hδ
  have hit : ∀ j, f^[j] δ ∈ componentRoots (rootCharHom a) i := fun j =>
    outerRoots_iterate_mem hf j hδ
  have hitneg : ∀ j, f^[j] (-δ) = -f^[j] δ := fun j =>
    (outerRoots_isIsometry_iterate hf j).neg δ hδ
  have hβ : ∀ j < m, ∀ B, (⇑φ₁)^[j] (rootSL2 τ L δ B) ∈ rootRankOneGroup τ L (f^[j] δ) := by
    intro j _ B
    rw [← iterHom_eq_iterate]
    exact (hpin.iterate j).mem_rankOne hδr (hitneg j) ⟨B, rfl⟩
  have hcommjl : ∀ j l, j < l → l < m → ∀ x ∈ rootRankOneGroup τ L (f^[j] δ),
      ∀ y ∈ rootRankOneGroup τ L (f^[l] δ), Commute x y := by
    intro j l hjl hlm
    have e : f^[l] δ = f^[l - j] (f^[j] δ) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjl.le]
    have h0 : iform (f^[j] δ) (f^[l - j] (f^[j] δ)) = 0 := by
      rw [← e, outerRoots_iform_iterate hf hδ hjl.le]
      exact horth _ (Nat.sub_pos_of_lt hjl) (lt_of_le_of_lt (Nat.sub_le l j) hlm)
    have hadd := outerRoots_not_isRoot_add_of_iform_eq_zero hΨ hf hpos (hit j) (l - j) h0
    have hsub := outerRoots_not_isRoot_sub hΨ hf hpos (hit j) (l - j)
    rw [← e] at h0 hadd hsub
    exact outer_commute_rankOne (hΨ.isRoot _ (hit j)) (hΨ.isRoot _ (hit l)) h0
      hadd hsub
  have hcomm₁ : ∀ j l, j < m → l < m → j ≠ l → ∀ x ∈ rootRankOneGroup τ L (f^[j] δ),
      ∀ y ∈ rootRankOneGroup τ L (f^[l] δ), Commute x y := by
    intro j l hj hl hjl x hx y hy
    rcases Nat.lt_or_gt_of_ne hjl with h | h
    · exact hcommjl j l h hl x hx y hy
    · exact (hcommjl l j h hj y hy x hx).symm
  obtain ⟨σm, hσm⟩ := outer_exists_frob S (s * m)
  have hσm' : ∀ t : L, t ^ ((S.D.q ^ s) ^ m) = σm t := fun t => by rw [hσm, pow_mul]
  obtain ⟨-, μ, hμ, hu⟩ := (hpin.iterate m) δ hδr
  obtain ⟨-, μ', hμ', hv⟩ := (hpin.iterate m) (-δ) (IsRoot.neg hδr)
  obtain ⟨X₀, hX₀⟩ := outer_return_fix (φ₁ := iterHom φ₁ m) σm hδr hμ hμ'
    (fun t => by rw [hu, hper, hσm']) (fun t => by rw [hv, hitneg, hper, hσm'])
  obtain ⟨hfin, hcard⟩ := outer_card_fixSubfield S σm (Nat.mul_pos hs0 hm) hσm
  have : Finite (fixSubfield σm) := hfin
  obtain ⟨P, hP⟩ := exists_twist_diag (K := fixSubfield σm) σm.toRingHom
    (fun c => by rw [hcard]; exact hσm c) X₀
  exact ⟨hβ, hcomm₁, σm, _, P, hσm, fun B => by rw [← iterHom_eq_iterate]; exact hX₀ B, hP⟩

theorem outer_commute_first_of_field_or_fixed (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hφ₁S : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ componentRoots (rootCharHom a) i) {m : ℕ} (hm : 0 < m)
    (hQ4 : 4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m))
    (hper : f^[m] δ = δ) (horth : ∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0)
    (z : ModGL τ L)
    (hCase : 3 ≤ S.D.q ∨
      (S.D.step z = z ∧
        (∀ j : KernelComponent (rootCharHom a), z ∈ Subgroup.normalizer
          (rootSpan τ L (componentRoots (rootCharHom a) j) : Set _)) ∧
        3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L δ B * z₀⁻¹) := by
  obtain ⟨hβ, hcomm₁, σm, X, P, hσm, hret, hP⟩ :=
    outer_exists_first_data S hT i hf hpos hpin hδ hm hper horth
  exact outer_commute_of_orbit_of_field_or_fixed S hτ hT i hz₀ hφ₁ hφ₁S hδ hm hQ4 (fun j => f^[j] δ)
    (fun j => outerRoots_iterate_mem hf j hδ) hβ hcomm₁ σm hσm X hret P hP z (hCase.elim Or.inl
      (fun h => Or.inr ⟨h.1, h.2.1, f, hpin, h.2.2⟩)) hcomm
theorem outer_commute_first (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (hq3 : 3 ≤ S.D.q)
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hφ₁S : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ componentRoots (rootCharHom a) i) {m : ℕ} (hm : 0 < m)
    (hQ4 : 4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m))
    (hper : f^[m] δ = δ) (horth : ∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0)
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L δ B * z₀⁻¹) := by
  exact outer_commute_first_of_field_or_fixed S hτ hT i hz₀ hφ₁ hφ₁S hf hpos hpin
    hδ hm hQ4 hper horth z (Or.inl hq3) hcomm

theorem outer_commute_second_of_field_or_fixed (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hφ₁S : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots (componentRoots (rootCharHom a) i)) {k : ℕ}
    (hb : OuterBlock f γ k)
    (hQ4 : 4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * k))
    (z : ModGL τ L)
    (hCase : 3 ≤ S.D.q ∨
      (S.D.step z = z ∧
        (∀ j : KernelComponent (rootCharHom a), z ∈ Subgroup.normalizer
          (rootSpan τ L (componentRoots (rootCharHom a) j) : Set _)) ∧
        3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x)
    (hω : ∀ (j : ℕ) (B : SL2 L),
      Commute z (z₀ * rootSL2 τ L (f^[j] (γ + f^[k] γ)) B * z₀⁻¹)) :
    ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L γ B * z₀⁻¹) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hγΨ : γ ∈ componentRoots (rootCharHom a) i := hγ.1
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγΨ
  have hk := hb.pos
  set ω := γ + f^[k] γ with hωdef
  have hωpos : ω ∈ posRoots (componentRoots (rootCharHom a) i) :=
    outerRoots_block_mem hΨ hpos hγ hb
  have hωΨ : ω ∈ componentRoots (rootCharHom a) i := hωpos.1
  have hωr : IsRoot τ ω := hΨ.isRoot ω hωΨ
  have hωfix : f^[k] ω = ω := outerRoots_block_fixed hΨ hf hpos hγ hb
  have hωorth : ∀ j, 0 < j → j < k → iform ω (f^[j] ω) = 0 := fun j hj hjk =>
    outerRoots_block_orthogonal hΨ hf hpos hγ hb hj hjk
  have hωit : ∀ j, f^[j] ω ∈ componentRoots (rootCharHom a) i := fun j =>
    outerRoots_iterate_mem hf j hωΨ
  have hωneg : ∀ j, f^[j] (-ω) = -f^[j] ω := fun j =>
    (outerRoots_isIsometry_iterate hf j).neg ω hωΨ
  have hωcomm : ∀ j, 0 < j → j < k → ∀ x ∈ rootRankOneGroup τ L ω,
      ∀ y ∈ rootRankOneGroup τ L (f^[j] ω), Commute x y := fun j hj hjk =>
    outer_commute_rankOne hωr (hΨ.isRoot _ (hωit j)) (hωorth j hj hjk)
      (outerRoots_not_isRoot_add_of_iform_eq_zero hΨ hf hpos hωΨ j (hωorth j hj hjk))
      (outerRoots_not_isRoot_sub hΨ hf hpos hωΨ j)
  obtain ⟨σk, hσk⟩ := outer_exists_frob S (s * k)
  have hσk' : ∀ t : L, t ^ ((S.D.q ^ s) ^ k) = σk t := fun t => by rw [hσk, pow_mul]
  obtain ⟨hfin, hcard⟩ := outer_card_fixSubfield S σk (Nat.mul_pos hs0 hk) hσk
  have : Finite (fixSubfield σk) := hfin
  have hFr : ∀ c, σk c = c ^ Nat.card (fixSubfield σk) := fun c => by
    rw [hcard]
    exact hσk c
  obtain ⟨-, μ, hμ, hu⟩ := (hpin.iterate k) ω hωr
  obtain ⟨-, μ', hμ', hv⟩ := (hpin.iterate k) (-ω) (IsRoot.neg hωr)
  obtain ⟨aω, haω⟩ := outer_return_fix (φ₁ := iterHom φ₁ k) σk hωr hμ hμ'
    (fun t => by rw [hu, hωfix, hσk']) (fun t => by rw [hv, hωneg, hωfix, hσk'])
  obtain ⟨B₀, x, hB₀⟩ := outer_sl2_lang (K := fixSubfield σk) σk hFr aω
  set g₀ : ModGL τ L := rootSL2 τ L ω B₀ with hg₀
  set n₀ : ModGL τ L := rootWeylSL2 τ L ω x with hn₀
  have hφk : iterHom φ₁ k g₀ = g₀ * n₀ := by
    rw [hg₀, haω, hB₀, map_mul]
    rfl
  have hhQ : ∀ j, iterHom φ₁ j g₀ ∈ rootRankOneGroup τ L (f^[j] ω) := fun j =>
    (hpin.iterate j).mem_rankOne hωr (hωneg j) ⟨B₀, rfl⟩
  have hhS : ∀ j, iterHom φ₁ j g₀ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun j =>
    outer_rankOne_le_rootSpan (hωit j) (hhQ j)
  set g : ModGL τ L := ((List.range k).map fun j => iterHom φ₁ j g₀).prod with hgdef
  have hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
    exact hhS j
  have hφg : φ₁ g = g * n₀ := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    set Pk : ModGL τ L := ((List.range k').map fun j => iterHom φ₁ (j + 1) g₀).prod with hPk
    have e1 : φ₁ g = Pk * (g₀ * n₀) := by
      have h1 : φ₁ g = ((List.range k).map fun j => iterHom φ₁ (j + 1) g₀).prod := by
        rw [hgdef, map_list_prod, List.map_map]
        rfl
      rw [h1, hk', List.range_succ, List.map_append, List.prod_append, ← hPk]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← hk', hφk]
    have e2 : g = g₀ * Pk := by
      rw [hgdef, hk', List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, hPk]
      rfl
    have hc : Commute g₀ Pk := by
      refine Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hj' : j < k' := List.mem_range.1 hj
      exact hωcomm (j + 1) (Nat.succ_pos j) (by omega) g₀ ⟨B₀, rfl⟩ _ (hhQ (j + 1))
    rw [e1, e2, ← mul_assoc, ← hc.eq]
  have hzg : Commute z (z₀ * g * z₀⁻¹) := by
    have e : z₀ * g * z₀⁻¹ =
        ((List.range k).map fun j => z₀ * iterHom φ₁ j g₀ * z₀⁻¹).prod := by
      have := map_list_prod (MulAut.conj z₀).toMonoidHom
        ((List.range k).map fun j => iterHom φ₁ j g₀)
      rw [List.map_map] at this
      exact this
    rw [e]
    refine Commute.list_prod_right _ _ fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
    obtain ⟨Bj, hBj⟩ := hhQ j
    rw [← hBj]
    exact hω j Bj
  obtain ⟨hn₀M, hn₀w⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hωr).2.2.1 x
  set φ₂ : ModGL τ L →* ModGL τ L := (MulAut.conj n₀).toMonoidHom.comp φ₁ with hφ₂def
  set f' : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ := fun β => rootReflection ω • f β with hf'def
  have hpin₂ : OuterPinned φ₂ f'
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    have h1 := hpin.comp (outerPinned_conj hn₀M)
    rw [hn₀w, mul_one] at h1
    exact h1
  set z₂ : ModGL τ L := z₀ * g with hz₂def
  have hconj : ∀ y : ModGL τ L, z₂ * y * z₂⁻¹ = z₀ * (g * y * g⁻¹) * z₀⁻¹ := fun y => by
    rw [hz₂def]
    group
  have hz₂ : ∀ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₂ * y * z₂⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    intro y hy
    rw [hconj]
    exact hz₀ _ (mul_mem (mul_mem hgS hy) (inv_mem hgS))
  have hn₀S : n₀ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    outer_rankOne_le_rootSpan hωΨ ⟨nSL x, rfl⟩
  have hφ₂S : ∀ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₂ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun y hy =>
    mul_mem (mul_mem hn₀S (hφ₁S y hy)) (inv_mem hn₀S)
  have hφ₂ : ∀ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z₂ * y * z₂⁻¹) = z₂ * φ₂ y * z₂⁻¹ := by
    intro y hy
    rw [hconj, hφ₁ _ (mul_mem (mul_mem hgS hy) (inv_mem hgS)), map_mul, map_mul, map_inv, hφg]
    show z₀ * (g * n₀ * φ₁ y * (g * n₀)⁻¹) * z₀⁻¹ =
      z₀ * g * (n₀ * φ₁ y * n₀⁻¹) * (z₀ * g)⁻¹
    group
  have hf'Ψ : ∀ β ∈ componentRoots (rootCharHom a) i, f' β ∈ componentRoots (rootCharHom a) i :=
    fun β hβ => hΨ.reflection_mem _ (hf.bijOn.mapsTo hβ) ω hωΨ
  have hf'neg : ∀ β ∈ componentRoots (rootCharHom a) i, f' (-β) = -f' β := fun β hβ => by
    show rootReflection ω • f (-β) = -(rootReflection ω • f β)
    rw [hf.neg β hβ, smul_neg]
  have hf'it := outer_iterate_neg_mem hf'Ψ hf'neg
  have horb : ∀ j, j < k → f'^[j] γ = f^[j] γ := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega)]
      have e : f (f^[j] γ) = f^[j + 1] γ := (Function.iterate_succ_apply' f j γ).symm
      show rootReflection ω • f (f^[j] γ) = f^[j + 1] γ
      rw [e]
      exact outerRoots_block_reflection_fix hΨ hf hpos hγ hb (Nat.succ_pos j) hj
  have horbk : f'^[k] γ = -γ := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', Function.iterate_succ_apply', horb k' (by omega)]
    have e : f (f^[k'] γ) = f^[k] γ := by rw [hk', Function.iterate_succ_apply']
    show rootReflection ω • f (f^[k'] γ) = -γ
    rw [e]
    exact outerRoots_block_reflection hΨ hf hpos hγ hb
  have hβ₂ : ∀ j < k, ∀ B, (⇑φ₂)^[j] (rootSL2 τ L γ B) ∈ rootRankOneGroup τ L (f^[j] γ) := by
    intro j hj B
    rw [← iterHom_eq_iterate, ← horb j hj]
    exact (hpin₂.iterate j).mem_rankOne hγr (hf'it j γ hγΨ).1 ⟨B, rfl⟩
  have hcommjl : ∀ j l, j < l → l < k → ∀ x ∈ rootRankOneGroup τ L (f^[j] γ),
      ∀ y ∈ rootRankOneGroup τ L (f^[l] γ), Commute x y := by
    intro j l hjl hlk
    have hjΨ : f^[j] γ ∈ componentRoots (rootCharHom a) i := outerRoots_iterate_mem hf j hγΨ
    have e : f^[l] γ = f^[l - j] (f^[j] γ) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjl.le]
    have h0 : iform (f^[j] γ) (f^[l - j] (f^[j] γ)) = 0 := by
      rw [← e, outerRoots_iform_iterate hf hγΨ hjl.le]
      exact hb.orth _ (Nat.sub_pos_of_lt hjl) (by omega) (by omega)
    have hadd := outerRoots_not_isRoot_add_of_iform_eq_zero hΨ hf hpos hjΨ (l - j) h0
    have hsub := outerRoots_not_isRoot_sub hΨ hf hpos hjΨ (l - j)
    rw [← e] at h0 hadd hsub
    exact outer_commute_rankOne (hΨ.isRoot _ hjΨ)
      (hΨ.isRoot _ (outerRoots_iterate_mem hf l hγΨ)) h0 hadd hsub
  have hcomm₁ : ∀ j l, j < k → l < k → j ≠ l → ∀ x ∈ rootRankOneGroup τ L (f^[j] γ),
      ∀ y ∈ rootRankOneGroup τ L (f^[l] γ), Commute x y := by
    intro j l hj hl hjl x hx y hy
    rcases Nat.lt_or_gt_of_ne hjl with h | h
    · exact hcommjl j l h hl x hx y hy
    · exact (hcommjl l j h hj y hy x hx).symm
  obtain ⟨-, ν, hν, hu₂⟩ := (hpin₂.iterate k) γ hγr
  obtain ⟨-, ν', hν', hv₂⟩ := (hpin₂.iterate k) (-γ) (IsRoot.neg hγr)
  obtain ⟨aγ, haγ⟩ := outer_return_neg (φ₁ := iterHom φ₂ k) σk hγr hν hν'
    (fun t => by rw [hu₂, horbk, hσk'])
    (fun t => by rw [hv₂, (hf'it k γ hγΨ).1, horbk, neg_neg, hσk'])
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KGD.exists_twist_antidiag (K := fixSubfield σk)
    σk.toRingHom hFr 1 aγ (RankThree.Classical.swapGL * diagUnitOne aγ)
    (by rw [coe_swapGL_mul_diagUnitOne, Units.val_one])
  have hres := outer_commute_of_orbit_of_field_or_fixed S hτ hT i hz₂ hφ₂ hφ₂S hγΨ hk hQ4 (fun j => f^[j] γ)
    (fun j => outerRoots_iterate_mem hf j hγΨ) hβ₂ hcomm₁ σk hσk _
    (fun B => by rw [← iterHom_eq_iterate]; exact haγ B) P hP z (hCase.elim Or.inl
      (fun h => Or.inr ⟨h.1, h.2.1, f', hpin₂, h.2.2⟩)) hcomm
  intro B
  have e : z₀ * rootSL2 τ L γ B * z₀⁻¹ =
      (z₀ * g * z₀⁻¹)⁻¹ * (z₂ * rootSL2 τ L γ B * z₂⁻¹) * (z₀ * g * z₀⁻¹) := by
    rw [hz₂def]
    group
  rw [e]
  exact (hzg.inv_right.mul_right (hres B)).mul_right hzg
theorem outer_commute_second (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (hq3 : 3 ≤ S.D.q)
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hφ₁S : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots (componentRoots (rootCharHom a) i)) {k : ℕ}
    (hb : OuterBlock f γ k)
    (hQ4 : 4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * k))
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x)
    (hω : ∀ (j : ℕ) (B : SL2 L),
      Commute z (z₀ * rootSL2 τ L (f^[j] (γ + f^[k] γ)) B * z₀⁻¹)) :
    ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L γ B * z₀⁻¹) := by
  exact outer_commute_second_of_field_or_fixed S hτ hT i hz₀ hφ₁ hφ₁S hf hpos hpin
    hγ hb hQ4 z (Or.inl hq3) hcomm hω

end Pass

end CFSG.HardMathSupport.Timmesfeld.LangTorus
