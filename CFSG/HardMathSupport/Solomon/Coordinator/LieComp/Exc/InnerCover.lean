module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeACover
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit
import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false

@[expose] def InnerRecog (ℓ : ℕ) (C : Type) [Group C] : Prop :=
  ∃ (X : Type) (_ : Group X), LieFactorData ℓ X ∧
    IsEmpty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) ∧
    ∃ g : X →* C, Function.Surjective g ∧ g.ker ≤ Subgroup.center X

section Cover


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem exists_inner_cover (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)])) :
    ∃ σ : L ≃+* L, Finite ↥(fixSubfield σ) ∧
      Nat.card ↥(fixSubfield σ) = S.D.q ^ componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i) ∧
      ∃ f : ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) →* ModGL τ L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) ∧
        (⁅componentRootSpan (fixSubfield σ) (rootCharHom ta) i,
            componentRootSpan (fixSubfield σ) (rootCharHom ta) i⁆ =
            componentRootSpan (fixSubfield σ) (rootCharHom ta) i →
          f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  exact ⟨σ, hfinK, by rw [hKcard, hq, ← pow_mul], f, hf1, hker, hf2⟩

theorem rationalLieType_of_innerRecog (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      InnerRecog (ringChar L) ↥(componentRootSpan K (rootCharHom ta) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨σ, hfin, -, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  obtain ⟨X, _, hX, hA6, g, hg, hgk⟩ := hrec (fixSubfield σ) hfin
  have hCperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := by
    have hcomm : commutator ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) = ⊤ := by
      have h1 := congrArg (Subgroup.map g) hX.perfect
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective g hg] at h1
      rw [commutator_def]
      exact h1
    exact Group.isPerfect_def.2 hcomm
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hCperf)) hf1
  let g' : X →* ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    (f.comp g).codRestrict _ (fun x => by
      rw [← hRf]
      exact ⟨g x, rfl⟩)
  have hg'surj : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ : y ∈ f.range := hRf ▸ hy
    obtain ⟨x, rfl⟩ := hg c
    exact ⟨x, Subtype.ext hc⟩
  have hg'ker : g'.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : f (g x) = 1 := congrArg Subtype.val hx
    have h2 : g x ∈ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
      hker h1
    rw [← comap_center_of_surjective hX.perfect g hg hgk]
    exact h2
  exact rationalLieType_of_cover _ hX g' hg'surj hg'ker hA6

end Cover

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
