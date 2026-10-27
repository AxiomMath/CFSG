module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace Up34Exc

section Data

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_unit_sq_ne_one_alg : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
  have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
  have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · simp [sub_eq_zero.1 h]
  · simp [eq_neg_of_add_eq_zero_left h]

structure InnerData (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) where
  s : ℕ
  e : ℕ
  hs0 : 0 < s
  he : 0 < e
  hq : S.D.q = 2 ^ e
  hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
    componentRoots (rootCharHom a) i
  hmin : ∀ k, 0 < k → k < s →
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
      componentRoots (rootCharHom a) i
  hinner : twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])
  σ : L ≃+* L
  z : ModGL τ L
  hσ : ∀ c, σ c = c ^ (2 ^ (e * s))
  hzZ : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))
  hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
    g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)
  hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
    iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹
  hKfin : Finite (fixSubfield σ)
  hKcard : Nat.card (fixSubfield σ) = 2 ^ (e * s)
  f : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL τ L
  hf1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range
  hf2 : f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)
  hf3 : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom a) i →
    f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i

theorem nonempty_innerData [CharP L 2] (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner) : Nonempty (InnerData S a i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ := exists_untwistT_Z S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r = 2 := CharP.eq L hchar ‹CharP L 2›
  subst hr2
  have hσ' : ∀ c, σ c = c ^ (2 ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) 2 (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (2 ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  haveI hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = 2 ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz
      (exists_unit_sq_ne_one_alg (L := L))
  exact ⟨⟨s, e, hs0, he, hq, hs, hmin, hinner, σ, z, hσ', hzZ, hnorm, hz, hfinK, hKcard, f, hf1,
    hf2, hf3⟩⟩

end Data

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
