module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResRank1
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem excres_norm_one {G : Type*} [Group G] {F : G →* G} (P : CycFamily F 1) (y : P.S 0) :
    P.norm y = (y : G) := by
  unfold CycFamily.norm
  rw [MonoidHom.comp_apply]
  have hd : P.diag y = Pi.mulSingle (0 : ZMod 1) (P.iter 0 y) := by
    funext k
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    simp [CycFamily.diag]
  rw [hd, CycFamily.mu_mulSingle]
  simp [CycFamily.coe_iter]

section Explicit


theorem excres_twistInner_of_rankOne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {Ψ : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hΨ : Ψ = {β, -β}) (hs1 : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ) :
    twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
  have hβΨ : β ∈ Ψ := by rw [hΨ]; simp
  have hρβ : S.ρ β ∈ Ψ := by
    rw [← hs1]
    exact Set.mem_image_of_mem _ hβΨ
  rw [hΨ] at hρβ
  have hneg : ∀ γ, S.ρ (-γ) = -S.ρ γ := fun γ => S.frob.neg_eq γ
  rcases hρβ with h | h
  · refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
    rw [hΨ] at hγ
    rcases hγ with rfl | rfl
    · simpa using h
    · simp [hneg, h]
  · have h := Set.mem_singleton_iff.1 h
    refine ⟨rootReflection β, Subgroup.subset_closure ⟨β, hβΨ, rfl⟩, fun γ hγ => ?_⟩
    rw [hΨ] at hγ
    rcases hγ with rfl | rfl
    · simpa [rootReflection_smul_self hβ] using h
    · simp [hneg, h, rootReflection_smul_self hβ]


theorem excres_rankOne_explicit {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hs1 : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ (K' : Subfield L) (_ : Finite K') (β : Fin τ.rank → ℤ) (z : ModGL τ L),
      IsRoot τ β ∧ 4 ≤ Nat.card K' ∧
      (excresTheta τ K' β z).range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  obtain ⟨β, hβ, hΨ⟩ := exists_pair_of_rank_one i hn
  have hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by simpa using hs1
  have hmin : ∀ k, 0 < k → k < 1 → (S.ρ : (Fin τ.rank → ℤ) → _)^[k] ''
      componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i :=
    fun k hk hk1 => absurd hk1 (by omega)
  have hinner := excres_twistInner_of_rankOne S hβ hΨ hs1
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i (s := 1) Nat.one_pos hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ e) := fun c => by rw [hσ, hq, pow_one]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e) he σ hσ'
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
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      (CFSG.LieType.Chevalley.rootSL2 τ (fixSubfield σ) β).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hΨ]
    simp only [rootSpan, iSup_insert, iSup_singleton]
  let eSL : SL(2, ↥(fixSubfield σ)) ≃*
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    (MonoidHom.ofInjective (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (K := ↥(fixSubfield σ)) β)).trans (MulEquiv.subgroupCongr hC.symm)
  have hQ4 : 4 ≤ r ^ e := by
    by_contra hQ4
    exfalso
    have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
    haveI : Group.IsSolvable SL(2, ↥(fixSubfield σ)) :=
      isSolvable_specialLinear_two_of_card_le_three hKle
    haveI : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
      Group.isSolvable_of_isSolvable_injective (f := eSL.symm.toMonoidHom) eSL.symm.injective
    haveI : Group.IsSolvable ↥f.range :=
      Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    haveI : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isSolvable_of_isQuasisimple hQS
      inferInstance
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' he hQ4
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id'] <;> rfl
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  have hιC : ∀ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hx, rfl⟩
  have hιS : ∀ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      ι x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    fun x hx => CQ_le_rootSpan σ i (hιC x hx)
  let θ' : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL τ L :=
    (MulAut.conj z).toMonoidHom.comp (ι.comp (componentRootSpan (fixSubfield σ) (rootCharHom a) i).subtype)
  have hθ' : ∀ x : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i), θ' x = z * ι x.1 * z⁻¹ :=
    fun x => rfl
  let θ₀ : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* P.S 0 :=
    θ'.codRestrict (P.S 0) fun x => by
      rw [hP0, hθ']
      exact (hnorm i _).1 (hιS x.1 x.2)
  have hfix : ∀ x, iterHom S.D.step 1 ((θ₀ x : P.S 0) : ModGL τ L) = θ₀ x := fun x => by
    change iterHom S.D.step 1 (θ' x) = θ' x
    rw [hθ', hz _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)]
  have hmem : ∀ x : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i),
      θ' x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := fun x => by
    have h := outer_norm_mem_rationalComponent S hT i hs hmin hperfC θ₀ hfix x
    rwa [excres_norm_one] at h
  have heSL : ∀ g, ((eSL g : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) :
      ModGL τ (fixSubfield σ)) = CFSG.LieType.Chevalley.rootSL2 τ (fixSubfield σ) β g := fun g => by
    simp only [eSL, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    exact MonoidHom.ofInjective_apply _
  have hθeq : ∀ g, excresTheta τ (fixSubfield σ) β z g = θ' (eSL g) := fun g => by
    rw [excresTheta_apply, hθ', heSL]
  have hle : (excresTheta τ (fixSubfield σ) β z).range ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rintro _ ⟨g, rfl⟩
    rw [hθeq]
    exact hmem _
  haveI : Finite (SL2 (fixSubfield σ)) := inferInstance
  haveI : Finite ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    Finite.of_equiv _ eSL.toEquiv
  haveI : Finite ↥f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hcard : Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤
      Nat.card (excresTheta τ (fixSubfield σ) β z).range := by
    calc Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i) = Nat.card f.range := by
          rw [hRf]
      _ ≤ Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd f)
      _ = Nat.card (SL2 (fixSubfield σ)) := Nat.card_congr eSL.toEquiv.symm
      _ = Nat.card (excresTheta τ (fixSubfield σ) β z).range :=
          (Nat.card_range_of_injective (excresTheta_injective τ (fixSubfield σ) β z)).symm
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    rw [← hRf]
    infer_instance
  exact ⟨fixSubfield σ, hfinK, β, z, hβ, by rw [hKcard]; exact hQ4,
    Subgroup.eq_of_le_of_card_ge hle hcard⟩

end Explicit

end CFSG.HardMathSupport.Dickson.Sec6.I1431
