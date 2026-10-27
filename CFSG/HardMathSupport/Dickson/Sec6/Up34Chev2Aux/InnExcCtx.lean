module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace Up34Exc

section Untwist

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem exists_untwistT_Z (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 0 < s)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  obtain ⟨w, hw, hwγ⟩ := hinner
  have hφpin : ∀ γ ∈ componentRoots (rootCharHom a) i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, iterHom S.D.step s (pinnedX τ L γ c) = pinnedX τ L (w • γ) (m * σ c) := by
    intro γ hγ
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hγ)
    exact ⟨μ, hμ0, fun c => by rw [iterHom_eq_iterate, hμ, hwγ γ hγ, hσc]⟩
  obtain ⟨y₁, hy₁, hpin⟩ := exists_pin i σ (iterHom S.D.step s) hw hφpin
  obtain ⟨z, hzZ, hφz⟩ := exists_lang_torus_sup_kernelRoots S hs
    (fun γ hγ => outer_iterate_mem_kernelRoots S hT s hγ)
    ((sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hy₁)
  refine ⟨σ, z, hσc, hzZ, mem_componentRootSpan_iff_conj_of_mem hzZ, fun g hg => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz]
  calc z * y₁ * iterHom S.D.step s g * (z * y₁)⁻¹ =
      z * (y₁ * iterHom S.D.step s g * y₁⁻¹) * z⁻¹ := by group
    _ = z * frobGL σ g * z⁻¹ := by rw [hpin g hg]

theorem rootDiagUnit_mul_comm_of_mem_Z (a : Fin τ.rank → Lˣ) {z : ModGL τ L}
    (hz : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    rootDiagUnit τ a * z = z * rootDiagUnit τ a := by
  have hle : torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ≤
      Subgroup.centralizer {rootDiagUnit τ a} := by
    refine sup_le (fun h hh => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2 (rootDiagUnit_mul_comm_of_mem_torusGroup a hh).symm
    · refine iSup₂_le fun γ hγ => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 := rootDiagUnit_conj_pinnedX (K := L) (a := a) hγ.1 c
      have h2 : (rootChar a γ : L) = 1 := by
        have := hγ.2
        change rootChar a γ = 1 at this
        rw [this]
        rfl
      rw [h2, one_mul] at h1
      symm
      calc rootDiagUnit τ a * pinnedX τ L γ c
          = (rootDiagUnit τ a * pinnedX τ L γ c * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by
            group
        _ = pinnedX τ L γ c * rootDiagUnit τ a := by rw [h1]
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

end Untwist

section Norm

theorem iterHom_eq_self_of_fixed {G : Type*} [Group G] {F : G →* G} {y : G} (hy : F y = y)
    (n : ℕ) : iterHom F n y = y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterHom_succ, ih, hy]

theorem norm_eq_pow_of_fixed {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (y : P.S 0) (hy : F (y : G) = y) : P.norm y = (y : G) ^ s := by
  classical
  unfold CycFamily.norm CycFamily.mu
  rw [MonoidHom.comp_apply, Subgroup.noncommPiCoprod_apply]
  refine (Finset.noncommProd_eq_pow_card _ _ _ (y : G) ?_).trans ?_
  · intro k _
    simp [CycFamily.coe_diag_apply, iterHom_eq_self_of_fixed hy]
  · simp [ZMod.card]

end Norm

section PowMem

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem pow_mem_rationalComponent_of_fixed (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i))
    (c : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i))
    (hF : S.D.step (z * baseChangeGL (fixSubfield σ).subtype c.1 * z⁻¹) =
      z * baseChangeGL (fixSubfield σ).subtype c.1 * z⁻¹) :
    (z * baseChangeGL (fixSubfield σ).subtype c.1 * z⁻¹) ^ s ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hιC : ∀ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hx, rfl⟩
  have hιS : ∀ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      ι x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    fun x hx => CQ_le_rootSpan σ i (hιC x hx)
  let θ : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL τ L :=
    (MulAut.conj z).toMonoidHom.comp (ι.comp (componentRootSpan (fixSubfield σ)
      (rootCharHom a) i).subtype)
  have hθ : ∀ x, θ x = z * ι x.1 * z⁻¹ := fun x => rfl
  let θ₀ : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* P.S 0 :=
    θ.codRestrict (P.S 0) fun x => by
      rw [hP0, hθ]
      exact (hnorm i _).1 (hιS x.1 x.2)
  have hθ₀ : ∀ x, ((θ₀ x : P.S 0) : ModGL τ L) = z * ι x.1 * z⁻¹ := fun x => rfl
  have hfix : ∀ x, iterHom S.D.step s ((θ₀ x : P.S 0) : ModGL τ L) = θ₀ x := fun x => by
    rw [hθ₀, hz _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)]
  have hmem := outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix c
  have hF1 : S.D.step ((θ₀ c : P.S 0) : ModGL τ L) = (θ₀ c : ModGL τ L) := by
    rw [hθ₀]
    exact hF
  rw [norm_eq_pow_of_fixed P (θ₀ c) hF1] at hmem
  exact hmem

end PowMem

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
