module

public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogD

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSExact

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
  CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped MatrixGroups


theorem exists_D_of_statedClassicalModel_POmegaPlus {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n p f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.D n q).Valid), q.p = p ∧ q.exponent = f ∧
      Nonempty (G ≃* (CFSGIndex.lie ⟨.D n q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField
    ⟨.D n q, hv⟩ K (by simp [ValidLieTypeIndex.fieldOrder, q, hK])
  let eT := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv
  let e1 : StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus n ↥(ValidLieTypeIndex.fixedField ⟨.D n q, hv⟩))) :=
    statedProjCongr (glCongr (ι := Fin n ⊕ Fin n) φ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp (n := n) φ))
      (glCongr_statedScalars φ)
  exact ⟨q, hv, rfl, rfl, ⟨(θ.trans e1).trans eT.symm⟩⟩

theorem isLieQuot_of_D_model {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel (G ⧸ Subgroup.center G) .POmegaPlus n p f)
    (P : LieTypeIndex → Prop) (hP : ∀ q : PrimePower, q.p = p → q.exponent = f → P (.D n q)) :
    IsLieQuot G P := by
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ := exists_D_of_statedClassicalModel_POmegaPlus h
  exact ⟨⟨.D n q, hv⟩, hP q hqp hqf, ⟨e⟩⟩

section Recog

open CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint CFSG.Timmesfeld


theorem innerModel_D {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    CFSG.IsQuasisimple ↥(rootSpan τ K (rootsOfFam β (Set.range l))) ∧
      StatedClassicalModel (↥(rootSpan τ K (rootsOfFam β (Set.range l))) ⧸
        Subgroup.center ↥(rootSpan τ K (rootsOfFam β (Set.range l)))) .POmegaPlus n p f := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  refine ⟨hqs, ?_⟩
  rcases hmodel with ⟨-, hmod⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩
  · exact hmod
  all_goals simp [chevalleyExceptionalTags, reeTitsTags] at ht

end Recog

section Rat


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {ta : Fin τ.rank → Lˣ}

theorem rationalComponent_dModel (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    {n : ℕ} (hn : 4 ≤ n) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hroots : componentRoots (rootCharHom ta) i = rootsOfFam β (Set.range l))
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ {F : Type} [Field F] (i j : Fin n), edgeD n i j → ∃ θ : SL(3, F) →* ModGL τ F,
      θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l i)) ∧
        θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l j)))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e) :
    StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i))
      .POmegaPlus n r (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  haveI : Finite ↥(fixSubfield σ) := hfin
  have hcard' : Nat.card ↥(fixSubfield σ) = r ^ (e * s) := by rw [hcard, hq, ← pow_mul]
  have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom ta) i =
      rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l)) := by
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom ta) i) = _
    rw [hroots]
  obtain ⟨hqs, hmod⟩ := innerModel_D hτ hn hr hes hcard' β hroot l hgram
    (hframe (F := ↥(fixSubfield σ)))
  rw [← hcomp] at hqs hmod
  have hCperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := hqs.1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hCperf)) hf1
  let g : ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := by
    intro c hc
    apply hker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hCperf.commutator_eq_top g hgsurj hgker
  obtain ⟨hadm, K'', hfield, hfinite, hK'', ⟨θ⟩⟩ := hmod
  exact ⟨hadm, K'', hfield, hfinite, hK'', ⟨e1.symm.trans θ⟩⟩

end Rat

end KSExact

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
