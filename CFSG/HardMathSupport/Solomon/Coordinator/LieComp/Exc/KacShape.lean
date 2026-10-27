module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


variable {τ : Tag}

theorem exists_cand_of_class (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ} (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ) (x : Option (Fin τ.rank)) (c : List ℕ),
      K.IsNormal p μ ∧ c ∈ cands ∧ K.comp p μ x = {y | nodeIdx y ∈ c} ∧ c.length ≤ τ.rank ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' K.rootsOf (((c.map (idxNode (r := τ.rank))).toFinset :
          Finset (Option (Fin τ.rank))) : Set (Option (Fin τ.rank))) ∧
      compRank (componentRoots (rootCharHom a) i) = c.length ∧
      (componentRoots (rootCharHom a) i).ncard =
        kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset := by
  classical
  obtain ⟨v, μ, hμ, hall⟩ := S.exists_kacT_of_prime hp hpL hK hTp
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := K.exists_comp_eq_of_check hT hadj (adm := fun _ => true) hcheck rfl hx
  set C : Finset (Option (Fin τ.rank)) := (c.map (idxNode (r := τ.rank))).toFinset with hCdef
  have hCset : K.comp p μ x = (C : Set (Option (Fin τ.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (hlt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp K hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' K.rootsOf (C : Set (Option (Fin τ.rank))) := by
    rw [hi, hCset]
  refine ⟨v, μ, x, c, hμ, hc, hcomp, ?_, hi', ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hCp
    have h1 : C.card < Fintype.card (Option (Fin τ.rank)) := Finset.card_lt_univ_of_notMem hy
    rw [Fintype.card_option, Fintype.card_fin, hcard c hc] at h1
    omega
  · rw [hi', compRank_image, compRank_rootsOf K hK hCp, hcard c hc]
  · rw [hi', ncard_image_smul, ncard_rootsOf K hK hCp]

theorem rootsOf_eq_parabolicRoots (K : KacData τ) (hK : K.Facts)
    {C : Finset (Option (Fin τ.rank))} {J : Set (Fin τ.rank)} (hnone : none ∉ C)
    (hCJ : ∀ j, some j ∈ C ↔ j ∈ J) :
    K.rootsOf (C : Set (Option (Fin τ.rank))) = parabolicRoots τ J := by
  ext γ
  rw [mem_rootsOf_iff K hK ⟨none, hnone⟩]
  constructor
  · rintro ⟨hγ, htest⟩
    refine ⟨hγ, fun i hi => ?_⟩
    rcases htest with h | ⟨h, -⟩
    · exact h i (fun hc => hi ((hCJ i).1 hc))
    · exact absurd h hnone
  · rintro ⟨hγ, hJ⟩
    exact ⟨hγ, Or.inl fun j hj => hJ j (fun hj' => hj ((hCJ j).2 hj'))⟩

theorem InnerRecog.of_mulEquiv {p : ℕ} {C D : Type} [Group C] [Group D] (h : InnerRecog p C)
    (e : C ≃* D) : InnerRecog p D := by
  obtain ⟨Y, hY, hfd, hA6, g, hg, hk⟩ := h
  refine ⟨Y, hY, hfd, hA6, e.toMonoidHom.comp g, e.surjective.comp hg, fun y hy => ?_⟩
  rw [MonoidHom.mem_ker] at hy
  exact hk (by
    rw [MonoidHom.mem_ker]
    exact e.injective (by simpa using hy))

theorem innerRecog_rootSpan_smul {K : Type} [Field K] (v : WeylGroup τ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {p : ℕ}
    (h : InnerRecog p ↥(rootSpan τ K S)) :
    InnerRecog p ↥(rootSpan τ K ((fun α => v • α) '' S)) := by
  have hmap := (canonical_weyl_root_transport τ K).1 v S hS
  refine h.of_mulEquiv ?_
  exact ((rootSpan τ K S).equivMapOfInjective (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).injective).trans
    (MulEquiv.subgroupCongr hmap)


section Card

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.RootAut

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem rationalLieType_of_innerRecog_card (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      InnerRecog (ringChar L) ↥(componentRootSpan K (rootCharHom ta) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  obtain ⟨X, _, hX, hA6, g, hg, hgk⟩ := hrec (fixSubfield σ) hfin hcard
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

end Card

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
