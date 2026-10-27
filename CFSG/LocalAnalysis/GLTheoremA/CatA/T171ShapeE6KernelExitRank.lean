module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

@[expose] def RankLieType (P : StatedLieTag → ℕ → Prop) (ℓ : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (r e : ℕ), P t r ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r ℓ e

theorem RankLieType.mono {P Q : StatedLieTag → ℕ → Prop} {ℓ : ℕ} {X : Type} [Group X]
    (h : RankLieType P ℓ X) (hPQ : ∀ t r, P t r → Q t r) : RankLieType Q ℓ X := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  exact ⟨t, r, e, hPQ t r ht, hm⟩

theorem RankLieType.of_tagLie {P : StatedLieTag → Prop} {Q : StatedLieTag → ℕ → Prop} {ℓ : ℕ}
    {X : Type} [Group X] (h : TagLieType P ℓ X) (hPQ : ∀ t r, P t → Q t r) :
    RankLieType Q ℓ X := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  exact ⟨t, r, e, hPQ t r ht, hm⟩

theorem RankLieType.of_surjective {P : StatedLieTag → ℕ → Prop} {ℓ : ℕ} {X Y : Type} [Group X]
    [Group Y] (h : RankLieType P ℓ X) (hX : commutator X = ⊤) (f : X →* Y)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center X) : RankLieType P ℓ Y := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  obtain ⟨g⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hX f hf hk
  exact ⟨t, r, e, ht, CFSG.Blueprint.LieModel.of_mulEquiv g hm⟩

section TypedClasses

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups


theorem rankLie_innerRecog_D {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      RankLieType (fun t r => t = .POmegaPlus ∧ r = n) p
        ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.POmegaPlus, n, f, ⟨rfl, rfl⟩, hmodel⟩⟩

variable {τ : Tag}

theorem rankLie_of_innerCover {P : StatedLieTag → ℕ → Prop} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      commutator ↥(componentRootSpan K (rootCharHom ta) i) = ⊤ ∧
        RankLieType P (ringChar L) ↥(componentRootSpan K (rootCharHom ta) i)) :
    RankLieType P (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  obtain ⟨hperf, hT'⟩ := hrec (fixSubfield σ) hfin hcard
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom ta) i,
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hperf)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  have hmem : ∀ x, f x ∈ rationalComponent S.ρ S.Γ (rootCharHom ta) i := fun x =>
    hRf ▸ ⟨x, rfl⟩
  let g := f.codRestrict _ hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ f.range := hRf ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hgk : g.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  exact hT'.of_surjective hperf g hg hgk

theorem rankLie_of_tree {P : StatedLieTag → ℕ → Prop} (K : KacData τ) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hTor : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      commutator ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l))) = ⊤ ∧
        RankLieType P p
          ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l)))) :
    RankLieType P (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  refine rankLie_of_innerCover S hTor i hinner (fun K' hK' _ => ?_)
  set β : Option (Fin τ.rank) → Fin τ.rank → ℤ := fun x => v • K.extRoot x with hβ
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ, v • K.combo n' = ∑ x, (n' x : ℤ) • β x := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
  have hset : (fun α => v • α) '' K.rootsOf (Set.range l) = rootsOfFam β (Set.range l) := by
    ext γ
    constructor
    · rintro ⟨γ₀, ⟨hr0, n', hn', hγ⟩, rfl⟩
      refine ⟨IsRoot.smul hr0 v, n', hn', ?_⟩
      rcases hγ with rfl | rfl
      · exact Or.inl (hsmulcombo n')
      · exact Or.inr (by show v • (-K.combo n') = _; rw [smul_neg, hsmulcombo])
    · rintro ⟨hr, n', hn', hγ⟩
      refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hr v⁻¹, n', hn', ?_⟩, smul_inv_smul v γ⟩
      rcases hγ with rfl | rfl
      · left
        rw [← hsmulcombo, inv_smul_smul]
      · right
        rw [smul_neg, ← hsmulcombo, inv_smul_smul]
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan τ K' (rootsOfFam β (Set.range l)) := by
    show rootSpan τ K' (componentRoots (rootCharHom a) i) = _
    rw [hroots, hset]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardK⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardK
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  exact hrec ↥K' (ringChar L) f hprime f.pos hK'card

theorem rankLie_of_dClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RankLieType (fun t r => t = .POmegaPlus ∧ r = compRank (componentRoots (rootCharHom a) i))
      (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE, hnr⟩ :=
    CompsPTwoDMain.exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4
      (fun n => 2 * n * (n - 1)) hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i
      h4 hn
  refine rankLie_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  refine (rankLie_innerRecog_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)).imp id fun h => h.mono fun t r ht => ⟨ht.1, ?_⟩
  rw [ht.2, hnr]

end TypedClasses

section Classes

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups


theorem rankLie_rationalComponent_E6_of_not_d4 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hnot : ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24)) :
    RankLieType (fun t r => t = .PSL ∨ t = .PSU ∨ (t = .POmegaPlus ∧ r ≠ 4) ∨ t = .POmegaMinus)
      (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · refine RankLieType.of_tagLie (tagLie_rationalComponent_typeA S hp hT hap h1 i hA hq) ?_
    intro t _ ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA' | hD' | hE'
  · exact (hA hA').elim
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · refine (rankLie_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check
        e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hT hTp i
        hD'.1 hD'.2 hinner).mono fun t r ht => Or.inr (Or.inr (Or.inl ⟨ht.1, ?_⟩))
      rw [ht.2]
      intro h4
      exact hnot ⟨h4, by rw [hD'.2, h4]⟩
    · by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
      · exact RankLieType.of_tagLie
          (tagLie_rationalComponent_outerD_high S hp hT hap h1 i h5 hD'.2 hinner)
          fun t _ ht => Or.inr (Or.inr (Or.inr ht))
      · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        exact (hnot ⟨hr4, by rw [hD'.2, hr4]⟩).elim
  · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim

end Classes

end CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

end
