module

import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw

@[expose] def TagLieType (P : StatedLieTag → Prop) (ℓ : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (r e : ℕ), P t ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r ℓ e

@[expose] def IsADETag (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨
    t = .twistedE6

@[expose] def IsInnerDETag (t : StatedLieTag) : Prop :=
  t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8

theorem isADETag_of_typeA {t : StatedLieTag} (h : t = .PSL ∨ t = .PSU) : IsADETag t := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem isADETag_of_innerDE {t : StatedLieTag} (h : IsInnerDETag t) : IsADETag t := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

theorem isADETag_POmegaMinus : IsADETag .POmegaMinus := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem isADETag_twistedE6 : IsADETag .twistedE6 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem TagLieType.mono {P Q : StatedLieTag → Prop} {ℓ : ℕ} {X : Type} [Group X]
    (h : TagLieType P ℓ X) (hPQ : ∀ t, P t → Q t) : TagLieType Q ℓ X := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  exact ⟨t, r, e, hPQ t ht, hm⟩

theorem TagLieType.of_mulEquiv {P : StatedLieTag → Prop} {ℓ : ℕ} {X Y : Type} [Group X]
    [Group Y] (h : TagLieType P ℓ X) (e : X ≃* Y) : TagLieType P ℓ Y := by
  obtain ⟨t, r, f, ht, hm⟩ := h
  exact ⟨t, r, f, ht, CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)) hm⟩

theorem TagLieType.of_surjective {P : StatedLieTag → Prop} {ℓ : ℕ} {X Y : Type} [Group X]
    [Group Y] (h : TagLieType P ℓ X) (hX : commutator X = ⊤) (f : X →* Y)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center X) : TagLieType P ℓ Y := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  obtain ⟨g⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hX f hf hk
  exact ⟨t, r, e, ht, CFSG.Blueprint.LieModel.of_mulEquiv g hm⟩

theorem TagLieType.map_conj {P : StatedLieTag → Prop} {G : Type} [Group G] {ℓ : ℕ}
    {R : Subgroup G} (φ : G ≃* G) (h : TagLieType P ℓ ↥R) :
    TagLieType P ℓ ↥(R.map φ.toMonoidHom) :=
  h.of_mulEquiv (R.equivMapOfInjective φ.toMonoidHom φ.injective)

section TypedClasses

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open scoped MatrixGroups

section TypeA


theorem tagLie_rationalComponent_typeA {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    TagLieType (fun t => t = .PSL ∨ t = .PSU) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨ν, f, -, -, -, hmodel⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model S hp hT hap h1 i hA
      hqs
  rcases hmodel with hM | hM
  · exact ⟨.PSL, ν, f, Or.inl rfl, Or.inl ⟨by decide, hM⟩⟩
  · exact ⟨.PSU, ν, f, Or.inr rfl, Or.inl ⟨by decide, hM⟩⟩

end TypeA

section DE

open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped Matrix


theorem tagLie_innerRecog_D {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      TagLieType (· = .POmegaPlus) p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.POmegaPlus, n, f, rfl, hmodel⟩⟩

theorem tagLie_innerRecog_E6 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      TagLieType (· = .E6) p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E6, 0, f, rfl, hmodel⟩⟩

theorem tagLie_innerRecog_E7 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      TagLieType (· = .E7) p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E7, 0, f, rfl, hmodel⟩⟩

theorem tagLie_innerRecog_E8 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 8, edgeE 8 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      TagLieType (· = .E8) p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e8_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E8, 0, f, rfl, hmodel⟩⟩

variable {τ : Tag}

theorem tagLie_of_innerCover {P : StatedLieTag → Prop} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      commutator ↥(componentRootSpan K (rootCharHom ta) i) = ⊤ ∧
        TagLieType P (ringChar L) ↥(componentRootSpan K (rootCharHom ta) i)) :
    TagLieType P (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
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

theorem tagLie_of_tree {P : StatedLieTag → Prop} (K : KacData τ) {L : Type} [Field L]
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
        TagLieType P p
          ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l)))) :
    TagLieType P (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  refine tagLie_of_innerCover S hTor i hinner (fun K' hK' _ => ?_)
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

theorem tagLie_of_dClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    TagLieType (· = .POmegaPlus) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  refine tagLie_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact tagLie_innerRecog_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

theorem tagLie_of_eClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    (hcount : ∀ c ∈ cands, 6 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = eRootCount c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hlen : ∀ P ∈ trees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType (fun t => t = .E6 ∨ t = .E7 ∨ t = .E8) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  refine tagLie_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  have hgr : ∀ c d : Fin n, c ≠ d → ¬ edgeE n c d → ¬ edgeE n d c →
      iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
    intro c d hcd h1 h2
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  have hfr := treeFrames K hframes v l (edgeE n) hE (F := K')
  have hroot : ∀ b, IsRoot τ ((fun x => v • K.extRoot x) b) :=
    fun b => IsRoot.smul (K.isRoot_extRoot b) v
  rcases hQ with rfl | rfl | rfl
  · exact (tagLie_innerRecog_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr
      hfr).imp id fun h => h.mono fun _ ht => Or.inl ht
  · exact (tagLie_innerRecog_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr
      hfr).imp id fun h => h.mono fun _ ht => Or.inr (Or.inl ht)
  · exact (tagLie_innerRecog_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr
      hfr).imp id fun h => h.mono fun _ ht => Or.inr (Or.inr ht)

theorem tagLie_inner_nonA_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType IsInnerDETag (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact (tagLie_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i hD.1
      hD.2 hinner).mono fun _ ht => Or.inl ht
  · exact (tagLie_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp
      i hE.1 hE.2 hinner).mono fun _ ht => Or.inr ht

theorem tagLie_inner_nonA_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType IsInnerDETag (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact (tagLie_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner).mono fun _ ht => Or.inl ht
  · exact (tagLie_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner).mono fun _ ht => Or.inr ht

theorem tagLie_inner_nonA_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType IsInnerDETag (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact (tagLie_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner).mono fun _ ht => Or.inl ht
  · exact (tagLie_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner).mono fun _ ht => Or.inr ht

end DE

end TypedClasses

section D4Cubic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp


theorem tagLie_graphFixedRootGroup_cubic {ℓ f' : ℕ} (hℓ : ℓ.Prime) (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f') ^ r)) :
    TagLieType (· = .trialityD4) ℓ ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ (ℓ ^ f')) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ (ℓ ^ f') := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (ℓ ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          K σ σ.symm (fun c => σ.apply_symm_apply c)⟩
  have hK' : Nat.card K = (ℓ ^ f') ^ TwistTag.D4.order := hK
  obtain ⟨ψ⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.D4 hℓ hf' K
    hK' σ₁.toRingHom (fun c => hσ₁ c)
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  let e0 : (↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hadm : CFSG.Open.StatedLieAdmissible .trialityD4 0 ℓ f' := ⟨hℓ, hf', rfl⟩
  refine ⟨.trialityD4, 0, f', rfl, Or.inr (Or.inl ⟨rfl, by decide, hadm, ?_⟩)⟩
  exact ⟨K, inferInstance, inferInstance, hK', σ₁.toRingHom, fun c => hσ₁ c,
    ⟨(e0.trans e).trans ψ.symm⟩⟩

end D4Cubic

section D4LayerDefs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def D4TrialityLayerTag (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ a b c : Fin τ.rank, a ≠ b → b ≠ c → a ≠ c → a.val ∈ ({1, 2, 4} : Set ℕ) →
    b.val ∈ ({1, 2, 4} : Set ℕ) → c.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      TagLieType (· = .trialityD4) ℓ ↥P

@[expose] def D4SwapLayerTag (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      TagLieType (· = .POmegaMinus) ℓ ↥P

end D4LayerDefs

section D4Tau

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

include hf in
theorem tagLie_tauDatum :
    TagLieType (· = .POmegaMinus) ℓ ↥(tauDatum L ℓ f hf).orbitGroup := by
  classical
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  refine ⟨.POmegaMinus, 4, _, rfl, lieModel_orbitGroup_of_datum_four (τ := Tag.E6)
    (Or.inr (Or.inl rfl)) (tauDatum L ℓ f hf) (m := 4) le_rfl
    (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau bTau_root bTau_injective iform_bTau
    ?_ ?_ ?_ ?_ ?_⟩
  ·
    ext β
    constructor
    · intro hβ
      rw [GenFixedRootDatum.simpleRootsJ_eq] at hβ
      obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
      have hjS : j ∈ d4Support := d4Aux_support ▸ hj
      rcases d4Support_cases hjS with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact single_mem_simpleRootsJ hf h1S
      · exact single_mem_simpleRootsJ hf h3S
      · exact single_mem_simpleRootsJ hf h2S
      · exact single_mem_simpleRootsJ hf h4S
  ·
    intro j hj
    fin_cases j
    · exact (theta_single_tau hf h1S).trans (by rw [gam_one]; rfl)
    · exact (theta_single_tau hf h3S).trans (by rw [gam_three]; rfl)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · exact (theta_single_tau hf h2S).trans (by rw [gam_two]; rfl)
  · exact (theta_single_tau hf h4S).trans (by rw [gam_four]; rfl)
  ·
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hjk; decide)
      | exact exists_frame_E6 (by decide)

include hf in
theorem tagLie_fixE6_dN :
    TagLieType (· = .POmegaMinus) ℓ ↥(fixE6 ℓ f (dN L)) := by
  rw [fixE6_dN hf]
  exact tagLie_tauDatum hf

include hf in
theorem exists_fix_swap13_tag :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      TagLieType (· = .POmegaMinus) ℓ ↥(fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, tagLie_fixE6_dN hf⟩

include hf in
theorem exists_fix_swap03_tag :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      TagLieType (· = .POmegaMinus) ℓ ↥(fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact TagLieType.map_conj _ (tagLie_fixE6_dN hf)

include hf in
theorem exists_fix_swap01_tag :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      TagLieType (· = .POmegaMinus) ℓ ↥(fixE6 ℓ f n₂) := by
  have hR := map_conj_mul (L := L) map_conj_d4TrialityRep map_conj_d4TrialityRep
  have hF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
      (d4TrialityRep L * d4TrialityRep L) = d4TrialityRep L * d4TrialityRep L := by
    rw [map_mul, frob_d4TrialityRep]
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L * (d4TrialityRep L * d4TrialityRep L)⁻¹,
    ?_, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · exact E6Fix.conj hR hF (E6Fix_dN hf)
  · rw [fixE6_conj hR hF]
    exact TagLieType.map_conj _ (tagLie_fixE6_dN hf)

end D4Tau

section D4Std

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [hτ : E6Sub τ]
variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem tagLie_layer_swap {tagP : StatedLieTag → Prop} {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L}
    (hstd : StdSwap n₁ π σ) (h₂ : Acts n₂ σ) (hRL : TagLieType tagP ℓ ↥(fixE6 ℓ f n₂))
    {n h : ModGL τ L} (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    TagLieType tagP ℓ ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact hRL.of_mulEquiv (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm

theorem tagLie_layer_triality {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}
    (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    TagLieType (· = .trialityD4) ℓ ↥P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  exact (tagLie_graphFixedRootGroup_cubic (Fact.out : ℓ.Prime) hf K hKc σ hstd.he
    hσ).of_mulEquiv eP.symm

theorem trialityLayerTag_generic (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    TagLieType (· = .trialityD4) ℓ ↥P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact tagLie_layer_triality hf hstd hh hlang hP

theorem swapLayerTag_generic {tagP : StatedLieTag → Prop} (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      TagLieType tagP ℓ ↥(fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    TagLieType tagP ℓ ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact tagLie_layer_swap hstd h₂ hRL hh hlang hP

end D4Std

section D4OfLeaf

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [E6Sub τ]

theorem d4TrialityLayerTag_of_leafCycle
    (hleaf : ∀ a b c : Fin τ.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
      b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
      a ≠ b → b ≠ c → a ≠ c →
      ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
        (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧
          ((List.formPerm [a, b, c]).symm i).val ≤ 4))) :
    D4TrialityLayerTag τ := by
  intro L _ _ ℓ f _ _ hf a b c hab hbc hac ha hb hc n hn _ hact P hP
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := hleaf a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · exact trialityLayerTag_generic hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
  · exact trialityLayerTag_generic hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP

theorem d4SwapLayerTag_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))) :
    D4SwapLayerTag τ := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact swapLayerTag_generic hf (Equiv.swap 1 3) (exists_fix_swap13_tag hf)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerTag_generic hf (Equiv.swap 0 3) (exists_fix_swap03_tag hf)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerTag_generic hf (Equiv.swap 0 1) (exists_fix_swap01_tag hf)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

end D4OfLeaf

section D4Tags

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers


theorem d4SwapLayerTag_E6 : D4SwapLayerTag .E6 := d4SwapLayerTag_of_leafSwap leafSwap_E6

theorem d4TrialityLayerTag_E6 : D4TrialityLayerTag .E6 :=
  d4TrialityLayerTag_of_leafCycle leafCycle_E6

end D4Tags

section D4Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
  {p : ℕ}

theorem rootSpan_inf_model_tag_d4_of_layer {tagP : StatedLieTag → Prop} (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      TagLieType tagP ℓ ↥(rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    TagLieType tagP (ringChar L)
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (d4Nodes τ), IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ, hFr']
      exact hxF
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots, hring]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hP := hlayer ℓ f hf hq (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact TagLieType.map_conj (MulAut.conj nv) hP

variable {Fr : L →+* L}

theorem rootSpan_inf_model_tag_d4_swap
    (hL : D4SwapLayerTag τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α) :
    TagLieType (· = .POmegaMinus) (ringChar L)
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_tag_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact

theorem rootSpan_inf_model_tag_d4 (hL : D4TrialityLayerTag τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {a b c : Fin τ.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    TagLieType (· = .trialityD4) (ringChar L)
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_tag_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC hex _ rfl)
    hact

end D4Transport

section D4Component

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable
  {τ : Tag} {L : Type} [Field L]
  [IsAlgClosed L] {p : ℕ}

theorem tagLie_rationalComponent_of_d4_outer {tagP : StatedLieTag → Prop} [E6Sub τ]
    (hsearch : D4BaseSearch τ) (hL2 : D4SwapLayer τ) (hR2 : D4SwapLayerTag τ)
    (hP2 : tagP .POmegaMinus) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (htri : ∀ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ π : Equiv.Perm (Fin τ.rank),
      (π = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
        π = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2]) →
      (∀ α ∈ parabolicRoots τ (d4Nodes τ), (v⁻¹ * w * v) • α = u • permLattice π α) →
      CFSG.IsQuasisimple
          ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) ∧
        TagLieType tagP (ringChar L)
          ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model)) :
    TagLieType tagP (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
      TagLieType tagP (ringChar L) ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        (rootSpan_inf_model_tag_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact).mono
          fun _ ht => ht ▸ hP2⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        (rootSpan_inf_model_tag_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact).mono
          fun _ ht => ht ▸ hP2⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        (rootSpan_inf_model_tag_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact).mono
          fun _ ht => ht ▸ hP2⟩
    · exact htri u hu _ (Or.inl rfl) hact
    · exact htri u hu _ (Or.inr rfl) hact
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

theorem d4_outer_htri_of_layer {tagP : StatedLieTag → Prop} [E6Sub τ] (hL3 : D4TrialityLayer τ)
    (hR3 : D4TrialityLayerTag τ) (hP3 : tagP .trialityD4) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ) :
    ∀ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ π : Equiv.Perm (Fin τ.rank),
      (π = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
        π = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2]) →
      (∀ α ∈ parabolicRoots τ (d4Nodes τ), (v⁻¹ * w * v) • α = u • permLattice π α) →
      CFSG.IsQuasisimple
          ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) ∧
        TagLieType tagP (ringChar L)
          ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  intro u hu π hπ hact
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  rcases hπ with rfl | rfl
  · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
      hact).2, (rootSpan_inf_model_tag_d4 hR3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).mono fun _ ht => ht ▸ hP3⟩
  · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
      hact).2, (rootSpan_inf_model_tag_d4 hR3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).mono fun _ ht => ht ▸ hP3⟩

end D4Component

section D4TwLayers

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem twisted_swap_layer_tag (hf : 1 ≤ f)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    TagLieType (· = .POmegaMinus) ℓ
      ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' : ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun k hk => by
    have := hact _ (single_mem_parabolicRoots hk)
    rw [permLattice_single (Equiv.swap i j)] at this
    exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap13_tag (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    exact tagLie_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap03_tag (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    exact tagLie_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap01_tag (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    exact tagLie_layer_swap hstd h₂ hRL hh hlang rfl

theorem twisted_triality_layer_tag (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    TagLieType (· = .trialityD4) ℓ
      ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact tagLie_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact tagLie_layer_triality hf hstd hh hlang rfl

end D4TwLayers

section D4TwComponent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers


theorem tagLie_rationalComponent_of_d4_twE6_of_layer {tagP : StatedLieTag → Prop} {L : Type}
    [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hlay : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L) (u : WeylGroup Tag.E6),
      u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) → ∀ π : Equiv.Perm (Fin Tag.E6.rank),
      IsD4LeafPerm π → π ≠ 1 →
      (¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → π * π ≠ 1) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      TagLieType tagP ℓ ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    TagLieType tagP (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → πJ * πJ ≠ 1 := by
    intro hnin2 h2
    apply hnin2
    have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
        exact (e6WeylTwist_simple j).symm
      exact hle ⟨u, hu, rfl⟩
    have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
        change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨e6WeylTwist u, hδu, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
    refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), permLattice πJ (u • x) =
        (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
      intro x hx
      rw [← hlin _ (huJ x hx), ← hlin x hx, ← e6WeylTwist_smul u x, mul_smul, mul_smul,
        inv_smul_smul]
    set β := u • permLattice πJ α with hβ
    have hβJ : β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
      rw [hβ, ← hθ' α hα]
      exact hθmem α hα
    have e1 : S.ρ (v • α) = v • β := by
      rw [hβ, ← hθ' α hα, smul_inv_smul]
    have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
      rw [← hθ' β hβJ, smul_inv_smul]
    have e3 : permLattice πJ (permLattice πJ α) = α := by
      rw [← permLattice_mul, h2]
      rfl
    calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
      _ = v • (u • permLattice πJ β) := by rw [e1, e2]
      _ = v • (u₂ • α) := by
          rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
      _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = w' := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hlayer := hlay ℓ f hf hq _ hn'M u hu πJ hπJleaf hπ1 hπ2 hact
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ', hFr'] at hxF'
      change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x
      calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
            group
        _ = x := hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = x := hxF
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ', hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  have hqs : CFSG.IsQuasisimple
        ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      TagLieType tagP ℓ ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
    set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    have e : Q ≃* Q.map (MulAut.conj nv).toMonoidHom :=
      Q.equivMapOfInjective _ (MulAut.conj nv).injective
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1,
      TagLieType.map_conj (MulAut.conj nv) hlayer.2⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs.1, ringChar.eq L ℓ]
  exact hqs.2

end D4TwComponent

section E6Triality

open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootChar_add
  rootChar_nsmul_single)

open CFSG.LieType.AlgebraicGroups (rootCharHom)

open CFSG.RankThree.PartOne.KE (d4Nodes)

open CFSG.RankThree.PartOne.KD4T (e6Idx)


@[expose] def e6TriSearchA : Bool :=
  Tag.E6.artifactRoots.all fun a₀ =>
    !(lform a₀ [0, 0, 1, 0, 0, 0] == 0 && lform a₀ [0, 0, 0, 0, 1, 0] == -1 &&
      lform a₀ [0, 0, 0, 1, 0, 0] == 0 && lform a₀ [0, 1, 0, 0, 0, 0] == 0) ||
    Tag.E6.artifactRoots.all fun a₅ =>
      !(lform a₅ [0, 0, 1, 0, 0, 0] == 0 && lform a₅ [0, 0, 0, 0, 1, 0] == 0 &&
        lform a₅ [0, 0, 0, 1, 0, 0] == 0 && lform a₅ [0, 1, 0, 0, 0, 0] == -1 &&
        decide (lcomb [4, 3, 5, 6, 4, 2] [a₀, [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0],
          [0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0], a₅] ∈ e6F4S27)) ||
      (a₀ == [0, 0, 0, 0, 0, 1] && a₅ == [-1, -2, -2, -3, -2, -1])

@[expose] def e6TriSearchB : Bool :=
  Tag.E6.artifactRoots.all fun a₀ =>
    !(lform a₀ [0, 0, 0, 0, 1, 0] == 0 && lform a₀ [0, 1, 0, 0, 0, 0] == -1 &&
      lform a₀ [0, 0, 0, 1, 0, 0] == 0 && lform a₀ [0, 0, 1, 0, 0, 0] == 0) ||
    Tag.E6.artifactRoots.all fun a₅ =>
      !(lform a₅ [0, 0, 0, 0, 1, 0] == 0 && lform a₅ [0, 1, 0, 0, 0, 0] == 0 &&
        lform a₅ [0, 0, 0, 1, 0, 0] == 0 && lform a₅ [0, 0, 1, 0, 0, 0] == -1 &&
        decide (lcomb [4, 3, 5, 6, 4, 2] [a₀, [0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0],
          [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], a₅] ∈ e6F4S27)) ||
      (a₀ == [-1, -2, -2, -3, -2, -1] && a₅ == [1, 0, 0, 0, 0, 0])

theorem e6TriSearchA_eq : e6TriSearchA = true := by
  decide +kernel

theorem e6TriSearchB_eq : e6TriSearchB = true := by
  decide +kernel


theorem e6Tri_images_A {g : WeylGroup Tag.E6}
    (h1 : g • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1)
    (h2 : g • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1)
    (h3 : g • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1)
    (h4 : g • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 1 1) :
    List.ofFn (g • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 0, 0, 0, 1] ∧
      List.ofFn (g • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) = [-1, -2, -2, -3, -2, -1] := by
  have hr : ∀ i, List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∈ Tag.E6.artifactRoots :=
    fun i => isRoot_iff_mem_artifactRoots.1 (IsRoot.smul (isRoot_single Tag.E6 i) g)
  have pf : ∀ (i j : Fin Tag.E6.rank) (l : List ℤ),
      List.ofFn (g • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = l →
      lform (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) l = Tag.E6.cartan i j := by
    intro i j l hl
    rw [← hl, lform_ofFn, e6Form_smul, e6Form_single]
  have e1 : List.ofFn (g • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 1, 0, 0, 0] := by
    rw [h1]; decide
  have e2 : List.ofFn (g • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 0, 0, 1, 0] := by
    rw [h2]; decide
  have e3 : List.ofFn (g • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 0, 1, 0, 0] := by
    rw [h3]; decide
  have e4 : List.ofFn (g • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) = [0, 1, 0, 0, 0, 0] := by
    rw [h4]; decide
  have hc := lcomb_gTuple g
  rw [gTuple, ofFn_six, e1, e2, e3, e4] at hc
  have hS := e6F4_S27_mem g
  rw [← hc] at hS
  have h := e6TriSearchA_eq
  rw [e6TriSearchA] at h
  have g₀ := bor_of_not (List.all_eq_true.1 h _ (hr 0)) (by
    rw [pf 0 1 _ e1, pf 0 2 _ e2, pf 0 3 _ e3, pf 0 4 _ e4]
    decide)
  have g₅ := bor_of_not (List.all_eq_true.1 g₀ _ (hr 5)) (by
    rw [pf 5 1 _ e1, pf 5 2 _ e2, pf 5 3 _ e3, pf 5 4 _ e4, decide_eq_true hS]
    decide)
  simpa using g₅

theorem e6Tri_images_B {g : WeylGroup Tag.E6}
    (h1 : g • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1)
    (h2 : g • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 1 1)
    (h3 : g • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1)
    (h4 : g • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1) :
    List.ofFn (g • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) = [-1, -2, -2, -3, -2, -1] ∧
      List.ofFn (g • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) = [1, 0, 0, 0, 0, 0] := by
  have hr : ∀ i, List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∈ Tag.E6.artifactRoots :=
    fun i => isRoot_iff_mem_artifactRoots.1 (IsRoot.smul (isRoot_single Tag.E6 i) g)
  have pf : ∀ (i j : Fin Tag.E6.rank) (l : List ℤ),
      List.ofFn (g • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = l →
      lform (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) l = Tag.E6.cartan i j := by
    intro i j l hl
    rw [← hl, lform_ofFn, e6Form_smul, e6Form_single]
  have e1 : List.ofFn (g • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 0, 0, 1, 0] := by
    rw [h1]; decide
  have e2 : List.ofFn (g • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) = [0, 1, 0, 0, 0, 0] := by
    rw [h2]; decide
  have e3 : List.ofFn (g • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 0, 1, 0, 0] := by
    rw [h3]; decide
  have e4 : List.ofFn (g • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) = [0, 0, 1, 0, 0, 0] := by
    rw [h4]; decide
  have hc := lcomb_gTuple g
  rw [gTuple, ofFn_six, e1, e2, e3, e4] at hc
  have hS := e6F4_S27_mem g
  rw [← hc] at hS
  have h := e6TriSearchB_eq
  rw [e6TriSearchB] at h
  have g₀ := bor_of_not (List.all_eq_true.1 h _ (hr 0)) (by
    rw [pf 0 1 _ e1, pf 0 2 _ e2, pf 0 3 _ e3, pf 0 4 _ e4]
    decide)
  have g₅ := bor_of_not (List.all_eq_true.1 g₀ _ (hr 5)) (by
    rw [pf 5 1 _ e1, pf 5 2 _ e2, pf 5 3 _ e3, pf 5 4 _ e4, decide_eq_true hS]
    decide)
  simpa using g₅

private def e6NegTheta : Fin Tag.E6.rank → ℤ := ![-1, -2, -2, -3, -2, -1]

private theorem eq_one_of_pow_three_of_inv {G : Type*} [CommGroup G] {x : G} (h3 : x ^ 3 = 1)
    (h : x⁻¹ * (x ^ 2)⁻¹ = (x ^ 2) ^ 2) : x = 1 := by
  have e1 : x⁻¹ * (x ^ 2)⁻¹ = (x ^ 3)⁻¹ := by
    rw [pow_succ x 2, mul_inv_rev, mul_comm]
  have e2 : (x ^ 2) ^ 2 = x ^ 3 * x := by
    rw [← pow_mul, ← pow_succ]
  rw [e1, e2, h3, inv_one, one_mul] at h
  exact h.symm

theorem eq_one_of_e6_triality {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha3 : ∀ i, a i ^ 3 = 1) {q : ℕ} (hq : q % 3 = 2) {v w u : WeylGroup Tag.E6}
    (hfrob : ∀ γ, IsRoot Tag.E6 γ → rootChar a (w • γ) = rootChar a γ ^ q)
    (hker : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), rootChar a (v • α) = 1)
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ : π = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
      π = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2])
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    a = 1 := by
  classical
  let ψh : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ :=
    (rootCharHom a).comp (AddMonoidHom.toMultiplicative
      (DistribSMul.toAddMonoidHom (Fin Tag.E6.rank → ℤ) v))
  have hψh : ∀ x, ψh (Multiplicative.ofAdd x) = rootChar a (v • x) := fun x => rfl
  have hψprod : ∀ z : Fin Tag.E6.rank → ℤ,
      rootChar a (v • z) = ∏ k, rootChar a (v • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) ^ z k := by
    intro z
    have hz : z = ∑ k, z k • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) := by
      funext m
      simp [Finset.sum_apply, Pi.single_apply]
    have h1 : ψh (Multiplicative.ofAdd (∑ k, z k • (Pi.single k 1 : Fin Tag.E6.rank → ℤ))) =
        ∏ k, rootChar a (v • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) ^ z k := by
      rw [ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [ofAdd_zsmul, map_zpow]
      rfl
    rw [← h1, ← hz]
    rfl
  have hψ3 : ∀ y : Fin Tag.E6.rank → ℤ, rootChar a y ^ 3 = 1 := by
    intro y
    rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hpowq : ∀ x : Lˣ, x ^ 3 = 1 → x ^ q = x ^ 2 := by
    intro x hx
    have hq' : q = 3 * (q / 3) + 2 := by omega
    rw [hq', pow_add, pow_mul, hx, one_pow, one_mul]
  have hψu : ∀ u' ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6), ∀ x : Fin Tag.E6.rank → ℤ,
      rootChar a (v • (u' • x)) = rootChar a (v • x) := by
    intro u' hu' x
    have hd : ∀ k ∉ d4Nodes Tag.E6, (u' • x - x) k = 0 := fun k hk => by
      rw [Pi.sub_apply, smul_apply_of_mem_parabolicWeylGroup hu' x hk, sub_self]
    have hz : rootChar a (v • (u' • x - x)) = 1 := by
      rw [hψprod]
      refine Finset.prod_eq_one fun k _ => ?_
      by_cases hk : k ∈ d4Nodes Tag.E6
      · rw [hker _ (single_mem_parabolicRoots hk), one_zpow]
      · rw [hd k hk, zpow_zero]
    calc rootChar a (v • (u' • x)) = rootChar a (v • (x + (u' • x - x))) := by
          congr 2
          abel
      _ = rootChar a (v • x) * rootChar a (v • (u' • x - x)) := by rw [smul_add, rootChar_add]
      _ = rootChar a (v • x) := by rw [hz, mul_one]
  set w'' : WeylGroup Tag.E6 := u⁻¹ * (v⁻¹ * w * v) with hw''
  have hw''ψ : ∀ δ, IsRoot Tag.E6 δ → rootChar a (v • (w'' • δ)) = rootChar a (v • δ) ^ q := by
    intro δ hδ
    rw [hw'', mul_smul, hψu _ (inv_mem hu), mul_smul, mul_smul, smul_inv_smul,
      hfrob _ (IsRoot.smul hδ v)]
  have hw''J : ∀ j ∈ d4Nodes Tag.E6,
      w'' • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π j) 1 := by
    intro j hj
    rw [hw'', mul_smul, hact _ (single_mem_parabolicRoots hj), permLattice_single, inv_smul_smul]
  have hJ : ∀ j : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 → j ∈ d4Nodes Tag.E6 :=
    fun j h1 h4 => ⟨h1, h4⟩
  have hψJ : ∀ j : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 →
      rootChar a (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 :=
    fun j h1 h4 => hker _ (single_mem_parabolicRoots (hJ j h1 h4))
  set x := rootChar a (v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) with hx
  set y := rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) with hy
  have hθ : rootChar a (v • e6NegTheta) = x⁻¹ * y⁻¹ := by
    rw [hψprod, Finset.prod_eq_mul (0 : Fin Tag.E6.rank) 5 (by decide)
      (fun c _ hc => by
        have h0 : c.val ≠ 0 := fun h => hc.1 (Fin.ext h)
        have h5 : c.val ≠ 5 := fun h => hc.2 (Fin.ext h)
        have h6 : c.val < 6 := c.isLt
        rw [hψJ c (by omega) (by omega), one_zpow])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
    rw [show e6NegTheta 0 = -1 from rfl, show e6NegTheta 5 = -1 from rfl, zpow_neg_one,
      zpow_neg_one]
  have hroot0 : IsRoot Tag.E6 (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 0
  have hroot5 : IsRoot Tag.E6 (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 5
  have hx3 : x ^ 3 = 1 := hψ3 _
  have hy3 : y ^ 3 = 1 := hψ3 _
  have hxy : x = 1 ∧ y = 1 := by
    rcases hπ with rfl | rfl
    · have hp1 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 2, e6Idx 4] 1 = 2 := by decide
      have hp2 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 2, e6Idx 4] 2 = 4 := by decide
      have hp3 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 2, e6Idx 4] 3 = 3 := by decide
      have hp4 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 2, e6Idx 4] 4 = 1 := by decide
      have h1 := hw''J 1 (hJ 1 (by decide) (by decide))
      have h2 := hw''J 2 (hJ 2 (by decide) (by decide))
      have h3 := hw''J 3 (hJ 3 (by decide) (by decide))
      have h4 := hw''J 4 (hJ 4 (by decide) (by decide))
      rw [hp1] at h1
      rw [hp2] at h2
      rw [hp3] at h3
      rw [hp4] at h4
      obtain ⟨i0, i5⟩ := e6Tri_images_A h1 h2 h3 h4
      have j0 : w'' • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 :=
        List.ofFn_injective (i0.trans (by decide))
      have j5 : w'' • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = e6NegTheta :=
        List.ofFn_injective (i5.trans rfl)
      have r0 := hw''ψ _ hroot0
      have r5 := hw''ψ _ hroot5
      rw [j0, ← hy, ← hx, hpowq x hx3] at r0
      rw [j5, hθ, ← hy, hpowq y hy3] at r5
      rw [r0] at r5
      have hx1 : x = 1 := eq_one_of_pow_three_of_inv hx3 r5
      refine ⟨hx1, ?_⟩
      rw [r0, hx1, one_pow]
    · have hp1 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 4, e6Idx 2] 1 = 4 := by decide
      have hp2 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 4, e6Idx 2] 2 = 1 := by decide
      have hp3 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 4, e6Idx 2] 3 = 3 := by decide
      have hp4 : List.formPerm [e6Idx (τ := Tag.E6) 1, e6Idx 4, e6Idx 2] 4 = 2 := by decide
      have h1 := hw''J 1 (hJ 1 (by decide) (by decide))
      have h2 := hw''J 2 (hJ 2 (by decide) (by decide))
      have h3 := hw''J 3 (hJ 3 (by decide) (by decide))
      have h4 := hw''J 4 (hJ 4 (by decide) (by decide))
      rw [hp1] at h1
      rw [hp2] at h2
      rw [hp3] at h3
      rw [hp4] at h4
      obtain ⟨i0, i5⟩ := e6Tri_images_B h1 h2 h3 h4
      have j0 : w'' • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = e6NegTheta :=
        List.ofFn_injective (i0.trans rfl)
      have j5 : w'' • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 :=
        List.ofFn_injective (i5.trans (by decide))
      have r0 := hw''ψ _ hroot0
      have r5 := hw''ψ _ hroot5
      rw [j0, hθ, ← hx, hpowq x hx3] at r0
      rw [j5, ← hx, ← hy, hpowq y hy3] at r5
      rw [r5] at r0
      have hy1 : y = 1 := eq_one_of_pow_three_of_inv hy3 (by rw [mul_comm]; exact r0)
      refine ⟨?_, hy1⟩
      rw [r5, hy1, one_pow]
  have hall : ∀ k : Fin Tag.E6.rank,
      rootChar a (v • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) = 1 := by
    intro k
    fin_cases k
    · exact hxy.1
    · exact hψJ 1 (by decide) (by decide)
    · exact hψJ 2 (by decide) (by decide)
    · exact hψJ 3 (by decide) (by decide)
    · exact hψJ 4 (by decide) (by decide)
    · exact hxy.2
  funext i
  have h1 : rootChar a (v • (v⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) = 1 := by
    rw [hψprod]
    exact Finset.prod_eq_one fun k _ => by rw [hall k, one_zpow]
  rw [smul_inv_smul] at h1
  have h2 := rootChar_nsmul_single a i 1
  rw [one_smul, pow_one] at h2
  rw [Pi.one_apply, ← h2, h1]

end E6Triality

section NoD4Three

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem false_of_d4Class_three_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E7 L p₀) (h3L : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ}
    (hTp : rootDiagUnit Tag.E7 a ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) : False := by
  classical
  obtain ⟨v, μ, hμ, hall⟩ := S.exists_kacT_of_prime Nat.prime_three h3L facts_E7 hTp
  obtain ⟨x, -, hi⟩ := hall i
  set hfin := Set.toFinite (kacE7.comp 3 μ x)
  have hC : kacE7.comp 3 μ x = (hfin.toFinset : Set (Option (Fin Tag.E7.rank))) :=
    hfin.coe_toFinset.symm
  have hCp : ∃ y, y ∉ hfin.toFinset := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacE7 (by norm_num : 0 < 3) μ x
    exact ⟨y, fun h => hy (hfin.mem_toFinset.1 h)⟩
  rw [hC] at hi
  have hrank : hfin.toFinset.card = 4 := by
    rw [← hr, hi, compRank_image, compRank_rootsOf kacE7 facts_E7 hCp]
  have hcount : kacCount Tag.E7 kacE7.θ hfin.toFinset = 24 := by
    rw [← hc, hi, ncard_image_smul, ncard_rootsOf kacE7 facts_E7 hCp]
  have hθ : kacE7.θ = ![2, 2, 3, 4, 3, 2, 1] := rfl
  rw [hθ] at hcount
  have hD := kacCount_E7_four _ hrank hcount
  have hmem : ∀ y, y ∈ kacE7.comp 3 μ x ↔
      y ∈ ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E7.rank))) := by
    intro y
    rw [hC, hD, Finset.mem_coe]
  have hnb : ∀ z y : Option (Fin Tag.E7.rank), z ∈ kacE7.comp 3 μ x → kacE7.Adj z y →
      y ∉ kacE7.comp 3 μ x → ¬ kacE7.IsZ 3 μ y := by
    intro z y hz hadj hy hZ
    exact hy ⟨hZ, Relation.EqvGen.trans _ _ _ hz.2 (Relation.EqvGen.rel _ _ ⟨hz.1, hZ, hadj⟩)⟩
  have hμ0 : μ 0 ≠ 0 := hnb (some 2) (some 0) ((hmem (some 2)).2 (by decide))
    ⟨by decide, show iform (Pi.single 2 1 : Fin Tag.E7.rank → ℤ) (Pi.single 0 1) ≠ 0 by decide⟩
    (fun h => absurd ((hmem (some 0)).1 h) (by decide))
  have hμ5 : μ 5 ≠ 0 := hnb (some 4) (some 5) ((hmem (some 4)).2 (by decide))
    ⟨by decide, show iform (Pi.single 4 1 : Fin Tag.E7.rank → ℤ) (Pi.single 5 1) ≠ 0 by decide⟩
    (fun h => absurd ((hmem (some 5)).1 h) (by decide))
  obtain ⟨hnn, hle⟩ := hμ
  have h2 : ∑ k ∈ ({0, 5} : Finset (Fin Tag.E7.rank)), kacE7.θ k * μ k ≤ kacE7.θ ⬝ᵥ μ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => mul_nonneg (kacE7.θ_nonneg k) (hnn k))
  rw [Finset.sum_pair (show (0 : Fin Tag.E7.rank) ≠ 5 by decide)] at h2
  have h0 : kacE7.θ 0 = 2 := rfl
  have h5 : kacE7.θ 5 = 2 := rfl
  rw [h0, h5] at h2
  have := hnn 0
  have := hnn 5
  omega

theorem false_of_d4Class_three_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) (h3L : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ}
    (hTp : rootDiagUnit Tag.E8 a ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) : False := by
  classical
  obtain ⟨v, μ, hμ, hall⟩ := S.exists_kacT_of_prime Nat.prime_three h3L facts_E8 hTp
  obtain ⟨x, -, hi⟩ := hall i
  set hfin := Set.toFinite (kacE8.comp 3 μ x)
  have hC : kacE8.comp 3 μ x = (hfin.toFinset : Set (Option (Fin Tag.E8.rank))) :=
    hfin.coe_toFinset.symm
  have hCp : ∃ y, y ∉ hfin.toFinset := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacE8 (by norm_num : 0 < 3) μ x
    exact ⟨y, fun h => hy (hfin.mem_toFinset.1 h)⟩
  rw [hC] at hi
  have hrank : hfin.toFinset.card = 4 := by
    rw [← hr, hi, compRank_image, compRank_rootsOf kacE8 facts_E8 hCp]
  have hcount : kacCount Tag.E8 kacE8.θ hfin.toFinset = 24 := by
    rw [← hc, hi, ncard_image_smul, ncard_rootsOf kacE8 facts_E8 hCp]
  have hθ : kacE8.θ = ![2, 3, 4, 6, 5, 4, 3, 2] := rfl
  rw [hθ] at hcount
  have hD := kacCount_E8_four _ hrank hcount
  have hmem : ∀ y, y ∈ kacE8.comp 3 μ x ↔
      y ∈ ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E8.rank))) := by
    intro y
    rw [hC, hD, Finset.mem_coe]
  have hnb : ∀ z y : Option (Fin Tag.E8.rank), z ∈ kacE8.comp 3 μ x → kacE8.Adj z y →
      y ∉ kacE8.comp 3 μ x → ¬ kacE8.IsZ 3 μ y := by
    intro z y hz hadj hy hZ
    exact hy ⟨hZ, Relation.EqvGen.trans _ _ _ hz.2 (Relation.EqvGen.rel _ _ ⟨hz.1, hZ, hadj⟩)⟩
  have hμ0 : μ 0 ≠ 0 := hnb (some 2) (some 0) ((hmem (some 2)).2 (by decide))
    ⟨by decide, show iform (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) (Pi.single 0 1) ≠ 0 by decide⟩
    (fun h => absurd ((hmem (some 0)).1 h) (by decide))
  have hμ5 : μ 5 ≠ 0 := hnb (some 4) (some 5) ((hmem (some 4)).2 (by decide))
    ⟨by decide, show iform (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) (Pi.single 5 1) ≠ 0 by decide⟩
    (fun h => absurd ((hmem (some 5)).1 h) (by decide))
  obtain ⟨hnn, hle⟩ := hμ
  have h2 : ∑ k ∈ ({0, 5} : Finset (Fin Tag.E8.rank)), kacE8.θ k * μ k ≤ kacE8.θ ⬝ᵥ μ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => mul_nonneg (kacE8.θ_nonneg k) (hnn k))
  rw [Finset.sum_pair (show (0 : Fin Tag.E8.rank) ≠ 5 by decide)] at h2
  have h0 : kacE8.θ 0 = 2 := rfl
  have h5 : kacE8.θ 5 = 4 := rfl
  rw [h0, h5] at h2
  have := hnn 0
  have := hnn 5
  omega

end NoD4Three

section D4Rank4

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


theorem tagLie_rank_four_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hTp : rootDiagUnit Tag.E6 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType (fun t => t = .POmegaMinus ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
    (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin hρ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    exact tagLie_rationalComponent_of_d4_outer d4Base_E6 (d4SwapLayer_E6 hE6) d4SwapLayerTag_E6
      (Or.inl rfl) S hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin
      (d4_outer_htri_of_layer d4TrialityLayer_E6 d4TrialityLayerTag_E6 (Or.inr rfl) S hFr hΦ' hn
        v)
  · rw [hs, Function.iterate_one] at hnin
    refine tagLie_rationalComponent_of_d4_twE6_of_layer S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv
      hρ hnin (fun ℓ f _ _ hf hqf n hn u hu π hleaf hπ1 _ hact => ?_)
    have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
    have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
    have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
    have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
        (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
    have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
        (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
    have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
        (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
    rcases hleaf with hc | hc | hc | hc | hc | hc
    · exact absurd hc hπ1
    · rw [hc] at hact
      exact ⟨(twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2,
        (twisted_swap_layer_tag hf h12 hv1 hv2 hn hu hact).mono fun _ ht => Or.inl ht⟩
    · rw [hc] at hact
      exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
        (twisted_swap_layer_tag hf h14 hv1 hv4 hn hu hact).mono fun _ ht => Or.inl ht⟩
    · rw [hc] at hact
      exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
        (twisted_swap_layer_tag hf h24 hv2 hv4 hn hu hact).mono fun _ ht => Or.inl ht⟩
    · rw [hc] at hact
      exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2,
        (twisted_triality_layer_tag hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).mono
          fun _ ht => Or.inr ht⟩
    · rw [hc] at hact
      exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2,
        (twisted_triality_layer_tag hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).mono
          fun _ ht => Or.inr ht⟩

theorem tagLie_rank_four_E6_untw_three {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) (hq3 : S.D.q % 3 = 2)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (ha1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType (· = .POmegaMinus) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  have hℓp : ringChar L ≠ 3 := ringChar_ne_of_pow_eq_one Nat.prime_three hap ha1
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne Nat.prime_three hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime Nat.prime_three hpL facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ :=
    fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ
  refine tagLie_rationalComponent_of_d4_outer (tagP := (· = .POmegaMinus)) d4Base_E6
    (d4SwapLayer_E6 hE6) d4SwapLayerTag_E6 rfl S hFr hΦ hn hρw i v hv hρ hnin ?_
  intro u hu π hπ hact
  exfalso
  apply ha1
  have ha : a = 1 := eq_one_of_e6_triality hap hq3 (v := v) (w := w) (u := u)
    (fun γ hγ => by rw [← hρw γ hγ]; exact S.frob.rootChar_eq a hT γ hγ)
    (fun α hα => by
      have hmem : v • α ∈ componentRoots (rootCharHom a) i := by
        rw [hv]
        exact ⟨α, hα, rfl⟩
      obtain ⟨hk, -⟩ := hmem
      exact hk.2)
    hu hπ hact
  rw [ha]
  exact rootDiagUnit_one

end D4Rank4

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


theorem tagLie_rationalComponent_outerD_high {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TagLieType (· = .POmegaMinus) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨m, e, -, hlie⟩ := lieModel_rationalComponent_of_twoD_highG hp S hT hap h1 i h5
    hn hout (fun _ _ => True)
    (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  exact ⟨.POmegaMinus, m, e, rfl, hlie⟩

theorem tagLie_rationalComponent_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    TagLieType (fun t => IsADETag t ∨ t = .trialityD4) (ringChar L)
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact (tagLie_rationalComponent_typeA S hp hT hap h1 i hA hq).mono
      fun _ ht => Or.inl (isADETag_of_typeA ht)
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact (tagLie_inner_nonA_E6 S hp hpL hT hTp i hA hinner).mono
      fun _ ht => Or.inl (isADETag_of_innerDE ht)
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
      · exact (tagLie_rationalComponent_outerD_high S hp hT hap h1 i h5 hD'.2 hinner).mono
          fun _ ht => Or.inl (ht ▸ isADETag_POmegaMinus)
      · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        have hc24 : (componentRoots (rootCharHom a) i).ncard = 24 := by
          rw [hD'.2, hr4]
        exact (tagLie_rank_four_E6 S hp hpL hT hTp i hr4 hc24 hinner).mono fun _ ht => by
          rcases ht with rfl | rfl
          · exact Or.inl isADETag_POmegaMinus
          · exact Or.inr rfl
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim

theorem tagLie_rationalComponent_untw {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hq3 : S.D.q % 3 = 2) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    TagLieType IsADETag (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hℓp : ringChar L ≠ 3 := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact (tagLie_rationalComponent_typeA S hp hT hap h1 i hA hq).mono
      fun _ ht => isADETag_of_typeA ht
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · rcases hτ with rfl | rfl | rfl
    · exact (tagLie_inner_nonA_E6 S hp hpL hT hTp i hA hinner).mono
        fun _ ht => isADETag_of_innerDE ht
    · exact (tagLie_inner_nonA_E7 S hp hpL hT hTp i hA hinner).mono
        fun _ ht => isADETag_of_innerDE ht
    · exact (tagLie_inner_nonA_E8 S hp hpL hT hTp i hA hinner).mono
        fun _ ht => isADETag_of_innerDE ht
  have hD : ∀ hD' : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1),
      (compRank (componentRoots (rootCharHom a) i) = 4 →
        (componentRoots (rootCharHom a) i).ncard = 24 →
          TagLieType IsADETag (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      TagLieType IsADETag (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    intro hD' h4
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · exact (tagLie_rationalComponent_outerD_high S hp hT hap h1 i h5 hD'.2 hinner).mono
        fun _ ht => ht ▸ isADETag_POmegaMinus
    · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      exact h4 hr4 (by rw [hD'.2, hr4])
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD' fun hr4 hc24 =>
        (tagLie_rank_four_E6_untw_three S hFr hΦ hq3 hT hap h1 i hr4 hc24 hinner).mono
          fun _ ht => ht ▸ isADETag_POmegaMinus
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD' fun hr4 hc24 => (false_of_d4Class_three_E7 S hpL hTp i hr4 hc24).elim
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, isADETag_twistedE6, hlie⟩
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD' fun hr4 hc24 => (false_of_d4Class_three_E8 S hpL hTp i hr4 hc24).elim
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, isADETag_twistedE6, hlie⟩

end Classes

end CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

end
