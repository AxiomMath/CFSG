module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

theorem ratCatExp_of_innerRecogOver
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      InnerRecogOver (ringChar L) (Nat.card ↥K) ↥(componentRootSpan K (rootCharHom ta) i)) :
    RationalCatalogueExp S i := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  have hrecσ := hrec (fixSubfield σ) hfin hcard
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom ta) i,
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hrecσ.1)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  have h := (hrecσ.of_range f hker hRf).2
  rw [hcard] at h
  exact ⟨_, Or.inl rfl, h⟩

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem ratCatExp_of_tree
    {τ : Tag}
    (K : KacData τ) {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hTor : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      InnerRecogOver p (p ^ f)
        ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l)))) :
    RationalCatalogueExp S i := by
  classical
  refine ratCatExp_of_innerRecogOver S hTor i hinner (fun K' hK' _ => ?_)
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
  rw [hK'card]
  exact hrec ↥K' (ringChar L) f hprime f.pos hK'card

theorem ratCatExp_of_dClass
    {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    RationalCatalogueExp S i := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  refine ratCatExp_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact innerRecogOver_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

theorem ratCatExp_of_eClass
    {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    RationalCatalogueExp S i := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  refine ratCatExp_of_tree K S hTor i hinner v l hroots ?_
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
  · exact innerRecogOver_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact innerRecogOver_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact innerRecogOver_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr

theorem ratCatExp_of_inner_nonA_E6
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact ratCatExp_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i hD.1
      hD.2 hinner
  · exact ratCatExp_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp
      i hE.1 hE.2 hinner

theorem ratCatExp_of_inner_nonA_E7
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact ratCatExp_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner
  · exact ratCatExp_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner

theorem ratCatExp_of_inner_nonA_E8
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact ratCatExp_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i
      hD.1 hD.2 hinner
  · exact ratCatExp_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor
      hTp i hE.1 hE.2 hinner

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq blk spBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_le_sup)
open CFSG.SeitzReduction.SymplecticPilot (isSimpleGroup_commutator_statedSp_two)
open scoped Matrix

theorem ratCatExp_of_f4Levi_class_any
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogueExp S i := by
  classical
  refine ratCatExp_of_innerRecogOver S hTor i hinner (fun K' hfin _ => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    show rootSpan Tag.F4 K' (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardf⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardf
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have hrec := innerRecogOver_f4_levi_any hJ hprime f.pos hK'card
  have hsub : subsystemGroup Tag.F4 ↥K' J = rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 J) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) ↥K'
  rw [hsub] at hrec
  rw [hK'card]
  exact innerRecogOver_rootSpan_smul v (fun α hα => hα.1) hrec

theorem ratCatExp_of_f4B2_class
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    RationalCatalogueExp S i := by
  classical
  refine ratCatExp_of_innerRecogOver S hTor i hinner (fun K' hfin hcardK' => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2) := by
    show rootSpan Tag.F4 K' (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardf⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardf
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have h3 : 3 ≤ Nat.card ↥K' := hcardK' ▸ hQ
  have hrec := innerRecogOver_f4_B2 hprime f.pos hK'card h3
  have hsub : subsystemGroup Tag.F4 ↥K' f4LeviB2 =
      rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 f4LeviB2) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := f4LeviB2) ↥K'
  rw [hsub] at hrec
  rw [hK'card]
  exact innerRecogOver_rootSpan_smul v (fun α hα => hα.1) hrec

theorem ratCatExp_of_f4B2_two
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalCatalogueExp S i := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨K', hfin, C, D, hC, hD, hcard, f, hf1, hker, hf2⟩ :=
    exists_inner_cover_derived_two S hT i hinner hQ
  haveI : Fintype ↥K' := Fintype.ofFinite _
  have hcard' : Fintype.card ↥K' = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hch : ringChar L = 2 := by
    have h2 := ringChar_eq_of_natCard_eq_pow Nat.prime_two (K := ↥K') (f := 1)
      (by rw [hcard]; norm_num) Nat.one_pos
    rw [← ringChar_subfield' K', h2]
  have hQ2 : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 := by
    obtain ⟨r, e, hr, -, he, hq⟩ := exists_char_pow S
    have h2 : 2 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
      rw [hq, ← pow_mul]
      exact le_trans hr.two_le (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
    omega
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum ↥K').isFiniteType
    (Dv := (f4Datum ↥K').divisible) rfl
  obtain ⟨Cc, -, hCc⟩ := f4_commutatorFormula ↥K' O
  have hE := f4_chevalleyExtras ↥K' O Cc hCc
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 ↥K' →* adjointGroup .F4 ↥K',
      φ.comp (spBlock ↥K' 1) = ρF (f4Node 1) ∧ φ.comp (spBlock ↥K' 0) = ρF (f4Node 2) := by
    obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    exact ⟨φ, hb1, hb0⟩
  have hφrange : φ.range = rankOne (f4Datum ↥K').rootGroup (f4Node 1) ⊔
      rankOne (f4Datum ↥K').rootGroup (f4Node 2) := by
    rw [ClassicalInvolution.Q3.Q3V.range_eq_sup_of_spBlocks hφs hφl, hρFr, hρFr, sup_comm]
  set n := canonicalRep (coxeterSystem Tag.F4) ↥K' v with hn
  set ψ : StatedSp 2 ↥K' →* ModGL Tag.F4 ↥K' :=
    (MulAut.conj n).toMonoidHom.comp ((adjointGroup .F4 ↥K').subtype.comp φ) with hψ
  have hψrange : ψ.range = C := by
    have hmap := (canonical_weyl_root_transport Tag.F4 ↥K').1 v (parabolicRoots Tag.F4 f4LeviB2)
      (fun α hα => hα.1)
    have hsub : subsystemGroup Tag.F4 ↥K' f4LeviB2 =
        rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 f4LeviB2) :=
      CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := f4LeviB2) ↥K'
    have hCeq : C = rootSpan Tag.F4 ↥K' ((fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2) := by
      rw [hC]
      show rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i) = _
      rw [hroots]
    rw [hCeq, ← hmap, ← hsub, ← map_subtype_sup_b2, ← hφrange, hψ, MonoidHom.range_comp,
      MonoidHom.range_comp]
  set X' : Subgroup (StatedSp 2 ↥K') := commutator (StatedSp 2 ↥K') with hX'
  have hDmap : D = X'.map ψ := by
    rw [hD, ← hψrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hX', commutator_def]
  have hX : LieFactorData 2 ↥X' := spFourTwoFacts_holds ↥K' hcard'
  have hs : IsSimpleGroup ↥X' := isSimpleGroup_commutator_statedSp_two hcard
  have hXp : ⁅X', X'⁆ = X' := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hX.perfect)
  have hperfD : ⁅D, D⁆ = D := by
    rw [hDmap, ← Subgroup.map_commutator, hXp]
  have hRf := le_antisymm hf1 (hf2 hperfD)
  let ψX : ↥X' →* ↥D := (ψ.comp X'.subtype).codRestrict D (fun x => by
    rw [hDmap]
    exact ⟨x, x.2, rfl⟩)
  have hψXsurj : Function.Surjective ψX := by
    rintro ⟨y, hy⟩
    rw [hDmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hΦrange : (f.comp ψX).range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψXsurj, ← MonoidHom.range_eq_map]
  have hR1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≠ ⊥ := by
    intro h
    have hsimple : IsSimpleGroup (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := hqs.2.1
    haveI := hsimple.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    have : g = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h g.1 g.2)
    rw [this]
    rfl
  set Φ : ↥X' →* ModGL Tag.F4 L := f.comp ψX with hΦ
  have hRΦ : rationalComponent S.ρ S.Γ (rootCharHom a) i = Φ.range := hRf.trans hΦrange.symm
  have hkerΦ : Φ.ker = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal Φ.ker with h | h
    · exact h
    · exfalso
      apply hR1
      rw [hRΦ, Subgroup.eq_bot_iff_forall]
      rintro _ ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
  let eR : ↥X' ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff Φ).1 hkerΦ)).trans
      (MulEquiv.subgroupCongr hRΦ.symm)
  have hcat := (catalogueOver_sp_four_two ↥K' hcard').of_mulEquiv eR
  refine ⟨_, Or.inl rfl, ?_⟩
  rw [hch, hQ2]
  exact hcat

theorem ratCatExp_of_inner_nonA_F4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalCatalogueExp S i := by
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hnonA with ⟨v, hroots, -, -⟩ |
      ⟨v, J, hJ, hroots, -, -⟩
  · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · exact ratCatExp_of_f4B2_class S hT i v hroots hinner hQ
    · exact ratCatExp_of_f4B2_two S hT i v hroots hinner (not_le.1 hQ) hqs
  · exact ratCatExp_of_f4Levi_class_any S hT i v hJ hroots hinner

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
