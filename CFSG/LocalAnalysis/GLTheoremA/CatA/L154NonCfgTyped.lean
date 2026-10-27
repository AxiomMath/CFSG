module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

section Roots

variable {τ : Tag}

theorem l154_smul_image_rootsOf_eq (K : KacData τ) (v : WeylGroup τ) {n : ℕ}
    (l : Fin n → Option (Fin τ.rank)) :
    (fun α => v • α) '' K.rootsOf (Set.range l) =
      rootsOfFam (fun x => v • K.extRoot x) (Set.range l) := by
  set β : Option (Fin τ.rank) → Fin τ.rank → ℤ := fun x => v • K.extRoot x with hβ
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ,
      v • K.combo n' = ∑ x, (n' x : ℤ) • β x := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
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

end Roots

section DClass


variable {τ : Tag}

theorem l154_model_of_dClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    ∃ n e : ℕ, CFSG.Open.StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaPlus n (ringChar L) e := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hrL : ringChar L = r := ringChar.eq L r
  have hroots' : componentRoots (rootCharHom a) i =
      rootsOfFam (fun x => v • K.extRoot x) (Set.range l) := by
    rw [hroots, l154_smul_image_rootsOf_eq]
  refine ⟨n, e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i), ?_⟩
  rw [hrL]
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.rationalComponent_dModel S hτ hTor
    i hinner hn4 (fun x => v • K.extRoot x) (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l hroots'
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (fun {F} _ c d hcd => treeFrames K hframes v l (edgeD n) hE (F := F) c d hcd) hr he hq

end DClass

section DClassTags


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}

theorem l154_model_of_dClass_E6 (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ n e : ℕ, CFSG.Open.StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaPlus n (ringChar L) e :=
  l154_model_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
    e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i h4 hn
    hinner

theorem l154_model_of_dClass_E7 (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ n e : ℕ, CFSG.Open.StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaPlus n (ringChar L) e :=
  l154_model_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
    e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i h4
    hn hinner

theorem l154_model_of_dClass_E8 (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ n e : ℕ, CFSG.Open.StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaPlus n (ringChar L) e :=
  l154_model_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
    e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i h4
    hn hinner

end DClassTags

theorem l154_nonCfgModel_of_statedClassical {X : Type} [Group X] {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (hp : p = 2) (ht : t ∈ classicalTags) (hg : L154GoodModel t n)
    (h : CFSG.Open.StatedClassicalModel X t n p f) : L154NonCfgModel X := by
  subst hp
  exact Or.inl ⟨t, n, f, Or.inl ⟨ht, h⟩, hg⟩

theorem l154_nonCfgModel_of_lieModel {X : Type} [Group X] {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (hp : p = 2) (hg : L154GoodModel t n) (h : LieModel X t n p f) :
    L154NonCfgModel X := by
  subst hp
  exact Or.inl ⟨t, n, f, h, hg⟩

section Outer


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154_classModel_of_twoD [CharP L 2] {p : ℕ} (hp : p.Prime) (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ClassModel S i := by
  obtain ⟨m, e, -, hlie⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_twoD_highG hp S
      hT hap h1 i h5 hn hout (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  exact l154_nonCfgModel_of_lieModel (ringChar.eq L 2) (by simp [L154GoodModel]) hlie

end Outer

section RankOne


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154_classModel_of_rankOne [CharP L 2]
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (h1 : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154ClassModel S i := by
  obtain ⟨f, -, -, hmodel⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_rankOne_model S hT i h1 hn hQS
  exact l154_nonCfgModel_of_statedClassical (ringChar.eq L 2) (by simp [classicalTags])
    (Or.inl ⟨rfl, rfl⟩) hmodel

end RankOne

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
