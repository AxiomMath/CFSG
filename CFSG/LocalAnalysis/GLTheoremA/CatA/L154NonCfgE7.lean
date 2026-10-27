module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgTyped

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Tree


variable {τ : Tag}

theorem l154_exists_tree_of_class_rank (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)}
    {tp : ℕ → ℕ → List ℕ} (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    (adjf : ∀ n : ℕ, Fin n → Fin n → Prop) (nmin : ℕ) (cnt : ℕ → ℕ)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, nmin ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = cnt c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ nmin ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ adjf P.length c d → ¬ adjf P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, adjf P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (Q : ℕ → Prop) (hQ : ∀ P ∈ trees, Q P.length)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : nmin ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      cnt (compRank (componentRoots (rootCharHom a) i))) :
    ∃ (v : WeylGroup τ) (n : ℕ) (l : Fin n → Option (Fin τ.rank)), nmin ≤ n ∧ Q n ∧
      compRank (componentRoots (rootCharHom a) i) = n ∧
      componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l) ∧
      (∀ c d : Fin n, c ≠ d → ¬ adjf n c d → ¬ adjf n d c →
        iform (K.extRoot (l c)) (K.extRoot (l d)) = 0) ∧
      ∀ c d : Fin n, adjf n c d → (nodeIdx (l c), nodeIdx (l d)) ∈ E := by
  classical
  obtain ⟨v, μ, -, hall⟩ := S.exists_kacT_of_prime hp hpL hK hTp
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
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf K hK hCp, hcard c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf K hK hCp]
  have hrank' := hrank
  rw [hrank] at h4 hn
  rw [hncard] at hn
  obtain ⟨P, hP, hsame⟩ := hcount c hc h4 hn
  obtain ⟨hnd, hlen, hnon, hE⟩ := htrees P hP
  have hCP : (C : Set (Option (Fin τ.rank))) = Set.range P.get := by
    rw [Set.range_list_get, ← hCset, hcomp]
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [mem_iff_of_sameSet hsame, List.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [← nodeIdx_injective hzy]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hcP : c.length = P.length := by
    have h1 : (C : Set (Option (Fin τ.rank))).ncard = c.length := by
      rw [Set.ncard_coe_finset]
      exact hcard c hc
    have h2 : (Set.range P.get).ncard = P.length := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ (List.nodup_iff_injective_get.mp hnd),
        Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [← h1, hCP, h2]
  exact ⟨v, P.length, P.get, hlen, hQ P hP, hrank'.trans hcP, by rw [hi', hCP], hnon, hE⟩

end Tree

section Recog


theorem l154_innerModel_E7 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    commutator ↥(rootSpan τ K (rootsOfFam β (Set.range l))) = ⊤ ∧
      LieModel (↥(rootSpan τ K (rootsOfFam β (Set.range l))) ⧸
        Subgroup.center ↥(rootSpan τ K (rootsOfFam β (Set.range l)))) .E7 0 p f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : CFSG.Open.StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, hmodel⟩

end Recog

section Rat


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {ta : Fin τ.rank → Lˣ}

theorem l154_rationalComponent_e7Model (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin 7 → ι)
    (hroots : componentRoots (rootCharHom ta) i = rootsOfFam β (Set.range l))
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ {F : Type} [Field F] (i j : Fin 7), edgeE 7 i j → ∃ θ : SL(3, F) →* ModGL τ F,
      θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l i)) ∧
        θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l j)))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e) :
    LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i))
      .E7 0 r (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) := by
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
  obtain ⟨hperf, hmod⟩ := l154_innerModel_E7 hτ hr hes hcard' β hroot l hgram
    (hframe (F := ↥(fixSubfield σ)))
  rw [← hcomp] at hperf hmod
  have hCperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
    Group.isPerfect_def.2 hperf
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
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hperf g hgsurj hgker
  exact LieModel.of_mulEquiv e1 hmod

end Rat

section E8


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154_classModel_of_e7Class [CharP L 2] (S : LangSetup Tag.E8 L p₀) {p : ℕ}
    (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ}
    (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hTp : rootDiagUnit Tag.E8 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h7 : compRank (componentRoots (rootCharHom a) i) = 7)
    (hn : (componentRoots (rootCharHom a) i).ncard = 126)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ClassModel S i := by
  classical
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hn' : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [hn, h7]
    rfl
  obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
    l154_exists_tree_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card edgeE 6
      eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL hTp i h6 hn'
  have hn7 : n = 7 := by rw [← hrk, h7]
  subst hn7
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := (ringChar.eq L r).symm.trans h2
  have hroots' : componentRoots (rootCharHom a) i =
      rootsOfFam (fun x => v • kacE8.extRoot x) (Set.range l) := by
    rw [hroots, l154_smul_image_rootsOf_eq]
  have hmodel := l154_rationalComponent_e7Model S (Or.inr (Or.inr (Or.inr rfl))) hTor i hinner
    (fun x => v • kacE8.extRoot x) (fun b => IsRoot.smul (kacE8.isRoot_extRoot b) v) l hroots'
    (fun c d hcd h1 h2 => by
      show iform (v • kacE8.extRoot (l c)) (v • kacE8.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (fun {F} _ c d hcd =>
      treeFrames kacE8 (fun {F} _ x y h => e8_frames x y h) v l (edgeE 7) hE (F := F) c d hcd)
    hr he hq
  subst hr2
  refine l154_nonCfgModel_of_lieModel rfl ?_ hmodel
  simp [L154GoodModel]

theorem l154E7Models_holds :
    ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E8 L p₀)
      (p : ℕ) (a : Fin Tag.E8.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
      L154Cls S p a i →
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      compRank (componentRoots (rootCharHom a) i) = 7 →
      (componentRoots (rootCharHom a) i).ncard = 126 → L154ClassModel S i := by
  intro L _ _ _ p₀ S p a i hcls hinner h7 hn
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hcls.prime hcls.pow hcls.ne_one
  exact l154_classModel_of_e7Class S hcls.prime (natCast_ne_zero_of_ringChar_ne hcls.prime hℓp)
    hcls.torus (rootDiagUnit_pow_eq_one_of_forall hcls.pow) i h7 hn hinner

end E8

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
