module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDMain

variable {τ : Tag}

theorem exists_tree_of_class' (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)}
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
      componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l) ∧
      (∀ c d : Fin n, c ≠ d → ¬ adjf n c d → ¬ adjf n d c →
        iform (K.extRoot (l c)) (K.extRoot (l d)) = 0) ∧
      (∀ c d : Fin n, adjf n c d → (nodeIdx (l c), nodeIdx (l d)) ∈ E) ∧
      n = compRank (componentRoots (rootCharHom a) i) := by
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
  have hlenP : P.length = c.length := by
    have h1 : (C : Set (Option (Fin τ.rank))).ncard = c.length := by
      rw [Set.ncard_coe_finset]
      exact hcard c hc
    rw [hCP] at h1
    rw [← h1, ← Nat.card_coe_set_eq, Nat.card_range_of_injective
      (List.nodup_iff_injective_get.1 hnd)]
    simp
  exact ⟨v, P.length, P.get, hlen, hQ P hP, by rw [hi', hCP], hnon, hE, hlenP.trans hrank.symm⟩

theorem exists_dFrames (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    {m : ℕ} (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m)
    (hε : ∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ))
    (F : Type) [Field F] (j k : Fin m) (hjk : CFSG.LieType.Universal.Spin.cartanD m j k = -1) :
    ∃ θ : SL(3, F) →* ModGL τ F,
      θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (ε.symm j : Fin τ.rank → ℤ) ∧
        θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (ε.symm k : Fin τ.rank → ℤ) := by
  classical
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  obtain ⟨v, n', l, hn4, -, hroots, hnon, hE, hnrank⟩ :=
    exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  have hcardΔ : (simpleRoots (componentRoots (rootCharHom a) i)).card = m := by
    rw [← Fintype.card_coe, Fintype.card_congr ε, Fintype.card_fin]
  have hmrank : m = compRank (componentRoots (rootCharHom a) i) := by rw [compRank_eq_card hΨ, hcardΔ]
  obtain rfl : n' = m := hnrank.trans hmrank.symm
  have hsl : ∀ β ∈ (componentRoots (rootCharHom a) i), iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hEsymm : ∀ c d : Fin n', (nodeIdx (l c), nodeIdx (l d)) ∈ E →
      (nodeIdx (l d), nodeIdx (l c)) ∈ E := fun c d h =>
    (hadj _ _).1 (K.adj_symm ((hadj _ _).2 h))
  have hadjiform : ∀ c d : Fin n', (nodeIdx (l c), nodeIdx (l d)) ∈ E →
      iform (K.extRoot (l c)) (K.extRoot (l d)) = -1 := by
    intro c d h
    obtain ⟨ρ, σ, hfr, h01, h12⟩ := hframes (F := L) (l c) (l d) h
    have e2 : iform (σ 0 2) (σ 0 2) = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (hfr.isRoot 0 2 (by decide))
    have h1 : iform (σ 0 1) (σ 0 1) = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (hfr.isRoot 0 1 (by decide))
    have h2 : iform (σ 1 2) (σ 1 2) = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (hfr.isRoot 1 2 (by decide))
    rw [← hfr.add 0 1 2, iform_add_left, iform_add_right, iform_add_right,
      iform_comm (σ 1 2) (σ 0 1), h1, h2] at e2
    rw [← h01, ← h12]
    omega
  set b' : Fin n' → Fin τ.rank → ℤ := fun c => v • K.extRoot (l c) with hb'
  have hbM : ∀ c d : Fin n', iform (b' c) (b' d) = CFSG.LieType.Universal.Spin.cartanD n' c d := by
    intro c d
    simp only [hb', iform_smul]
    rw [LevisSpin.cartanD_apply]
    by_cases hcd : c = d
    · subst hcd
      rw [if_pos rfl]
      exact CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (K.isRoot_extRoot _)
    · rw [if_neg hcd]
      by_cases hedge : (c.val + 1 = d.val ∧ d.val + 1 < n') ∨ (d.val + 1 = c.val ∧ c.val + 1 < n') ∨
          (c.val + 3 = n' ∧ d.val + 1 = n') ∨ (d.val + 3 = n' ∧ c.val + 1 = n')
      · rw [if_pos hedge]
        rcases hedge with h | h | h | h
        · exact hadjiform c d (hE c d (Or.inl h))
        · rw [iform_comm]
          exact hadjiform d c (hE d c (Or.inl h))
        · exact hadjiform c d (hE c d (Or.inr h))
        · rw [iform_comm]
          exact hadjiform d c (hE d c (Or.inr h))
      · rw [if_neg hedge]
        refine hnon c d hcd (fun h => hedge ?_) (fun h => hedge ?_)
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases h with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h))
  have hb'Ψ : ∀ c, b' c ∈ (componentRoots (rootCharHom a) i) := fun c => by
    rw [hroots]
    refine ⟨K.extRoot (l c), ⟨K.isRoot_extRoot _, fun x => if x = l c then 1 else 0, ?_,
      Or.inl ?_⟩, rfl⟩
    · intro x hx
      by_cases hxc : x = l c
      · exact hxc ▸ ⟨c, rfl⟩
      · exact absurd (by simp [hxc]) hx
    · simp [KacData.combo, apply_ite, ite_smul, Finset.sum_ite_eq']
  have hdiag : ∀ j : Fin n', CFSG.LieType.Universal.Spin.cartanD n' j j = 2 := fun j => by
    rw [LevisSpin.cartanD_apply]
    simp
  have hoff : ∀ j k : Fin n', j ≠ k → CFSG.LieType.Universal.Spin.cartanD n' j k ≠ 2 := by
    intro j k hjk
    rw [LevisSpin.cartanD_apply, if_neg hjk]
    split_ifs <;> omega
  obtain ⟨u, -, π, hπM, hu⟩ := CompsPTwoDBase.exists_weyl_base_transport hΨ ε hsl hε hdiag hoff
    b' hb'Ψ hbM
  have hadjc : CFSG.LieType.Universal.Spin.cartanD n' (π.symm j) (π.symm k) = -1 := by
    rw [← hπM, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hjk
  have hmem : (nodeIdx (l (π.symm j)), nodeIdx (l (π.symm k))) ∈ E := by
    rw [LevisSpin.cartanD_apply] at hadjc
    by_cases hcd : π.symm j = π.symm k
    · rw [if_pos hcd] at hadjc
      omega
    · rw [if_neg hcd] at hadjc
      by_cases hedge : ((π.symm j).val + 1 = (π.symm k).val ∧ (π.symm k).val + 1 < n') ∨
          ((π.symm k).val + 1 = (π.symm j).val ∧ (π.symm j).val + 1 < n') ∨
          ((π.symm j).val + 3 = n' ∧ (π.symm k).val + 1 = n') ∨
          ((π.symm k).val + 3 = n' ∧ (π.symm j).val + 1 = n')
      · rcases hedge with h | h | h | h
        · exact hE _ _ (Or.inl h)
        · exact hEsymm _ _ (hE _ _ (Or.inl h))
        · exact hE _ _ (Or.inr h)
        · exact hEsymm _ _ (hE _ _ (Or.inr h))
      · rw [if_neg hedge] at hadjc
        omega
  obtain ⟨θ, h0, h1⟩ := treeFrames K hframes (u * v) l
    (fun c d => (nodeIdx (l c), nodeIdx (l d)) ∈ E) (fun c d h => h) (F := F) (π.symm j)
    (π.symm k) hmem
  have e1 : ∀ x : Fin n', (u * v) • K.extRoot (l (π.symm x)) = (ε.symm x : Fin τ.rank → ℤ) := by
    intro x
    rw [mul_smul]
    have := hu (π.symm x)
    simp only [hb', Equiv.apply_symm_apply] at this
    exact this
  refine ⟨θ, ?_, ?_⟩
  · rw [h0]
    simp only [e1]
  · rw [h1]
    simp only [e1]

theorem rationalLieType_of_map_eq {G : Type} [Group G] (φ : G ≃* G) {R C : Subgroup G}
    (h : R.map φ.toMonoidHom = C) {ℓ : ℕ} (hC : RationalLieType ℓ C) : RationalLieType ℓ R := by
  let e : ↥R ≃* ↥C :=
    (R.equivMapOfInjective φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr h)
  let g : (↥R ⧸ Subgroup.center ↥R) ≃* (↥C ⧸ Subgroup.center ↥C) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨isChevSimple_congr g.symm hC.1, ⟨fun f => hC.2.false (g.symm.trans f)⟩⟩

end CompsPTwoDMain

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
