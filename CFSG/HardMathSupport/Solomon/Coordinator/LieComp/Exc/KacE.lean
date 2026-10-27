module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

@[expose] def eRootCount (n : ℕ) : ℕ :=
  if n = 6 then 72 else if n = 7 then 126 else if n = 8 then 240 else 0


variable {τ : Tag}

theorem rationalLieType_of_eClass (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
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
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  refine rationalLieType_of_tree K S hTor i hinner v l hroots ?_
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
  · exact innerRecog_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact innerRecog_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact innerRecog_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
