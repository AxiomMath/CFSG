module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgTyped

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


private theorem excRec_dInner_aux {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
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
        (componentRoots (rootCharHom a) i)]))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e) :
    StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaPlus
      (compRank (componentRoots (rootCharHom a) i)) r
      (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE, hnr⟩ :=
    CompsPTwoDMain.exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4
      (fun n => 2 * n * (n - 1)) hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i
      h4 hn
  have hroots' : componentRoots (rootCharHom a) i =
      rootsOfFam (fun x => v • K.extRoot x) (Set.range l) := by
    rw [hroots, CFSG.LocalAnalysis.GLTheoremA.K155X.l154_smul_image_rootsOf_eq]
  subst hnr
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.rationalComponent_dModel S hτ hTor
    i hinner hn4 (fun x => v • K.extRoot x) (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l hroots'
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (fun {F} _ c d hcd => treeFrames K hframes v l (edgeD _) hE (F := F) c d hcd) hr he hq

theorem excRec_dInner {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaPlus
      (compRank (componentRoots (rootCharHom a) i)) r
      (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  classical
  have _ := hQS
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  rcases hτ with rfl | rfl | rfl
  · exact excRec_dInner_aux (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hT hTp i h4 hn
      hinner hr he hq
  · exact excRec_dInner_aux (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hT hTp i h4
      hn hinner hr he hq
  · exact excRec_dInner_aux (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hT hTp i h4
      hn hinner hr he hq

theorem excRec_dInner4 {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e) :
    StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaPlus
      (compRank (componentRoots (rootCharHom a) i)) r
      (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  rcases hτ with rfl | rfl | rfl
  · exact excRec_dInner_aux (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hT hTp i h4 hn
      hinner hr he hq
  · exact excRec_dInner_aux (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hT hTp i h4
      hn hinner hr he hq
  · exact excRec_dInner_aux (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hT hTp i h4
      hn hinner hr he hq

end CFSG.LocalAnalysis.GLTheoremA.I167

end
