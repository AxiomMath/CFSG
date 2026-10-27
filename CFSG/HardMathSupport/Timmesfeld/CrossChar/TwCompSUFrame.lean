module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompPath
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

variable
  {τ : Tag}

theorem exists_frame_of_path {L : Type} [Field L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) {m : ℕ} {l : Fin m → Option (Fin τ.rank)} (hl : Function.Injective l)
    (hG : ∀ c d, iform (K.extRoot (l c)) (K.extRoot (l d)) = chainGram c d)
    (hA2 : ∀ (c : Fin m) (h : (c : ℕ) + 1 < m), ∃ (ρ : SL(3, L) →* ModGL τ L)
      (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ), CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧
        σ 0 1 = K.extRoot (l c) ∧ σ 1 2 = K.extRoot (l ⟨c + 1, h⟩))
    (v : WeylGroup τ) :
    ∃ (ψ : SL(m + 1, L) →* ModGL τ L) (σ : Fin (m + 1) → Fin (m + 1) → Fin τ.rank → ℤ),
      IsSLFrame ψ σ ∧ frameRoots σ = (fun α => v • α) '' K.rootsOf (Set.range l) := by
  set β : Fin m → Fin τ.rank → ℤ := fun c => K.extRoot (l c) with hβdef
  have hβ : ∀ c, IsRoot τ (β c) := fun c => K.isRoot_extRoot (l c)
  have hθ : ∀ (c : Fin m) (h : (c : ℕ) + 1 < m), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (β c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (β ⟨c + 1, h⟩) := by
    intro c h
    obtain ⟨ρ, σ, hρ, h01, h12⟩ := hA2 c h
    obtain ⟨θ, hθ0, hθ1⟩ := exists_normalized_a2Frame hρ
    exact ⟨θ, by rw [hθ0, h01], by rw [hθ1, h12]⟩
  obtain ⟨ψ, hψ⟩ := exists_chainHom hτ β hβ hG hθ
  have hframe := isSLFrame_chainHom hτ hβ hG hψ
  refine ⟨(MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom.comp ψ,
    fun a b => v • chainσ β a b, hframe.transport v, ?_⟩
  rw [IsSLFrame.frameRoots_smul, K.rootsOf_range_eq_frameRoots hτ hl hG]

theorem exists_a2Frame_of_word {L : Type} [Field L] {ρ₀ : SL(3, L) →* ModGL τ L}
    {σ₀ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h₀ : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ₀ σ₀)
    (w : List (Fin τ.rank)) {x y : Fin τ.rank → ℤ}
    (hx : CFSG.RankThree.Lattice.wordMat τ w *ᵥ σ₀ 0 1 = x)
    (hy : CFSG.RankThree.Lattice.wordMat τ w *ᵥ σ₀ 1 2 = y) :
    ∃ (ρ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = x ∧ σ 1 2 = y :=
  ⟨_, _, h₀.transport ((coxeterSystem τ).wordProd w),
    by rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, hx],
    by rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, hy]⟩

theorem exists_frame_of_typeA_T_of_prime (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {paths : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 2 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = c.length * (c.length + 1) →
        ∃ P ∈ paths, sameSet c (P.map nodeIdx) = true)
    (hpaths : ∀ P ∈ paths, P.Nodup ∧ 2 ≤ P.length ∧
      (∀ c d : Fin P.length, iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = chainGram c d) ∧
      ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
        (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ E)
    {L : Type} [Field L] [IsAlgClosed L]
    (hframes : ∀ x y : Option (Fin τ.rank), (nodeIdx x, nodeIdx y) ∈ E →
      ∃ (ρ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧ σ 1 2 = K.extRoot y)
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ), 3 ≤ ν ∧
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
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
  rw [hrank] at h2 hn
  rw [hncard] at hn
  obtain ⟨P, hP, hsame⟩ := hcount c hc h2 hn
  obtain ⟨hnd, hlen, hG, hedges⟩ := hpaths P hP
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
  have hA2 : ∀ (k : Fin P.length) (h : (k : ℕ) + 1 < P.length), ∃ (ρ : SL(3, L) →* ModGL τ L)
      (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ), CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧
        σ 0 1 = K.extRoot (P.get k) ∧ σ 1 2 = K.extRoot (P.get ⟨k + 1, h⟩) :=
    fun k h => hframes _ _ (hedges k h)
  obtain ⟨ψ, σ, hψ, hσ⟩ := exists_frame_of_path hτ K (List.nodup_iff_injective_get.1 hnd) hG hA2 v
  refine ⟨P.length + 1, ψ, σ, by omega, hψ, fun a b hab => ?_, ?_⟩
  · rw [mul_one]
    exact CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (hψ.isRoot a b hab)
  · rw [hi', hCP, hσ]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
