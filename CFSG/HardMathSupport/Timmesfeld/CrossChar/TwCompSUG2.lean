module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

section Facts

open KacData

theorem iform_G2 (c : Fin Tag.G2.rank → ℤ) :
    iform c c = 6 * c (0 : Fin 2) ^ 2 - 6 * c (0 : Fin 2) * c (1 : Fin 2) +
      2 * c (1 : Fin 2) ^ 2 := by
  have h00 : Tag.G2.symmetrizedCartan (0 : Fin 2) (0 : Fin 2) = 6 := by decide
  have h01 : Tag.G2.symmetrizedCartan (0 : Fin 2) (1 : Fin 2) = -3 := by decide
  have h10 : Tag.G2.symmetrizedCartan (1 : Fin 2) (0 : Fin 2) = -3 := by decide
  have h11 : Tag.G2.symmetrizedCartan (1 : Fin 2) (1 : Fin 2) = 2 := by decide
  show ∑ i : Fin 2, ∑ j : Fin 2, c i * Tag.G2.symmetrizedCartan i j * c j = _
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, h00, h01, h10, h11]
  ring

theorem iform_G2_ne_four (c : Fin Tag.G2.rank → ℤ) : iform c c ≠ 4 := by
  rw [iform_G2]
  intro h
  generalize c (0 : Fin 2) = x at h
  generalize c (1 : Fin 2) = y at h
  have h1 : (2 * y - 3 * x) ^ 2 + 3 * x ^ 2 = 8 := by nlinarith
  have hx : x ^ 2 ≤ 2 := by nlinarith [sq_nonneg (2 * y - 3 * x)]
  have hx1 : -1 ≤ x := by nlinarith
  have hx2 : x ≤ 1 := by nlinarith
  have hy : (2 * y - 3 * x) ^ 2 ≤ 8 := by nlinarith [sq_nonneg x]
  have hy1 : -3 ≤ 2 * y - 3 * x := by nlinarith
  have hy2 : 2 * y - 3 * x ≤ 3 := by nlinarith
  have hy3 : -3 ≤ y := by omega
  have hy4 : y ≤ 3 := by omega
  interval_cases x <;> interval_cases y <;> omega

theorem g2_root_norms : ∀ l ∈ Tag.G2.artifactRoots,
    iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 2 ∨
      iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 6 := by
  decide +kernel

theorem toVec_ofFn_G2 (v : Fin Tag.G2.rank → ℤ) : toVec Tag.G2.rank (List.ofFn v) = v := by
  funext i
  fin_cases i <;> rfl

theorem iform_root_G2 {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β) :
    iform β β = 2 ∨ iform β β = 6 := by
  have h := g2_root_norms _ (isRoot_iff_mem_artifactRoots.1 hβ)
  rwa [toVec_ofFn_G2] at h

theorem split_G2 (S₁ S₂ : Set (Option (Fin Tag.G2.rank)))
    (hS : ∀ x ∈ S₁, ∀ y ∈ S₂, x ≠ y ∧ ¬ kacG2.Adj x y)
    (n₁ n₂ : Option (Fin Tag.G2.rank) → ℕ) (hn₁ : ∀ x, n₁ x ≠ 0 → x ∈ S₁)
    (hn₂ : ∀ x, n₂ x ≠ 0 → x ∈ S₂) (hr : IsRoot Tag.G2 (kacG2.combo n₁ + kacG2.combo n₂)) :
    kacG2.combo n₁ = 0 ∨ kacG2.combo n₂ = 0 := by
  set c₁ := kacG2.combo n₁
  set c₂ := kacG2.combo n₂
  have h0 : iform c₁ c₂ = 0 := kacG2.iform_combo_eq_zero hS hn₁ hn₂
  by_contra hne
  push Not at hne
  obtain ⟨hc₁, hc₂⟩ := hne
  have hβ := iform_root_G2 hr
  rw [iform_add_left, iform_add_right, iform_add_right, h0, iform_comm c₂ c₁, h0] at hβ
  have hp₁ := iform_self_pos hc₁
  have hp₂ := iform_self_pos hc₂
  obtain ⟨m₁, hm₁⟩ := even_iform_self c₁
  obtain ⟨m₂, hm₂⟩ := even_iform_self c₂
  have h4₁ := iform_G2_ne_four c₁
  have h4₂ := iform_G2_ne_four c₂
  omega

theorem facts_G2 : kacG2.Facts where
  θ_pos := show ∀ j : Fin 2, (0 : ℤ) < ![2, 3] j by decide
  le_θ := kacG2.le_θ_of_list ![2, 3] rfl
    (show ∀ l ∈ Tag.G2.artifactRoots, ∀ j : Fin 2, (∀ k : Fin 2, 0 ≤ l.getD k 0) →
      l.getD j 0 ≤ (![2, 3] : Fin 2 → ℤ) j by decide +kernel)
  split := split_G2

end Facts

@[expose] def g2ExtVec : Option (Fin 2) → Fin Tag.G2.rank → ℤ
  | none => -![2, 3]
  | some j => Pi.single j 1

@[expose] def g2Anc : ℕ → List ℕ
  | 0 => [0, 1]
  | 1 => [1]
  | 2 => [2, 1]
  | _ => []

@[expose] def g2EdgeIdx : List (ℕ × ℕ) := [(0, 1), (1, 0), (1, 2), (2, 1)]

@[expose] def g2Conn : List (List ℕ) := [[0], [1], [2], [0, 1], [1, 2], [0, 1, 2]]

@[expose] def g2θ : Fin Tag.G2.rank → ℤ := ![2, 3]

theorem kacG2_extRoot : kacG2.extRoot = g2ExtVec := by
  funext x
  cases x <;> rfl

set_option maxRecDepth 100000

theorem g2_tree : IsTreePaths (Tag.G2.rank + 1) g2EdgeIdx (treePath g2Anc) where
  self := by decide +kernel
  lt := by decide +kernel
  head := by decide +kernel
  last := by decide +kernel
  chain := by decide +kernel
  step := by decide +kernel

theorem g2_adj_raw : ∀ x y : Option (Fin 2),
    (x ≠ y ∧ iform (g2ExtVec x) (g2ExtVec y) ≠ 0) ↔ (nodeIdx x, nodeIdx y) ∈ g2EdgeIdx := by
  decide +kernel

theorem g2_adj :
    ∀ x y : Option (Fin Tag.G2.rank), kacG2.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ g2EdgeIdx := by
  intro x y
  unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.Adj
  rw [kacG2_extRoot]
  exact g2_adj_raw x y

theorem g2_check : ((List.range (Tag.G2.rank + 1)).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => g2Conn.any (sameSet (compIdx (Tag.G2.rank + 1) (treePath g2Anc) zl x))) =
        true := by
  decide +kernel

theorem g2_lt : ∀ c ∈ g2Conn, ∀ w ∈ c, w < Tag.G2.rank + 1 := by
  decide +kernel

theorem g2_card : ∀ c ∈ g2Conn, (c.map (idxNode (r := Tag.G2.rank))).toFinset.card = c.length := by
  decide +kernel

theorem g2_count_raw : ∀ c ∈ g2Conn, 2 ≤ c.length →
    kacCount Tag.G2 ![2, 3] (c.map (idxNode (r := Tag.G2.rank))).toFinset =
      c.length * (c.length + 1) → c = [0, 1] ∨ c = [0, 1, 2] := by
  decide +kernel

@[expose] def g2LongRoots : Set (Fin Tag.G2.rank → ℤ) := {γ | IsRoot Tag.G2 γ ∧ iform γ γ = 6}

theorem g2_long_test : ∀ r ∈ Tag.G2.artifactRoots,
    (kacTest g2θ {none, some 0} (toVec Tag.G2.rank r) ↔
      iform (toVec Tag.G2.rank r) (toVec Tag.G2.rank r) = 6) := by
  decide +kernel

theorem g2_rootsOf_long :
    kacG2.rootsOf (({none, some 0} : Finset (Option (Fin Tag.G2.rank))) :
      Set (Option (Fin Tag.G2.rank))) = g2LongRoots := by
  ext γ
  rw [mem_rootsOf_iff kacG2 facts_G2 ⟨some 1, by decide⟩]
  constructor
  · rintro ⟨hγ, hk⟩
    refine ⟨hγ, ?_⟩
    have h := (g2_long_test _ (isRoot_iff_mem_artifactRoots.1 hγ)).1
      (by rw [toVec_ofFn_G2]; exact hk)
    rwa [toVec_ofFn_G2] at h
  · rintro ⟨hγ, h6⟩
    refine ⟨hγ, ?_⟩
    have h := (g2_long_test _ (isRoot_iff_mem_artifactRoots.1 hγ)).2
      (by rw [toVec_ofFn_G2]; exact h6)
    rwa [toVec_ofFn_G2] at h

section Frames

@[expose] def G2LongA2Frame : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L], ∃ (ψ : SL(3, L) →* ModGL Tag.G2 L)
    (σ : Fin 3 → Fin 3 → Fin Tag.G2.rank → ℤ), IsSLFrame ψ σ ∧ frameRoots σ = g2LongRoots

theorem smul_g2LongRoots (v : WeylGroup Tag.G2) :
    (fun α => v • α) '' g2LongRoots = g2LongRoots := by
  ext γ
  constructor
  · rintro ⟨δ, ⟨hδ, h6⟩, rfl⟩
    exact ⟨IsRoot.smul hδ v, by rw [iform_smul]; exact h6⟩
  · rintro ⟨hγ, h6⟩
    refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hγ v⁻¹, by rw [iform_smul]; exact h6⟩, ?_⟩
    simp

theorem exists_frame_of_typeA_G2_T_of_prime (hG2 : G2LongA2Frame) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup Tag.G2 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.G2.rank → Lˣ}
    (hTp : rootDiagUnit Tag.G2 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.G2 L) (σ : Fin ν → Fin ν → Fin Tag.G2.rank → ℤ) (κ : ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
  classical
  obtain ⟨v, μ, -, hall⟩ := S.exists_kacT_of_prime hp hpL facts_G2 hTp
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := kacG2.exists_comp_eq_of_check g2_tree g2_adj (adm := fun _ => true)
    g2_check rfl hx
  set C : Finset (Option (Fin Tag.G2.rank)) := (c.map (idxNode (r := Tag.G2.rank))).toFinset
    with hCdef
  have hCset : kacG2.comp p μ x = (C : Set (Option (Fin Tag.G2.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (g2_lt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacG2 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacG2.rootsOf (C : Set (Option (Fin Tag.G2.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf kacG2 facts_G2 hCp, g2_card c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount Tag.G2 kacG2.θ (c.map (idxNode (r := Tag.G2.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf kacG2 facts_G2 hCp]
  rw [hrank] at h2 hn
  rw [hncard] at hn
  rcases g2_count_raw c hc h2 hn with rfl | rfl
  · have hC : C = {none, some 0} := by rw [hCdef]; decide
    obtain ⟨ψ, σ, hψ, hσ⟩ := hG2 L
    refine ⟨3, ψ, σ, 3, le_rfl, hψ, by decide, fun a b hab => ?_, ?_⟩
    · have h : σ a b ∈ g2LongRoots := by rw [← hσ]; exact ⟨a, b, hab, rfl⟩
      rw [h.2]
      norm_num
    · rw [hi', hC, g2_rootsOf_long, smul_g2LongRoots, hσ]
  · exfalso
    obtain ⟨y, hy⟩ := hCp
    apply hy
    rw [hCdef]
    revert y
    decide

end Frames

end CFSG.HardMathSupport.Timmesfeld.CrossChar
