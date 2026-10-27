module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenSiegel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNodePairs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23 blockSL2 blockSL3)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear consecutiveBlock)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

section Reindex

variable {F : Type} [Field F]

theorem map_reindex_blockSpecialLinear {n : ℕ} (ε : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    (blockSpecialLinear (K := F) I).map (LinearPilot.reindexSpecialLinear (K := F) ε).toMonoidHom =
      blockSpecialLinear (K := F) (I.map ε.toEmbedding) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact reindex_mem_blockSpecialLinear ε hx
  · intro y hy
    refine ⟨LinearPilot.reindexSpecialLinear (K := F) ε.symm y, ?_, ?_⟩
    · have h := reindex_mem_blockSpecialLinear (F := F) ε.symm hy
      have hI : (I.map ε.toEmbedding).map ε.symm.toEmbedding = I := by
        ext a
        simp
      rwa [hI] at h
    · apply Subtype.ext
      change reindex ε ε (reindex ε.symm ε.symm (y : Matrix (Fin n) (Fin n) F)) = _
      simp

@[expose] def chainPerm : Equiv.Perm (Fin (2 * 2 + 1)) := Equiv.swap 1 4 * Equiv.swap 1 2

@[expose] def revPerm5 : Equiv.Perm (Fin (2 * 2 + 1)) := Fin.revPerm

theorem chainPerm_two_three_four :
    (consecutiveBlock (2 * 2 + 1) 1 3).map chainPerm.toEmbedding = oddFixBlock := by decide

theorem chainPerm_zero_one :
    ({0, 1} : Finset (Fin (2 * 2 + 1))).map chainPerm.toEmbedding = oddTwA := by decide

theorem chainPerm_three_four :
    ({3, 4} : Finset (Fin (2 * 2 + 1))).map chainPerm.toEmbedding = oddTwB := by decide

theorem revPerm5_zero_one :
    ({0, 1} : Finset (Fin (2 * 2 + 1))).map revPerm5.toEmbedding = {3, 4} := by decide

theorem revPerm5_three_four :
    ({3, 4} : Finset (Fin (2 * 2 + 1))).map revPerm5.toEmbedding = {0, 1} := by decide

theorem revPerm5_one_two_three :
    (consecutiveBlock (2 * 2 + 1) 1 3).map revPerm5.toEmbedding =
      consecutiveBlock (2 * 2 + 1) 1 3 := by
  decide

end Reindex

section Nodes

theorem nodeSix_lt_cases : ∀ i j : Fin 6, (i : ℕ) + 1 < j →
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 0 ∧ j = 5) ∨ (i = 1 ∧ j = 3) ∨
      (i = 1 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨ (i = 2 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨
        (i = 3 ∧ j = 5) := by
  decide

theorem nodeSix_succ_cases : ∀ i j : Fin 6, (j : ℕ) = i + 1 →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 4) ∨
      (i = 4 ∧ j = 5) := by
  decide

theorem nodeSix_fold_cases : ∀ (j : Fin 3) (i i' : Fin 6), (i : ℕ) = j →
    (i' : ℕ) + j + 1 = 6 →
      (j = 0 ∧ i = 0 ∧ i' = 5) ∨ (j = 1 ∧ i = 1 ∧ i' = 4) ∨ (j = 2 ∧ i = 2 ∧ i' = 3) := by
  decide

theorem ker_comp_blockSL3_le_center {F : Type} [Field F] {E : Type*} [Group E]
    (ρ : SL(2 * 2 + 1, F) →* E) (hker : ρ.ker ≤ center SL(2 * 2 + 1, F))
    (i : Fin (2 * 2)) (h : (i : ℕ) + 1 < 2 * 2) :
    (ρ.comp (blockSL3 F (2 * 2) i h)).ker ≤ center SL(3, F) := by
  intro x hx
  have hc : blockSL3 F (2 * 2) i h x ∈ center SL(2 * 2 + 1, F) := hker hx
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hmem : blockSL3 F (2 * 2) i h x ∈
      blockSpecialLinear (K := F) (consecutiveBlock (2 * 2 + 1) i 3) := by
    rw [← LinearPilot.range_blockSL_eq (by omega)]
    exact ⟨x, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * 2 + 1), a ∉ consecutiveBlock (2 * 2 + 1) i 3 := by
    by_cases hi : (i : ℕ) = 0
    · refine ⟨4, ?_⟩
      rw [LinearPilot.mem_consecutiveBlock]
      intro h4
      have : ((4 : Fin (2 * 2 + 1)) : ℕ) = 4 := rfl
      omega
    · refine ⟨0, ?_⟩
      rw [LinearPilot.mem_consecutiveBlock]
      intro h0
      have : ((0 : Fin (2 * 2 + 1)) : ℕ) = 0 := rfl
      omega
  have haa := (mem_blockSpecialLinear.1 hmem a a (Or.inl ha)).trans (Matrix.one_apply_eq a)
  have hr1 : r = 1 := by
    rw [← hr] at haa
    simpa using haa
  have hx1 : blockSL3 F (2 * 2) i h x = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have : x = 1 := CFSG.ClassicalInvolution.WeakCT.blockSL3_injective (2 * 2) i h
    (by rw [hx1, map_one])
  rw [this]
  exact one_mem _

end Nodes

section Chain

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem disjoint_blockSL2_coords {m : ℕ} {a b : Fin m} (hab : (a : ℕ) + 1 < b) :
    Disjoint ({a.castSucc, a.succ} : Finset (Fin (m + 1))) {b.castSucc, b.succ} := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;>
    · have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega

omit [CharP K 2] in
theorem spLinearNodeSystem_of_chain {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (S : SiegelSwapParam e t)
    (ρ : SL(2 * 2 + 1, K) →* G) (hker : ρ.ker ≤ center SL(2 * 2 + 1, K))
    (h2 : pieceCore e ({2} : Finset (Fin 3)) =
      (blockSpecialLinear (K := K) (consecutiveBlock (2 * 2 + 1) 1 3)).map ρ)
    (h1f : S.fstS (simpleRootSL2 K 1) = (blockSL2 K (2 * 2) 0).range.map ρ)
    (h1s : S.sndS (simpleRootSL2 K 1) = (blockSL2 K (2 * 2) 3).range.map ρ)
    (hO : pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)) :
    SpLinearNodeSystem e f 6 := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hM0 := S.pieceCore_eq_fstS_sup_sndS hK (j := 0) (by decide)
  have hM1 := S.pieceCore_eq_fstS_sup_sndS hK (j := 1) (by decide)
  have hM2 : pieceCore e ({2} : Finset (Fin 3)) =
      (blockSL2 K (2 * 2) 1).range.map ρ ⊔ (blockSL2 K (2 * 2) 2).range.map ρ := by
    rw [h2, ← LinearPilot.range_blockSL_eq (by norm_num), ← Subgroup.map_sup]
    congr 1
    exact CFSG.ClassicalInvolution.WeakCT.range_blockSL3 (2 * 2) 1 (by norm_num)
  have hc : ∀ B B' : Subgroup (StatedSp 3 K), ∀ x ∈ S.fstS B, ∀ y ∈ S.sndS B', x * y = y * x :=
    fun B B' x hx y hy => mem_centralizer_iff.1 (S.sndS_le_centralizer_fstS B B' hy) x hx
  have hblk : ∀ a b : Fin (2 * 2), (a : ℕ) + 1 < b →
      ∀ x ∈ (blockSL2 K (2 * 2) a).range.map ρ, ∀ y ∈ (blockSL2 K (2 * 2) b).range.map ρ,
        x * y = y * x := by
    rintro a b hab _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    rw [LinearPilot.range_blockSL2_eq] at hx hy
    exact congrArg ρ (LinearPilot.commute_blockSpecialLinear_of_disjoint
      (disjoint_blockSL2_coords hab) hx hy).eq
  have hO1 : ∀ x ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ y ∈ pieceCore e ({2} : Finset (Fin 3)),
      x * y = y * x := fun x hx y hy => (mem_centralizer_iff.1 (hO hx) y hy).symm
  have hO2 : ∀ x ∈ pieceCore e ({2} : Finset (Fin 3)), ∀ y ∈ pieceCore e ({0} : Finset (Fin 3)),
      x * y = y * x := fun x hx y hy => (hO1 y hy x hx).symm
  have hsymm : ∀ {W U V : Subgroup G}, LinearBlockStandardPair K W U V →
      LinearBlockStandardPair K W V U := by
    rintro W U V ⟨θ, c, h1, h2, h3⟩
    exact ⟨θ, c, h1, h2, h3.symm⟩
  have hpair : ∀ (i : Fin (2 * 2)) (h : (i : ℕ) + 1 < 2 * 2), ∃ W, LinearBlockStandardPair K W
      ((blockSL2 K (2 * 2) i).range.map ρ) ((blockSL2 K (2 * 2) ⟨i + 1, h⟩).range.map ρ) := by
    intro i h
    refine ⟨(ρ.comp (blockSL3 K (2 * 2) i h)).range,
      linearBlockStandardPair_range_of_map (ker_comp_blockSL3_le_center ρ hker i h) ?_ ?_⟩
    · rw [← Subgroup.map_map, CFSG.ClassicalInvolution.WeakCT.map_B12_blockSL3]
    · rw [← Subgroup.map_map, CFSG.ClassicalInvolution.WeakCT.map_B23_blockSL3]
  obtain ⟨W₀₁, h₀₁⟩ := S.exists_pair_fstS
  obtain ⟨W₄₅, h₄₅⟩ := S.exists_pair_sndS
  rw [h1f] at h₀₁
  rw [h1s] at h₄₅
  refine ⟨K, inferInstance, inferInstance, ![S.fstS (simpleRootSL2 K 0),
    (blockSL2 K (2 * 2) 0).range.map ρ, (blockSL2 K (2 * 2) 1).range.map ρ,
    (blockSL2 K (2 * 2) 2).range.map ρ, (blockSL2 K (2 * 2) 3).range.map ρ,
    S.sndS (simpleRootSL2 K 0)], hKc, ?_, ?_, ?_⟩
  · intro j i i' hi hi'
    rcases nodeSix_fold_cases j i i' hi hi' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · exact hM0
    · rw [hM1, h1f, h1s]
      rfl
    · exact hM2
  · intro i j hij
    have hU0 : ∀ x ∈ S.fstS (simpleRootSL2 K 0), x ∈ pieceCore e ({0} : Finset (Fin 3)) :=
      fun x hx => hM0.ge (mem_sup_left hx)
    have hU5 : ∀ x ∈ S.sndS (simpleRootSL2 K 0), x ∈ pieceCore e ({0} : Finset (Fin 3)) :=
      fun x hx => hM0.ge (mem_sup_right hx)
    have hU2 : ∀ x ∈ (blockSL2 K (2 * 2) 1).range.map ρ, x ∈ pieceCore e ({2} : Finset (Fin 3)) :=
      fun x hx => hM2.ge (mem_sup_left hx)
    have hU3 : ∀ x ∈ (blockSL2 K (2 * 2) 2).range.map ρ, x ∈ pieceCore e ({2} : Finset (Fin 3)) :=
      fun x hx => hM2.ge (mem_sup_right hx)
    rcases nodeSix_lt_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun x hx y hy => hO1 x (hU0 x hx) y (hU2 y hy)
    · exact fun x hx y hy => hO1 x (hU0 x hx) y (hU3 y hy)
    · intro x hx y hy
      exact hc _ _ x hx y (h1s.ge hy)
    · exact hc _ _
    · exact hblk 0 2 (by decide)
    · exact hblk 0 3 (by decide)
    · intro x hx y hy
      exact hc _ _ x (h1f.ge hx) y hy
    · exact hblk 1 3 (by decide)
    · exact fun x hx y hy => hO2 x (hU2 x hx) y (hU5 y hy)
    · exact fun x hx y hy => hO2 x (hU3 x hx) y (hU5 y hy)
  · intro i j hij
    rcases nodeSix_succ_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact ⟨W₀₁, h₀₁⟩
    · exact hpair 0 (by decide)
    · exact hpair 1 (by decide)
    · exact hpair 2 (by decide)
    · exact ⟨W₄₅, hsymm h₄₅⟩

end Chain

section Ident

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem ker_comp_mulEquiv_le_center_of_le {A B E : Type*} [Group A] [Group B] [Group E]
    (φ : A ≃* B) (ψ : B →* E) (hker : ψ.ker ≤ center B) :
    (ψ.comp φ.toMonoidHom).ker ≤ center A := by
  intro x hx
  have hz : φ x ∈ center B := hker hx
  rw [mem_center_iff] at hz ⊢
  intro g
  apply φ.injective
  rw [map_mul, map_mul]
  exact hz (φ g)

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_ringEquiv_blockSpecialLinear {F : Type} [Field F] {n : ℕ} (σ : K ≃+* F)
    (I : Finset (Fin n)) :
    (blockSpecialLinear (K := K) I).map (Matrix.SpecialLinearGroup.map (σ : K →+* F)) =
      blockSpecialLinear (K := F) I := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact LinearPilot.map_ringHom_mem_blockSpecialLinear _ hx
  · intro y hy
    refine ⟨Matrix.SpecialLinearGroup.map (σ.symm : F →+* K) y,
      LinearPilot.map_ringHom_mem_blockSpecialLinear _ hy, ?_⟩
    apply Subtype.ext
    ext a b
    simp

theorem fstS_sndS_eq_chainBlocks (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (S : SiegelSwapParam e t) (ρ : SL(2 * 2 + 1, K) →* G)
    (hM1 : pieceCore e ({1} : Finset (Fin 3)) =
      (blockSL2 K (2 * 2) 0).range.map ρ ⊔ (blockSL2 K (2 * 2) 3).range.map ρ) :
    (S.fstS (simpleRootSL2 K 1) = (blockSL2 K (2 * 2) 0).range.map ρ ∧
        S.sndS (simpleRootSL2 K 1) = (blockSL2 K (2 * 2) 3).range.map ρ) ∨
      (S.fstS (simpleRootSL2 K 1) = (blockSL2 K (2 * 2) 3).range.map ρ ∧
        S.sndS (simpleRootSL2 K 1) = (blockSL2 K (2 * 2) 0).range.map ρ) := by
  set A := (blockSL2 K (2 * 2) 0).range.map ρ with hA
  set B := (blockSL2 K (2 * 2) 3).range.map ρ with hB
  have hqA : CFSG.Open.IsQuasisimple (blockSL2 K (2 * 2) 0).range := by
    rw [LinearPilot.range_blockSL2_eq]
    exact isQuasisimple_blockSpecialLinear_of_card_two (by decide) hK
  have hqB : CFSG.Open.IsQuasisimple (blockSL2 K (2 * 2) 3).range := by
    rw [LinearPilot.range_blockSL2_eq]
    exact isQuasisimple_blockSpecialLinear_of_card_two (by decide) hK
  have hnA := UnitaryPilot.dichotomy_map_of_isQuasisimple hqA ρ
  have hnB := UnitaryPilot.dichotomy_map_of_isQuasisimple hqB ρ
  have hBA : B ≤ centralizer (A : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    rw [LinearPilot.range_blockSL2_eq] at hx hy
    exact congrArg ρ (LinearPilot.commute_blockSpecialLinear_of_disjoint
      (disjoint_blockSL2_coords (a := (0 : Fin (2 * 2))) (b := 3) (by decide)) hx hy).eq
  have hM2 := S.pieceCore_eq_fstS_sup_sndS hK (j := 1) (by decide)
  have hqS := isQuasisimple_simpleRootSL2_subgroupOf hK
    (simpleRootSL2_le_siegelLevi (F := K) (j := (1 : Fin 3)) (by decide))
  obtain ⟨hperf₁, hbot₁, hnN₁⟩ := S.fstS_props hqS
  obtain ⟨hperf₂, hbot₂, hnN₂⟩ := S.flip.fstS_props hqS
  rw [S.flip_fstS] at hperf₂ hbot₂ hnN₂
  have hc₁₂ := S.sndS_le_centralizer_fstS (simpleRootSL2 K 1) (simpleRootSL2 K 1)
  have hc₂₁ : S.fstS (simpleRootSL2 K 1) ≤ centralizer (S.sndS (simpleRootSL2 K 1) : Set G) :=
    le_centralizer_iff.1 hc₁₂
  have h1 := F4Pilot.eq_or_eq_of_perfect_of_le_sup hBA hnA hnB hperf₁ hbot₁ hnN₁
    (by rw [← hM1, hM2]; exact le_sup_left)
    (by rw [← hM1, hM2]
        exact sup_le le_normalizer (hc₁₂.trans (centralizer_le_normalizer _)))
  have h2 := F4Pilot.eq_or_eq_of_perfect_of_le_sup hBA hnA hnB hperf₂ hbot₂ hnN₂
    (by rw [← hM1, hM2]; exact le_sup_right)
    (by rw [← hM1, hM2]
        exact sup_le (hc₂₁.trans (centralizer_le_normalizer _)) le_normalizer)
  have hne : S.fstS (simpleRootSL2 K 1) ≠ S.sndS (simpleRootSL2 K 1) := by
    intro h
    have hab : S.fstS (simpleRootSL2 K 1) ≤ centralizer (S.fstS (simpleRootSL2 K 1) : Set G) := by
      calc S.fstS (simpleRootSL2 K 1) = S.sndS (simpleRootSL2 K 1) := h
        _ ≤ centralizer (S.fstS (simpleRootSL2 K 1) : Set G) := hc₁₂
    exact hbot₁ (by rw [← hperf₁, commutator_eq_bot_iff_le_centralizer.2 hab])
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Ident

section Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem ker_comp_map_le_center {F : Type} [Field F] {n : ℕ} (σ : K ≃+* F)
    (Φ : SL(n, F) →* G) (hker : Φ.ker ≤ center SL(n, F)) :
    (Φ.comp (Matrix.SpecialLinearGroup.map (σ : K →+* F))).ker ≤ center SL(n, K) := by
  intro x hx
  have hz : Matrix.SpecialLinearGroup.map (σ : K →+* F) x ∈ center SL(n, F) := hker hx
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (σ : K →+* F) : SL(n, K) → _) := by
    intro a b hab
    apply Subtype.ext
    ext i j
    have h := congrArg (fun M : SL(n, F) => (M : Matrix (Fin n) (Fin n) F) i j) hab
    simpa using h
  rw [mem_center_iff] at hz ⊢
  intro g
  apply hinj
  rw [map_mul, map_mul]
  exact hz _

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_chain_blockSpecialLinear {F : Type} [Field F] (σ : K ≃+* F)
    (ε : Equiv.Perm (Fin (2 * 2 + 1)))
    (Φ : SL(2 * 2 + 1, F) →* G) (J : Finset (Fin (2 * 2 + 1))) :
    (blockSpecialLinear (K := K) J).map ((Φ.comp (Matrix.SpecialLinearGroup.map (σ : K →+* F))).comp
      (LinearPilot.reindexSpecialLinear (K := K) ε).toMonoidHom) =
      (blockSpecialLinear (K := F) (J.map ε.toEmbedding)).map Φ := by
  rw [← Subgroup.map_map, map_reindex_blockSpecialLinear, ← Subgroup.map_map,
    map_ringEquiv_blockSpecialLinear]

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_reindex_comp_blockSpecialLinear (ε : Equiv.Perm (Fin (2 * 2 + 1)))
    (ρ : SL(2 * 2 + 1, K) →* G) (J : Finset (Fin (2 * 2 + 1))) :
    (blockSpecialLinear (K := K) J).map
        (ρ.comp (LinearPilot.reindexSpecialLinear (K := K) ε).toMonoidHom) =
      (blockSpecialLinear (K := K) (J.map ε.toEmbedding)).map ρ := by
  rw [← Subgroup.map_map, map_reindex_blockSpecialLinear]

omit [Finite K] [CharP K 2] in
theorem blockSL2_range_zero :
    (blockSL2 K (2 * 2) 0).range =
      blockSpecialLinear (K := K) ({0, 1} : Finset (Fin (2 * 2 + 1))) := by
  rw [LinearPilot.range_blockSL2_eq]
  rfl

omit [Finite K] [CharP K 2] in
theorem blockSL2_range_three :
    (blockSL2 K (2 * 2) 3).range =
      blockSpecialLinear (K := K) ({3, 4} : Finset (Fin (2 * 2 + 1))) := by
  rw [LinearPilot.range_blockSL2_eq]
  rfl

theorem spLinearNodeSystem_of_oddStd
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hsplit : OddCentralSplit (siegelLevi K 3)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin 3, RootKindSp e t f k .linearOdd) (hstd : SpThreeOddStandard e)
    (hO : pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)) :
    SpLinearNodeSystem e f 6 := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨S⟩ := nonempty_siegelSwapParam_of_oddStd hcat hdet hsplit hset hKc hf e htC ht
    (hroot 2) hstd
  obtain ⟨F, _, _, _, σ, Φ, -, hrange, hker, hN1, -⟩ :=
    spThreeOddGraphNormalized_of_standard hset hKc hf e htC ht 0 (hroot 0) hstd
  set ρ : SL(2 * 2 + 1, K) →* G := (Φ.comp (Matrix.SpecialLinearGroup.map (σ : K →+* F))).comp
    (LinearPilot.reindexSpecialLinear (K := K) chainPerm).toMonoidHom with hρ
  have hkerσ : (Φ.comp (Matrix.SpecialLinearGroup.map (σ : K →+* F))).ker ≤
      center SL(2 * 2 + 1, K) :=
    ker_comp_map_le_center σ Φ hker
  have hkerρ : ρ.ker ≤ center SL(2 * 2 + 1, K) :=
    ker_comp_mulEquiv_le_center_of_le (LinearPilot.reindexSpecialLinear (K := K) chainPerm) _
      hkerσ
  have h2 : pieceCore e ({2} : Finset (Fin 3)) =
      (blockSpecialLinear (K := K) (consecutiveBlock (2 * 2 + 1) 1 3)).map ρ := by
    rw [hρ, map_chain_blockSpecialLinear, chainPerm_two_three_four,
      pieceCore_two_eq_of_oddStd hK e σ Φ hrange hker (fun x => hN1 x)]
  have hM1 : pieceCore e ({1} : Finset (Fin 3)) =
      (blockSL2 K (2 * 2) 0).range.map ρ ⊔ (blockSL2 K (2 * 2) 3).range.map ρ := by
    rw [blockSL2_range_zero, blockSL2_range_three, hρ, map_chain_blockSpecialLinear,
      map_chain_blockSpecialLinear, chainPerm_zero_one, chainPerm_three_four, ← Subgroup.map_sup,
      pieceCore_one_eq_of_oddStd hK e σ Φ hrange hker (fun x => hN1 x)]
  rcases fstS_sndS_eq_chainBlocks hK e S ρ hM1 with ⟨h1f, h1s⟩ | ⟨h1f, h1s⟩
  · exact spLinearNodeSystem_of_chain hKc hf e S ρ hkerρ h2 h1f h1s hO
  · set ρ' : SL(2 * 2 + 1, K) →* G :=
      ρ.comp (LinearPilot.reindexSpecialLinear (K := K) revPerm5).toMonoidHom with hρ'
    have hkerρ' : ρ'.ker ≤ center SL(2 * 2 + 1, K) :=
      ker_comp_mulEquiv_le_center_of_le (LinearPilot.reindexSpecialLinear (K := K) revPerm5) _
        hkerρ
    refine spLinearNodeSystem_of_chain hKc hf e S ρ' hkerρ' ?_ ?_ ?_ hO
    · rw [hρ', map_reindex_comp_blockSpecialLinear revPerm5 ρ, revPerm5_one_two_three, h2]
    · rw [h1f, blockSL2_range_three, blockSL2_range_zero, hρ',
        map_reindex_comp_blockSpecialLinear revPerm5 ρ, revPerm5_zero_one]
    · rw [h1s, blockSL2_range_three, blockSL2_range_zero, hρ',
        map_reindex_comp_blockSpecialLinear revPerm5 ρ, revPerm5_three_four]

end Std

@[expose] def SpThreeLinearOddOrthInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearOdd) → SpThreeOddStandard e →
        pieceCore e ({0} : Finset (Fin 3)) ≤
          centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)

theorem spThreeLinearOddStandardInput_of_orth
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hO : SpThreeLinearOddOrthInput) : SpThreeLinearOddStandardInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hstd
  exact spGlobalCoverType_of_nodeSystem hf (by norm_num) (Or.inr ⟨rfl, rfl⟩)
    (spLinearNodeSystem_of_oddStd hcat hdet (oddCentralSplit_siegelLevi (by norm_num)) hset hKc hf
      e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht hroot hstd
      (hO G L hset f K hKc hf e t ht hKt hroot hstd))

theorem spThreeKindCoverInput_linearOdd_of_orth
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hO : SpThreeLinearOddOrthInput) : SpThreeKindCoverInput .linearOdd :=
  spThreeKindCoverInput_linearOdd_of_clauses hcat hdet
    (spThreeLinearOddStandardInput_of_orth hcat hdet hO) spThreeLinearOddTrivialSiegelInput_holds

end CFSG.SeitzReduction.SymplecticPilot
