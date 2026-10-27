module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

namespace TwE6UniqAbs

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

theorem e6EdgeIdx_lt : ∀ p ∈ e6EdgeIdx, p.1 < 7 ∧ p.2 < 7 := by
  decide +kernel

theorem e6_edge_gram : ∀ x y : Option (Fin 6), (nodeIdx x, nodeIdx y) ∈ e6EdgeIdx →
    x ≠ y ∧ ∀ c d : Fin 2,
      iform (e6ExtVec (![x, y] c)) (e6ExtVec (![x, y] d)) = chainGram c d := by
  decide +kernel

theorem isRoot_of_mem_R6 {γ : Fin Tag.E6.rank → ℤ} (h : γ ∈ R6) :
    IsRoot Tag.E6 γ := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
  exact isRoot_toVec hl

theorem mem_R6_of_isRoot {γ : Fin Tag.E6.rank → ℤ}
    (h : IsRoot Tag.E6 γ) : γ ∈ R6 := by
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 h
  exact List.mem_map.2 ⟨l, hl, rfl⟩

theorem pair_of_size_six {zl : List ℕ} (hpair : kcPairB zl = true) {x : ℕ} (hx : x ∈ zl)
    (h6 : szF zl x = 6) :
    ∃ u v, compIdx (Tag.E6.rank + 1) (treePath e6Anc) zl x = [u, v] ∧ (u, v) ∈ e6EdgeIdx := by
  have h1 := List.all_eq_true.1 hpair x hx
  rw [h6] at h1
  revert h1
  generalize compIdx (Tag.E6.rank + 1) (treePath e6Anc) zl x = c
  rcases c with _ | ⟨u, _ | ⟨v, _ | ⟨t, c⟩⟩⟩ <;> simp

section Frames


theorem frame_of_edge {L : Type} [Field L] {x y : Option (Fin Tag.E6.rank)}
    (hxy : (nodeIdx x, nodeIdx y) ∈ e6EdgeIdx) (v : WeylGroup Tag.E6) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2) ∧
        frameRoots σ = (fun α => v • α) '' kacE6.rootsOf (Set.range ![x, y]) := by
  obtain ⟨hne, hG⟩ := e6_edge_gram x y hxy
  have hinj : Function.Injective (![x, y] : Fin 2 → Option (Fin Tag.E6.rank)) := by
    intro c d h
    fin_cases c <;> fin_cases d <;> first | rfl | exact absurd h hne | exact absurd h.symm hne
  obtain ⟨ψ, σ, hψ, hσ⟩ := exists_frame_of_path (L := L) (Or.inr (Or.inl rfl)) kacE6 hinj
    (by
      intro c d
      rw [kacE6_extRoot]
      exact hG c d)
    (fun c h => by
      have hc0 : (c : ℕ) = 0 := by omega
      have hc : c = 0 := Fin.ext hc0
      subst hc
      exact e6_frames x y hxy) v
  exact ⟨ψ, σ, hψ, fun a b hab =>
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl))
      (hψ.isRoot a b hab), hσ⟩


theorem kac_facts {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) : KacFacts a := by
  classical
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  choose xs hxs hroots hncard hrank hprop using hcl
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hne : ∀ i j, i ≠ j →
      cmpF (zlC m0 m1 m2 m3 m4 m5) (xs i) ≠ cmpF (zlC m0 m1 m2 m3 m4 m5) (xs j) := by
    intro i j hij h
    exact hij (eq_of_componentRoots_eq (by rw [hroots i, hroots j, h]))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hncard i]
    exact kc_sizes m0 m1 m2 m3 m4 m5 hsum (xs i) (hxs i)
  · intro i h2
    rw [hrank i]
    rw [hncard i] at h2
    exact kc_card2 m0 m1 m2 m3 m4 m5 hsum (xs i) (hxs i) h2
  · intro i j hij hi hj
    rw [hncard i] at hi
    rw [hncard j] at hj
    exact kc_big m0 m1 m2 m3 m4 m5 hsum (xs i) (hxs i) (xs j) (hxs j) (hne i j hij) hi hj
  · intro i j hi hj
    rw [hncard i] at hi
    rw [hncard j] at hj
    exact eq_of_componentRoots_eq (by
      rw [hroots i, hroots j,
        kc_one m0 m1 m2 m3 m4 m5 hsum (xs i) (hxs i) (xs j) (hxs j) hi hj])
  · intro i j k l hij hik hil hjk hjl hkl
    have hc : ((zlC m0 m1 m2 m3 m4 m5).map (cmpF (zlC m0 m1 m2 m3 m4 m5))).toFinset.card ≤ 3 := by
      have h := kc_count m0 m1 m2 m3 m4 m5 hsum
      unfold kcCountB at h
      exact of_decide_eq_true h
    have hmem : ∀ i, cmpF (zlC m0 m1 m2 m3 m4 m5) (xs i) ∈
        ((zlC m0 m1 m2 m3 m4 m5).map (cmpF (zlC m0 m1 m2 m3 m4 m5))).toFinset := fun i =>
      List.mem_toFinset.2 (List.mem_map.2 ⟨xs i, hxs i, rfl⟩)
    have h4 := four_le_card (hmem i) (hmem j) (hmem k) (hmem l) (hne i j hij) (hne i k hik)
      (hne i l hil) (hne j k hjk) (hne j l hjl) (hne k l hkl)
    omega
  · intro i j k hij hik hjk
    have h := kc_triple m0 m1 m2 m3 m4 m5 hsum
    unfold kcTripleB at h
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h (xs i) (hxs i))
      (xs j) (hxs j)) (xs k) (hxs k)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h1
    rw [hncard i, hncard j, hncard k]
    rcases h1 with ((h1 | h1) | h1) | ⟨⟨h1, h2⟩, h3⟩
    · exact absurd h1 (hne i j hij)
    · exact absurd h1 (hne i k hik)
    · exact absurd h1 (hne j k hjk)
    · exact ⟨h1, h2, h3⟩
  · intro i h6
    have hs6 : szF (zlC m0 m1 m2 m3 m4 m5) (xs i) = 6 := by rw [← hncard i]; exact h6
    obtain ⟨u, v, huv, hedge⟩ := pair_of_size_six (kc_pair m0 m1 m2 m3 m4 m5 hsum) (hxs i) hs6
    obtain ⟨hu, hv⟩ := e6EdgeIdx_lt _ hedge
    have hu' : u < Tag.E6.rank + 1 := hu
    have hv' : v < Tag.E6.rank + 1 := hv
    have hxy : (nodeIdx (idxNode (r := Tag.E6.rank) u), nodeIdx (idxNode (r := Tag.E6.rank) v)) ∈
        e6EdgeIdx := by
      rw [nodeIdx_idxNode hu', nodeIdx_idxNode hv']
      exact hedge
    obtain ⟨ψ, σ, hψ, hnorm, hσ⟩ := frame_of_edge (L := L) hxy w⁻¹
    refine ⟨ψ, σ, hψ, hnorm, ?_⟩
    have hcmp : (cmpF (zlC m0 m1 m2 m3 m4 m5) (xs i) : Set (Option (Fin Tag.E6.rank))) =
        Set.range ![idxNode (r := Tag.E6.rank) u, idxNode (r := Tag.E6.rank) v] := by
      unfold cmpF
      rw [huv]
      ext z
      simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hσ, hroots i, hcmp]
  · intro i h6
    have hs6 : szF (zlC m0 m1 m2 m3 m4 m5) (xs i) = 6 := by rw [← hncard i]; exact h6
    have hg := kc_glue m0 m1 m2 m3 m4 m5 hsum
    unfold kcGlueB at hg
    have hg1 := List.all_eq_true.1 hg (xs i) (hxs i)
    rw [hs6] at hg1
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at hg1
    obtain ⟨hA, hB⟩ := hg1
    refine ⟨?_, ?_⟩
    · obtain ⟨γ0, hγ0R, hγ0⟩ := List.any_eq_true.1 hA
      refine ⟨w⁻¹ • γ0, IsRoot.smul (isRoot_of_mem_R6 hγ0R) w⁻¹, ?_⟩
      rw [hchar, smul_inv_smul]
      intro h1
      have h2 := (hζu.zpow_eq_one_iff_dvd _).1 h1
      simp only [bne_iff_ne, ne_eq] at hγ0
      omega
    · intro γ γ' hγ hγ' hform
      have hγ0R : w • γ ∈ R6 := mem_R6_of_isRoot (IsRoot.smul hγ w)
      have hγ0'R : w • γ' ∈ R6 := mem_R6_of_isRoot (IsRoot.smul hγ' w)
      have hB1 := List.all_eq_true.1 (List.all_eq_true.1 hB (w • γ) hγ0R) (w • γ') hγ0'R
      have key : ∀ δ : Fin Tag.E6.rank → ℤ, ∀ g : Fin Tag.E6.rank → ℤ,
          iform (w • g) δ = iform g (w⁻¹ • δ) := fun δ g => by
        conv_lhs => rw [← smul_inv_smul w δ]
        exact iform_smul w g (w⁻¹ • δ)
      have hall : ((R6.filter fun δ => decide (kacTest θ6
          (cmpF (zlC m0 m1 m2 m3 m4 m5) (xs i)) δ)).all fun δ =>
            iform (w • γ) δ == iform (w • γ') δ) = true := by
        rw [List.all_eq_true]
        intro δ hδ
        rw [List.mem_filter] at hδ
        obtain ⟨hδR, hδt⟩ := hδ
        have hδt' : kacTest θ6 (cmpF (zlC m0 m1 m2 m3 m4 m5) (xs i)) δ := of_decide_eq_true hδt
        have hδmem : δ ∈ kacE6.rootsOf
            (cmpF (zlC m0 m1 m2 m3 m4 m5) (xs i) : Set (Option (Fin Tag.E6.rank))) :=
          (mem_rootsOf_iff kacE6 facts_E6 (hprop i)).2 ⟨isRoot_of_mem_R6 hδR, hδt'⟩
        have hδc : w⁻¹ • δ ∈ componentRoots (rootCharHom a) i := by
          rw [hroots i]
          exact ⟨δ, hδmem, rfl⟩
        rw [beq_iff_eq, key, key]
        exact hform _ hδc
      simp only [hall, Bool.not_true, Bool.false_or, beq_iff_eq] at hB1
      rw [hchar γ, hchar γ']
      have hdvd : ((3 : ℕ) : ℤ) ∣ dotμ (w • γ) ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ)
          ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ) -
          dotμ (w • γ') ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ)
            ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ) := by omega
      have h1 := (hζu.zpow_eq_one_iff_dvd _).2 hdvd
      rw [zpow_sub, mul_inv_eq_one] at h1
      exact h1

end Frames

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
