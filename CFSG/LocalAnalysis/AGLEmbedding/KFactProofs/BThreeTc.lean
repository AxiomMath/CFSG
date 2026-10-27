module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BThreeCoxeter
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank

public section

namespace CFSG.AGLEmbedding.BCox

open CFSG.RankThree.PartOne.CTP.Fus

variable {G : Type} [Group G]

theorem pair_cent (gs : Gens G) {m i j : Fin 11} (hij : adj i j = true) (hk : kind m i j = 1) :
    gs.t m * gs.w i j * (gs.t m)⁻¹ = gs.w i j := by
  have := gs.pair_conj hij (by rw [hk]; norm_num)
  rwa [hk, pow_one] at this

theorem isPGroup_span (D : ModuleSpec G 3) : IsPGroup 3 D.span := by
  have hEA := D.isElemAbelian_span
  exact fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hEA.2 x x.2)⟩

theorem three_le_pRank_of_gens [Finite G] (gs : Gens G) (hc : 2 < Nat.card G) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup G) :=
  (modA gs hc).n_le_pRank Nat.prime_three

theorem n_le_pRank_span [Finite G] (D : ModuleSpec G 3) : D.n ≤ Open.pRank 3 D.span :=
  le_pRank_of_pow_le_card Nat.prime_three le_rfl D.isElemAbelian_span
    (by rw [D.card_span Nat.prime_three])

theorem tcGenDatum_of_gens [Finite G] (gs : Gens G) (hc : 2 < Nat.card G) :
    TCGenDatum G 3 := by
  have hP3 : 3 ≤ Open.pRank 3 (modA gs hc).span := n_le_pRank_span (modA gs hc)
  have hn : ∀ i, 2 ≤ (mods gs hc i).n := by
    intro i
    fin_cases i
    · exact (by norm_num : 2 ≤ 3)
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  refine ⟨4, fun i => (mods gs hc i).span, (modA gs hc).span, ⋃ i, Set.range (mods gs hc i).g,
    isPGroup_span _, span_le gs hc, ?_, closure_acting gs hc, ?_⟩
  · intro i
    refine ⟨(hn i).trans (n_le_pRank_span (mods gs hc i)), ?_⟩
    have hcomm : ∀ x ∈ (modA gs hc).span, ∀ u ∈ (mods gs hc i).span, u * x = x * u := by
      intro x hx u hu
      have hEA := (modA gs hc).isElemAbelian_span.1
      exact congrArg Subtype.val
        (hEA.is_comm.comm ⟨u, span_le gs hc i hu⟩ ⟨x, hx⟩)
    have hle : (modA gs hc).span ≤
        (mods gs hc i).span ⊔ ((modA gs hc).span ⊓
          Subgroup.centralizer ((mods gs hc i).span : Set G)) := by
      refine le_trans ?_ le_sup_right
      refine le_inf le_rfl fun x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      exact fun u hu => hcomm x hx u hu
    exact hP3.trans (PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hle)
  · intro g hg
    obtain ⟨i, j, rfl⟩ := Set.mem_iUnion.1 hg
    exact ⟨i, (mods gs hc i).g_mem_normalizer j⟩

@[expose] def hn : Fin 2 → Fin 3 → Fin 11 := ![![4, 5, 10], ![2, 2, 2]]

@[expose] def pts : Fin 2 → Fin 11 × Fin 11 := ![(0, 1), (6, 7)]

theorem hn_cent :
    ∀ j i, adj (pts j).1 (pts j).2 = true ∧ kind (hn j i) (pts j).1 (pts j).2 = 1 := by
  decide

theorem coverPointDatum_of_gens (gs : Gens G) (hc : 2 < Nat.card G) :
    CoverPointDatum G 3 := by
  refine ⟨modA gs hc, 2, fun j => gs.w (pts j).1 (pts j).2, fun _ => 3,
    fun j i => gs.t (hn j i), fun _ _ => 1, Or.inl le_rfl, modA_noFun gs hc, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, gs.w_ne_one hc (hn_cent j 0).1⟩
    fin_cases j
    · exact Subgroup.subset_closure ⟨(0 : Fin 3), rfl⟩
    · exact Subgroup.subset_closure ⟨(1 : Fin 3), rfl⟩
  · intro j i
    rw [pow_one]
    exact pair_cent gs (hn_cent j i).1 (hn_cent j i).2
  · rw [eq_top_iff, ← gs.gen]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨m, rfl⟩
    fin_cases m
    · exact Or.inl ⟨(0 : Fin 7), rfl⟩
    · exact Or.inl ⟨(1 : Fin 7), rfl⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨1, (0 : Fin 3), rfl⟩)
    · exact Or.inl ⟨(2 : Fin 7), rfl⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨0, (0 : Fin 3), rfl⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨0, (1 : Fin 3), rfl⟩)
    · exact Or.inl ⟨(3 : Fin 7), rfl⟩
    · exact Or.inl ⟨(4 : Fin 7), rfl⟩
    · exact Or.inl ⟨(5 : Fin 7), rfl⟩
    · exact Or.inl ⟨(6 : Fin 7), rfl⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨0, (2 : Fin 3), rfl⟩)

theorem sporCaseThreePrimeData_of_gens [Finite G] (gs : Gens G) (hc : 2 < Nat.card G) :
    @SporCaseThreePrimeData G _ ‹_› 3 ⟨Nat.prime_three⟩ :=
  Or.inr (Or.inr ⟨fun T => Or.inl
    (@weakCoreOfTC G _ ‹_› 3 ⟨Nat.prime_three⟩ (tcGenDatum_of_gens gs hc) T),
    Or.inr (@coverWeakGen_of_coverPointDatum G _ ‹_› 3 ⟨Nat.prime_three⟩ (by norm_num)
      (coverPointDatum_of_gens gs hc))⟩)

theorem fusionGenerationOf_of_gens (gs : Gens G) (hc : 2 < Nat.card G) :
    FusionGenerationOf G 3 := by
  have hmem0 : gs.w 0 1 ∈ (modAB gs hc).span := Subgroup.subset_closure ⟨(0 : Fin 2), rfl⟩
  have hmem1 : gs.w 6 7 ∈ (modAB gs hc).span := Subgroup.subset_closure ⟨(1 : Fin 2), rfl⟩
  refine ⟨(modAB gs hc).span, Set.range gs.t, isPGroup_span _, ?_, gs.gen, ?_⟩
  · intro h
    have := h ▸ hmem0
    exact gs.w_ne_one hc (by decide : adj 0 1 = true) ((Subgroup.mem_bot).1 this)
  · rintro _ ⟨m, rfl⟩
    by_cases hm : kind m 0 1 = 0
    · have hm' : kind m 6 7 ≠ 0 := by
        revert hm
        fin_cases m <;> decide
      refine ⟨gs.w 6 7, hmem1, gs.w_ne_one hc (by decide : adj 6 7 = true), ?_⟩
      rw [gs.pair_conj (by decide : adj 6 7 = true) hm']
      exact Subgroup.pow_mem _ hmem1 _
    · refine ⟨gs.w 0 1, hmem0, gs.w_ne_one hc (by decide : adj 0 1 = true), ?_⟩
      rw [gs.pair_conj (by decide : adj 0 1 = true) hm]
      exact Subgroup.pow_mem _ hmem0 _

end CFSG.AGLEmbedding.BCox
