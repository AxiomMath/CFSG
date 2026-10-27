module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoIncidence
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSuborbit

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Module Submodule CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open LinearMap (BilinForm)

variable {K : Type} [Field K]

theorem isTotallyIsotropic_sup {r : ℕ} {L M : SpPoint r K} (h : SpOrth L M) :
    IsTotallyIsotropic (pairedSympForm K r) (L.line ⊔ M.line) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  simp only [map_add, LinearMap.add_apply]
  rw [spOrth_self L a ha c hc, h a ha d hd, spOrth_comm.mp h b hb c hc, spOrth_self M b hb d hd]
  simp

theorem finrank_sup_of_ne {r : ℕ} {L M : SpPoint r K} (h : L ≠ M) :
    finrank K ↥(L.line ⊔ M.line) = 2 := by
  have hinf : L.line ⊓ M.line = ⊥ := by
    by_contra hne
    have h1 : finrank K ↥(L.line ⊓ M.line) = 1 := by
      have hle : finrank K ↥(L.line ⊓ M.line) ≤ 1 :=
        L.finrank_line ▸ Submodule.finrank_mono inf_le_left
      have hpos := one_le_finrank_of_ne_bot hne
      omega
    apply h
    apply SpPoint.ext
    have e1 : L.line ⊓ M.line = L.line :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (h1.trans L.finrank_line.symm)
    have e2 : L.line ⊓ M.line = M.line :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (h1.trans M.finrank_line.symm)
    rw [← e1, e2]
  have := Submodule.finrank_sup_add_finrank_inf_eq L.line M.line
  rw [hinf, finrank_bot, L.finrank_line, M.finrank_line] at this
  omega

theorem exists_spOrth_spOrth (L M : SpPoint 2 K) : ∃ N : SpPoint 2 K, SpOrth L N ∧ SpOrth M N := by
  set U := (pairedSympForm K 2).orthogonal (L.line ⊔ M.line)
  have hU : 0 < finrank K U := by
    have h := BilinForm.finrank_add_finrank_orthogonal SymplecticFlag.pairedSympForm_isAlt.isRefl
      (L.line ⊔ M.line)
    rw [BilinForm.orthogonal_top_eq_bot SymplecticFlag.pairedSympForm_nondegenerate, inf_bot_eq,
      finrank_bot, add_zero, finrank_standard] at h
    have h2 := Submodule.finrank_add_le_finrank_add_finrank L.line M.line
    rw [L.finrank_line, M.finrank_line] at h2
    change finrank K ↥(L.line ⊔ M.line) + finrank K U = 2 * 2 at h
    omega
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_of_finrank_pos hU)
  have hle : ∀ L' : SpPoint 2 K, L'.line ≤ L.line ⊔ M.line → SpOrth L' (SpPoint.ofVec n hn0) := by
    intro L' hL'
    rw [spOrth_iff_le_orthogonal, line_ofVec, span_le, Set.singleton_subset_iff]
    exact BilinForm.orthogonal_le hL' hn
  exact ⟨SpPoint.ofVec n hn0, hle L le_sup_left, hle M le_sup_right⟩

@[expose] def supPlane {L M : SpPoint 2 K} (h : SpOrth L M) (hne : L ≠ M) :
    isoSubspaces 2 K 2 :=
  ⟨L.line ⊔ M.line, isTotallyIsotropic_sup h, finrank_sup_of_ne hne⟩

theorem exists_line_le (W : isoSubspaces 2 K 2) : ∃ L : SpPoint 2 K, L.line ≤ W.1 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (ne_bot_of_finrank_pos (r := 2) (W := W.1) (by rw [W.2.2]; norm_num))
  exact ⟨SpPoint.ofVec w hw0, by rw [line_ofVec, span_le, Set.singleton_subset_iff]; exact hw⟩

variable [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

@[expose] def pointVertex (L : SpPoint 2 K) : spExtremalParabolics 2 K p :=
  ⟨projStabilizer 2 K L.line,
    projStabilizer_mem_spExtremalParabolics p L.line_ne_bot (isTotallyIsotropic_line L)⟩

@[expose] def planeVertex (W : isoSubspaces 2 K 2) : spExtremalParabolics 2 K p :=
  ⟨projStabilizer 2 K W.1, projStabilizer_mem_spExtremalParabolics p
    (ne_bot_of_finrank_pos (by rw [W.2.2]; norm_num)) W.2.1⟩

variable (K) in
abbrev pointVertices : Set (spExtremalParabolics 2 K p) :=
  {M | (M : Subgroup (StatedProj (StatedSp 2 K))) ∈ pointParabolics K}

variable (K) in
abbrev planeVertices : Set (spExtremalParabolics 2 K p) :=
  {M | (M : Subgroup (StatedProj (StatedSp 2 K))) ∈ planeParabolics K}

variable {p}

theorem pointVertex_adj_planeVertex {L : SpPoint 2 K} {W : isoSubspaces 2 K 2} :
    (incidenceGraph K p).Adj (pointVertex p L) (planeVertex p W) ↔ L.line ≤ W.1 :=
  adj_iff_le p L.finrank_line W.2.1 W.2.2 rfl rfl

theorem pointVertex_adj_planeVertex_of_le {L : SpPoint 2 K} {W : isoSubspaces 2 K 2}
    (h : L.line ≤ W.1) : (incidenceGraph K p).Adj (pointVertex p L) (planeVertex p W) :=
  pointVertex_adj_planeVertex.mpr h

theorem exists_eq_pointVertex {M : spExtremalParabolics 2 K p}
    (hM : (M : Subgroup (StatedProj (StatedSp 2 K))) ∈ pointParabolics K) :
    ∃ L : SpPoint 2 K, M = pointVertex p L := by
  obtain ⟨L, hL, hML⟩ := hM
  exact ⟨⟨L, hL⟩, Subtype.ext hML⟩

theorem exists_eq_planeVertex {M : spExtremalParabolics 2 K p}
    (hM : (M : Subgroup (StatedProj (StatedSp 2 K))) ∈ planeParabolics K) :
    ∃ W : isoSubspaces 2 K 2, M = planeVertex p W := by
  obtain ⟨W, hW, hW2, hMW⟩ := hM
  exact ⟨⟨W, hW, hW2⟩, Subtype.ext hMW⟩

theorem exists_walk_pointVertex (L M : SpPoint 2 K) :
    ∃ w : (incidenceGraph K p).Walk (pointVertex p L) (pointVertex p M), w.length ≤ 4 := by
  by_cases hLM : L = M
  · subst hLM
    exact ⟨.nil, by simp⟩
  by_cases horth : SpOrth L M
  · set W := supPlane horth hLM
    have h1 := pointVertex_adj_planeVertex_of_le (p := p) (L := L) (W := W) le_sup_left
    have h2 := pointVertex_adj_planeVertex_of_le (p := p) (L := M) (W := W) le_sup_right
    exact ⟨.cons h1 (.cons h2.symm .nil), by simp⟩
  obtain ⟨N, hLN, hMN⟩ := exists_spOrth_spOrth L M
  have hNL : L ≠ N := fun h => horth (by
    rw [h] at hLN ⊢
    exact spOrth_comm.mp hMN)
  have hNM : M ≠ N := fun h => horth (by rw [← h] at hLN; exact hLN)
  set W₁ := supPlane hLN hNL
  set W₂ := supPlane hMN hNM
  have h1 := pointVertex_adj_planeVertex_of_le (p := p) (L := L) (W := W₁) le_sup_left
  have h2 := pointVertex_adj_planeVertex_of_le (p := p) (L := N) (W := W₁) le_sup_right
  have h3 := pointVertex_adj_planeVertex_of_le (p := p) (L := N) (W := W₂) le_sup_right
  have h4 := pointVertex_adj_planeVertex_of_le (p := p) (L := M) (W := W₂) le_sup_left
  exact ⟨.cons h1 (.cons h2.symm (.cons h3 (.cons h4.symm .nil))), by simp⟩

variable (p)

theorem incidence_connected :
    (incidenceGraph K p).Connected ∧
    (incidenceGraph K p).IsBipartiteWith (pointVertices K p) (planeVertices K p) ∧
    pointVertices K p ∪ planeVertices K p = Set.univ ∧
    (pointVertices K p).Nonempty ∧ (planeVertices K p).Nonempty ∧
    ∀ M N : spExtremalParabolics 2 K p, M ∈ pointVertices K p → N ∈ pointVertices K p →
      ∃ w : (incidenceGraph K p).Walk M N, w.IsPath ∧ w.length ≤ 4 := by
  classical
  obtain ⟨-, hEXY, hdisj, -, -, -, -, -⟩ := extremal_parabolics (K := K) p rfl
  obtain ⟨-, hedge, -⟩ := common_normalizer_incidence (K := K) p
  set L₀ : SpPoint 2 K := ⟨flag 2 K 1, finrank_flag (by norm_num)⟩
  set W₀ : isoSubspaces 2 K 2 :=
    ⟨flag 2 K 2, isCompleteIsotropicFlag_flag.2.2 2 le_rfl, finrank_flag (by norm_num)⟩
  have hreach : ∀ M : spExtremalParabolics 2 K p,
      (incidenceGraph K p).Reachable (pointVertex p L₀) M := by
    intro M
    have hM : (M : Subgroup (StatedProj (StatedSp 2 K))) ∈ pointParabolics K ∪
        planeParabolics K := hEXY ▸ M.2
    rcases hM with hM | hM
    · obtain ⟨L, rfl⟩ := exists_eq_pointVertex hM
      obtain ⟨w, -⟩ := exists_walk_pointVertex (p := p) L₀ L
      exact ⟨w⟩
    · obtain ⟨W, rfl⟩ := exists_eq_planeVertex hM
      obtain ⟨L, hL⟩ := exists_line_le W
      obtain ⟨w, -⟩ := exists_walk_pointVertex (p := p) L₀ L
      exact ⟨w.concat (pointVertex_adj_planeVertex_of_le hL)⟩
  refine ⟨(SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨_, hreach⟩,
    ⟨Set.disjoint_left.mpr fun M hX hY => Set.disjoint_left.mp hdisj hX hY,
      fun M N hMN => hedge M N hMN⟩, ?_, ⟨pointVertex p L₀, ⟨L₀.line, L₀.finrank_line, rfl⟩⟩,
    ⟨planeVertex p W₀, ⟨W₀.1, W₀.2.1, W₀.2.2, rfl⟩⟩, fun M N hM hN => ?_⟩
  · ext M
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hM : (M : Subgroup (StatedProj (StatedSp 2 K))) ∈ pointParabolics K ∪
        planeParabolics K := hEXY ▸ M.2
    exact hM
  · obtain ⟨L, rfl⟩ := exists_eq_pointVertex hM
    obtain ⟨M', rfl⟩ := exists_eq_pointVertex hN
    obtain ⟨w, hw⟩ := exists_walk_pointVertex (p := p) L M'
    exact ⟨w.bypass, w.bypass_isPath, (w.length_bypass_le_length).trans hw⟩

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
