module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherExtremalParabolics
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup

section Group

variable {G : Type*} [Group G] {p : ℕ}

theorem map_mem_sylowNormalizers (φ : G ≃* G) {B₀ : Subgroup G}
    (h : B₀ ∈ sylowNormalizers G p) : B₀.map (φ : G →* G) ∈ sylowNormalizers G p := by
  obtain ⟨T, rfl⟩ := h
  refine ⟨(φ : MulAut G) • T, ?_⟩
  rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  exact (Subgroup.map_equiv_normalizer_eq _ φ).symm

theorem map_mem_maximalParabolics (φ : G ≃* G) {M : Subgroup G}
    (h : M ∈ maximalParabolics G p) : M.map (φ : G →* G) ∈ maximalParabolics G p := by
  obtain ⟨hM, B₀, hB₀, hle⟩ := h
  exact ⟨(OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ) M).mpr hM, _,
    map_mem_sylowNormalizers φ hB₀, map_mono hle⟩

theorem map_mem_extremalParabolics (φ : G ≃* G) {M : Subgroup G}
    (h : M ∈ extremalParabolics G p) : M.map (φ : G →* G) ∈ extremalParabolics G p := by
  obtain ⟨hM, hmin⟩ := h
  refine ⟨map_mem_maximalParabolics φ hM, fun M' hM' => ?_⟩
  have h1 := hmin _ (map_mem_maximalParabolics φ.symm hM')
  rw [Subgroup.index_map_equiv] at h1 ⊢
  exact h1

@[expose] def parabolicGraphAut (p : ℕ) (φ : G ≃* G) :
    parabolicGraph G p ≃g parabolicGraph G p where
  toFun M := ⟨(M : Subgroup G).map (φ : G →* G), map_mem_extremalParabolics φ M.2⟩
  invFun M := ⟨(M : Subgroup G).map (φ.symm : G →* G), map_mem_extremalParabolics φ.symm M.2⟩
  left_inv M := Subtype.ext ((MulEquiv.mapSubgroup φ).symm_apply_apply M.1)
  right_inv M := Subtype.ext ((MulEquiv.mapSubgroup φ).apply_symm_apply M.1)
  map_rel_iff' {M N} := by
    set e := MulEquiv.mapSubgroup φ with he
    change (_ ≠ _ ∧ ∃ B₀ ∈ sylowNormalizers G p, B₀ ≤ e M.1 ⊓ e N.1) ↔
      (M ≠ N ∧ ∃ B₀ ∈ sylowNormalizers G p, B₀ ≤ M.1 ⊓ N.1)
    refine and_congr ?_ ⟨?_, ?_⟩
    · refine not_congr ⟨fun h => Subtype.ext (e.injective (congrArg Subtype.val h)), fun h => ?_⟩
      rw [h]
    · rintro ⟨B₀, hB₀, hle⟩
      refine ⟨e.symm B₀, map_mem_sylowNormalizers φ.symm hB₀, ?_⟩
      rw [OrderIso.symm_apply_le, e.map_inf]
      exact hle
    · rintro ⟨B₀, hB₀, hle⟩
      refine ⟨e B₀, map_mem_sylowNormalizers φ hB₀, ?_⟩
      rw [← e.map_inf]
      exact e.monotone hle

theorem parabolicGraphAut_apply (φ : G ≃* G) (M : extremalParabolics G p) :
    ((parabolicGraphAut p φ M : extremalParabolics G p) : Subgroup G) =
      (M : Subgroup G).map (φ : G →* G) :=
  rfl

end Group

theorem preserves_or_swaps_parts {V : Type*} {Γ : SimpleGraph V} {s t : Set V}
    (hΓ : Γ.Connected) (hst : Γ.IsBipartiteWith s t) (hcov : ∀ v, v ∈ s ∨ v ∈ t) (Φ : Γ ≃g Γ) :
    ((∀ v, v ∈ s → Φ v ∈ s) ∧ ∀ v, v ∈ t → Φ v ∈ t) ∨
      ((∀ v, v ∈ s → Φ v ∈ t) ∧ ∀ v, v ∈ t → Φ v ∈ s) := by
  have hts : ∀ v, v ∈ t → v ∉ s := fun v hv hvs => Set.disjoint_left.mp hst.disjoint hvs hv
  have hcross : ∀ u w, Γ.Adj u w → (u ∈ s ↔ w ∉ s) := by
    intro u w h
    rcases hst.mem_of_adj h with ⟨hu, hw⟩ | ⟨hu, hw⟩
    · exact ⟨fun _ => hts w hw, fun _ => hu⟩
    · exact ⟨fun hus => absurd hus (hts u hu), fun h => absurd hw h⟩
  have hwalk : ∀ u v, Γ.Reachable u v → ((u ∈ s ↔ Φ u ∈ s) ↔ (v ∈ s ↔ Φ v ∈ s)) := by
    rintro u v ⟨w⟩
    induction w with
    | nil => exact Iff.rfl
    | cons h w ih =>
      rw [← ih, hcross _ _ h, hcross _ _ (Φ.map_rel_iff.mpr h), not_iff_not]
  have hΓ' := hΓ
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hΓ'
  obtain ⟨v₀, hv₀⟩ := hΓ'
  by_cases h0 : v₀ ∈ s ↔ Φ v₀ ∈ s
  · have hall : ∀ v, v ∈ s ↔ Φ v ∈ s := fun v => (hwalk v₀ v (hv₀ v)).mp h0
    refine Or.inl ⟨fun v hv => (hall v).mp hv, fun v hv => ?_⟩
    exact (hcov _).resolve_left fun h => hts v hv ((hall v).mpr h)
  · have hall : ∀ v, ¬(v ∈ s ↔ Φ v ∈ s) := fun v h => h0 ((hwalk v₀ v (hv₀ v)).mpr h)
    refine Or.inr ⟨fun v hv => (hcov _).resolve_left fun h => hall v ⟨fun _ => h, fun _ => hv⟩,
      fun v hv => ?_⟩
    by_contra h
    exact hall v ⟨fun hvs => absurd hvs (hts v hv), fun hΦ => absurd hΦ fun hΦs =>
      h ((hcov _).resolve_right fun hΦt => hts _ hΦt hΦs)⟩

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_chain_between {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    ∀ (k : ℕ) (A B : Submodule K V), A ≤ B → finrank K B = finrank K A + k →
      ∃ C : ℕ → Submodule K V, Monotone C ∧ (∀ i, A ≤ C i ∧ C i ≤ B) ∧
        ∀ i ≤ k, finrank K (C i) = finrank K A + i := by
  intro k
  induction k with
  | zero =>
    intro A B hAB _
    exact ⟨fun _ => A, monotone_const, fun _ => ⟨le_rfl, hAB⟩, fun i hi => by
      rw [Nat.le_zero.mp hi, add_zero]⟩
  | succ k ih =>
    intro A B hAB hdim
    have hlt : A < B := lt_of_le_of_ne hAB fun h => by
      rw [h] at hdim
      omega
    obtain ⟨v, hvB, hvA⟩ := IsConcreteLE.exists_of_lt hlt
    have hv0 : v ≠ 0 := fun h => hvA (h ▸ A.zero_mem)
    have hdisj : A ⊓ K ∙ v = ⊥ := ((Submodule.disjoint_span_singleton' hv0).mpr hvA).eq_bot
    have hdimA' : finrank K (A ⊔ K ∙ v : Submodule K V) = finrank K A + 1 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq A (K ∙ v)
      rw [hdisj, finrank_bot, finrank_span_singleton hv0] at this
      omega
    have hA'B : A ⊔ K ∙ v ≤ B := sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).mpr hvB)
    obtain ⟨C, hCmono, hCbd, hCdim⟩ := ih (A ⊔ K ∙ v) B hA'B (by omega)
    let C' : ℕ → Submodule K V := fun i => if i = 0 then A else C (i - 1)
    have hC'0 : C' 0 = A := ite_eq_left rfl
    have hC'succ : ∀ i, C' (i + 1) = C i := fun i => ite_eq_right (Nat.succ_ne_zero i)
    refine ⟨C', ?_, fun i => ?_, fun i hi => ?_⟩
    · refine monotone_nat_of_le_succ fun i => ?_
      rcases i with _ | i
      · rw [hC'0, hC'succ]
        exact le_sup_left.trans (hCbd 0).1
      · rw [hC'succ, hC'succ]
        exact hCmono (Nat.le_succ i)
    · rcases i with _ | i
      · rw [hC'0]
        exact ⟨le_rfl, hAB⟩
      · rw [hC'succ]
        exact ⟨le_sup_left.trans (hCbd _).1, (hCbd _).2⟩
    · rcases i with _ | i
      · rw [hC'0, add_zero]
      · rw [hC'succ, hCdim i (by omega), hdimA']
        omega

theorem exists_hyperplane_ge {A : Submodule K (Fin n → K)} (hA : finrank K A ≤ n - 1) :
    ∃ H : Submodule K (Fin n → K), A ≤ H ∧ finrank K H = n - 1 := by
  have hAn : finrank K A ≤ n := by simpa using Submodule.finrank_le A
  obtain ⟨C, -, hCbd, hCdim⟩ := exists_chain_between (n - finrank K A) A ⊤ le_top (by
    rw [finrank_top, finrank_fin_fun]
    omega)
  exact ⟨C (n - 1 - finrank K A), (hCbd _).1, by rw [hCdim _ (by omega)]; omega⟩

theorem exists_map_flagSpace_eq_of_le (hn : 2 ≤ n) {L H : Submodule K (Fin n → K)} (hLH : L ≤ H)
    (hL : finrank K L = 1) (hH : finrank K H = n - 1) :
    ∃ g : SpecialLinearGroup (Fin n) K,
      (flagSpace n K 1).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = L ∧
        (flagSpace n K (n - 1)).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = H := by
  classical
  obtain ⟨C, hCmono, hCbd, hCdim⟩ := exists_chain_between (n - 2) L H hLH (by omega)
  let V : Fin (n + 1) → Submodule K (Fin n → K) := fun i =>
    if (i : ℕ) = 0 then ⊥ else if (i : ℕ) = n then ⊤ else C ((i : ℕ) - 1)
  have hV0 : ∀ i : Fin (n + 1), (i : ℕ) = 0 → V i = ⊥ := fun _ h => ite_eq_left h
  have hVn : ∀ i : Fin (n + 1), (i : ℕ) = n → V i = ⊤ := fun _ h =>
    (ite_eq_right (by omega)).trans (ite_eq_left h)
  have hVm : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≠ n → V i = C ((i : ℕ) - 1) :=
    fun _ h0 hn' => (ite_eq_right h0).trans (ite_eq_right hn')
  have hVc : IsCompleteFlag V := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : (i : ℕ) ≤ j := hij
      have hj := j.isLt
      by_cases hi0 : (i : ℕ) = 0
      · rw [hV0 i hi0]
        exact bot_le
      by_cases hjn : (j : ℕ) = n
      · rw [hVn j hjn]
        exact le_top
      rw [hVm i hi0 (by omega), hVm j (by omega) hjn]
      exact hCmono (by omega)
    · have hi := i.isLt
      by_cases hi0 : (i : ℕ) = 0
      · rw [hV0 i hi0, finrank_bot, hi0]
      by_cases hin : (i : ℕ) = n
      · rw [hVn i hin, finrank_top, finrank_fin_fun, hin]
      rw [hVm i hi0 hin, hCdim _ (by omega), hL]
      omega
  obtain ⟨g, hg⟩ := exists_map_standardFlag_eq hVc
  have hC0 : C 0 = L :=
    (Submodule.eq_of_le_of_finrank_eq (hCbd 0).1 (by rw [hCdim 0 (Nat.zero_le _), add_zero])).symm
  have hCn : C (n - 2) = H :=
    Submodule.eq_of_le_of_finrank_eq (hCbd _).2 (by rw [hCdim _ le_rfl, hL, hH]; omega)
  refine ⟨g, ?_, ?_⟩
  · have h1 : (flagSpace n K 1).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) =
        V ⟨1, by omega⟩ := hg ⟨1, by omega⟩
    rw [h1, hVm _ one_ne_zero (show (1 : ℕ) ≠ n by omega)]
    exact hC0
  · have h2 : (flagSpace n K (n - 1)).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) =
        V ⟨n - 1, by omega⟩ := hg ⟨n - 1, by omega⟩
    rw [h2, hVm _ (show n - 1 ≠ 0 by omega) (show n - 1 ≠ n by omega)]
    change C (n - 1 - 1) = H
    rw [show n - 1 - 1 = n - 2 by omega, hCn]

theorem eq_map_flagSpace_of_le {g : SpecialLinearGroup (Fin n) K} {W : Submodule K (Fin n → K)}
    (h : (projUpperTriangular n K).map
        (MulAut.conj (proj n K g) : projectiveSL n K →* projectiveSL n K) ≤ projStabilizer W) :
    W = (flagSpace n K (finrank K W)).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) := by
  have h1 : (upperTriangular n K).map (MulAut.conj g : SpecialLinearGroup (Fin n) K →*
      SpecialLinearGroup (Fin n) K) ≤ stabilizer W := by
    rw [← comap_projStabilizer, ← Subgroup.map_le_iff_le_comap]
    refine le_trans (le_of_eq ?_) h
    rw [projUpperTriangular, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hgg : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g)
  set X := W.map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
    with hX
  have hXW : X.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W := by
    rw [hX, ← Submodule.map_comp, ← mulVecLin_mul, hgg, mulVecLin_one, Submodule.map_id]
  have hinv : ∀ u ∈ unitriangular n K, ∀ v ∈ X, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ X := by
    rintro u hu _ ⟨w, hw, rfl⟩
    have hconj : g * u * g⁻¹ ∈ stabilizer W :=
      h1 ⟨u, unitriangular_le_upperTriangular n K hu, rfl⟩
    have hmem : ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈
        W := by
      rw [← mem_stabilizer.mp hconj]
      exact ⟨w, hw, rfl⟩
    refine ⟨_, hmem, ?_⟩
    change ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((g * u * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      (u : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w)
    have hmat : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (u : Matrix (Fin n) (Fin n) K) *
          ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      congrArg Subtype.val (show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group)
    rw [mulVec_mulVec, hmat, ← mulVec_mulVec]
  obtain ⟨m, hm, hXm⟩ := eq_flagSpace_of_invariant hinv
  have hfin : finrank K X = finrank K W :=
    LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g⁻¹) W
  rw [hXm, finrank_flagSpace hm] at hfin
  rw [← hfin, ← hXm, hXW]

theorem exists_le_inf_iff [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 1 ≤ n)
    (W W' : Submodule K (Fin n → K)) :
    (∃ B₀ ∈ sylowNormalizers (projectiveSL n K) p,
        B₀ ≤ projStabilizer W ⊓ projStabilizer W') ↔
      ∃ g : SpecialLinearGroup (Fin n) K,
        W = (flagSpace n K (finrank K W)).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) ∧
          W' = (flagSpace n K (finrank K W')).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) := by
  rw [sylowNormalizers_eq p hn]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, hle⟩
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    exact ⟨g, eq_map_flagSpace_of_le (hle.trans inf_le_left),
      eq_map_flagSpace_of_le (hle.trans inf_le_right)⟩
  · rintro ⟨g, hW, hW'⟩
    refine ⟨_, ⟨proj n K g, rfl⟩, le_inf ?_ ?_⟩
    · rw [hW, ← projStabilizer_map_conj]
      exact map_mono (projUpperTriangular_le_projStabilizer _)
    · rw [hW', ← projStabilizer_map_conj]
      exact map_mono (projUpperTriangular_le_projStabilizer _)

@[expose] def pointVertices (n : ℕ) (K : Type*) [Field K] (p : ℕ) :
    Set (extremalParabolics (projectiveSL n K) p) :=
  {M | ∃ L : Submodule K (Fin n → K), finrank K L = 1 ∧
    (M : Subgroup (projectiveSL n K)) = projStabilizer L}

@[expose] def hyperplaneVertices (n : ℕ) (K : Type*) [Field K] (p : ℕ) :
    Set (extremalParabolics (projectiveSL n K) p) :=
  {M | ∃ H : Submodule K (Fin n → K), finrank K H = n - 1 ∧
    (M : Subgroup (projectiveSL n K)) = projStabilizer H}

theorem incidence_graph [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 3 ≤ n) :
    (parabolicGraph (projectiveSL n K) p).Connected ∧
    (parabolicGraph (projectiveSL n K) p).IsBipartiteWith (pointVertices n K p)
      (hyperplaneVertices n K p) ∧
    pointVertices n K p ∪ hyperplaneVertices n K p = Set.univ ∧
    (∀ M N, M ∈ pointVertices n K p → N ∈ pointVertices n K p →
      ¬(parabolicGraph (projectiveSL n K) p).Adj M N) ∧
    (∀ M N, M ∈ hyperplaneVertices n K p → N ∈ hyperplaneVertices n K p →
      ¬(parabolicGraph (projectiveSL n K) p).Adj M N) ∧
    (∀ (L H : Submodule K (Fin n → K)) (M N : extremalParabolics (projectiveSL n K) p),
      finrank K L = 1 → finrank K H = n - 1 →
      (M : Subgroup (projectiveSL n K)) = projStabilizer L →
      (N : Subgroup (projectiveSL n K)) = projStabilizer H →
      ((parabolicGraph (projectiveSL n K) p).Adj M N ↔ L ≤ H)) ∧
    ∀ φ : projectiveSL n K ≃* projectiveSL n K,
      ∃ Φ : parabolicGraph (projectiveSL n K) p ≃g parabolicGraph (projectiveSL n K) p,
        (∀ M, (Φ M : Subgroup (projectiveSL n K)) =
          (M : Subgroup (projectiveSL n K)).map (φ : projectiveSL n K →* projectiveSL n K)) ∧
        (((∀ M, M ∈ pointVertices n K p → Φ M ∈ pointVertices n K p) ∧
            ∀ M, M ∈ hyperplaneVertices n K p → Φ M ∈ hyperplaneVertices n K p) ∨
          ((∀ M, M ∈ pointVertices n K p → Φ M ∈ hyperplaneVertices n K p) ∧
            ∀ M, M ∈ hyperplaneVertices n K p → Φ M ∈ pointVertices n K p)) := by
  classical
  obtain ⟨hE, hdisjE, -, -, -⟩ := intrinsic_extremal_parabolics (K := K) p hn
  have hn1 : 1 ≤ n := by omega
  have hmemL : ∀ L : Submodule K (Fin n → K), finrank K L = 1 →
      projStabilizer L ∈ extremalParabolics (projectiveSL n K) p := fun L hL => by
    rw [hE]
    exact Or.inl ⟨L, hL, rfl⟩
  have hmemH : ∀ H : Submodule K (Fin n → K), finrank K H = n - 1 →
      projStabilizer H ∈ extremalParabolics (projectiveSL n K) p := fun H hH => by
    rw [hE]
    exact Or.inr ⟨H, hH, rfl⟩
  have hneLH : ∀ L H : Submodule K (Fin n → K), finrank K L = 1 → finrank K H = n - 1 →
      projStabilizer L ≠ projStabilizer H := fun L H hL hH h =>
    Set.disjoint_left.mp hdisjE ⟨L, hL, rfl⟩ ⟨H, hH, h.symm⟩
  have hadj : ∀ (W W' : Submodule K (Fin n → K)) (M N : extremalParabolics (projectiveSL n K) p),
      (M : Subgroup (projectiveSL n K)) = projStabilizer W →
      (N : Subgroup (projectiveSL n K)) = projStabilizer W' →
      ((parabolicGraph (projectiveSL n K) p).Adj M N ↔ M ≠ N ∧
        ∃ g : SpecialLinearGroup (Fin n) K,
          W = (flagSpace n K (finrank K W)).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) ∧
          W' = (flagSpace n K (finrank K W')).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) := by
    intro W W' M N hM hN
    rw [parabolicGraph_adj, hM, hN, exists_le_inf_iff p hn1]
  have hsame : ∀ (W W' : Submodule K (Fin n → K)) (M N : extremalParabolics (projectiveSL n K) p),
      finrank K W = finrank K W' → (M : Subgroup (projectiveSL n K)) = projStabilizer W →
      (N : Subgroup (projectiveSL n K)) = projStabilizer W' →
      ¬(parabolicGraph (projectiveSL n K) p).Adj M N := by
    intro W W' M N hd hM hN h
    obtain ⟨hne, g, hW, hW'⟩ := (hadj W W' M N hM hN).mp h
    have hWW' : W = W' := by rw [hW, hW', hd]
    exact hne (Subtype.ext (by rw [hM, hN, hWW']))
  have hpts : ∀ M N, M ∈ pointVertices n K p → N ∈ pointVertices n K p →
      ¬(parabolicGraph (projectiveSL n K) p).Adj M N := by
    rintro M N ⟨L, hL, hML⟩ ⟨L', hL', hNL'⟩
    exact hsame L L' M N (hL.trans hL'.symm) hML hNL'
  have hhyps : ∀ M N, M ∈ hyperplaneVertices n K p → N ∈ hyperplaneVertices n K p →
      ¬(parabolicGraph (projectiveSL n K) p).Adj M N := by
    rintro M N ⟨H, hH, hMH⟩ ⟨H', hH', hNH'⟩
    exact hsame H H' M N (hH.trans hH'.symm) hMH hNH'
  have hLH : ∀ (L H : Submodule K (Fin n → K)) (M N : extremalParabolics (projectiveSL n K) p),
      finrank K L = 1 → finrank K H = n - 1 →
      (M : Subgroup (projectiveSL n K)) = projStabilizer L →
      (N : Subgroup (projectiveSL n K)) = projStabilizer H →
      ((parabolicGraph (projectiveSL n K) p).Adj M N ↔ L ≤ H) := by
    intro L H M N hL hH hM hN
    rw [hadj L H M N hM hN]
    constructor
    · rintro ⟨-, g, hLg, hHg⟩
      rw [hLg, hHg, hL, hH]
      exact Submodule.map_mono (flagSpace_mono (by omega))
    · intro hle
      obtain ⟨g, hg1, hg2⟩ := exists_map_flagSpace_eq_of_le (by omega) hle hL hH
      refine ⟨fun h => hneLH L H hL hH ?_, g, ?_, ?_⟩
      · rw [← hM, ← hN, h]
      · rw [hL, hg1]
      · rw [hH, hg2]
  have hcov : ∀ M : extremalParabolics (projectiveSL n K) p,
      M ∈ pointVertices n K p ∨ M ∈ hyperplaneVertices n K p := by
    intro M
    have hM : (M : Subgroup (projectiveSL n K)) ∈
        projStabilizer '' {L : Submodule K (Fin n → K) | finrank K L = 1} ∪
          projStabilizer '' {H : Submodule K (Fin n → K) | finrank K H = n - 1} := by
      rw [← hE]
      exact M.2
    rcases hM with ⟨L, hL, hML⟩ | ⟨H, hH, hMH⟩
    · exact Or.inl ⟨L, hL, hML.symm⟩
    · exact Or.inr ⟨H, hH, hMH.symm⟩
  have hdisj : Disjoint (pointVertices n K p) (hyperplaneVertices n K p) :=
    Set.disjoint_left.mpr fun M ⟨L, hL, hML⟩ ⟨H, hH, hMH⟩ =>
      hneLH L H hL hH (hML.symm.trans hMH)
  have hbip : (parabolicGraph (projectiveSL n K) p).IsBipartiteWith (pointVertices n K p)
      (hyperplaneVertices n K p) := by
    refine ⟨hdisj, fun M N h => ?_⟩
    rcases hcov M with hM | hM <;> rcases hcov N with hN | hN
    · exact absurd h (hpts M N hM hN)
    · exact Or.inl ⟨hM, hN⟩
    · exact Or.inr ⟨hM, hN⟩
    · exact absurd h (hhyps M N hM hN)
  have hF1 : finrank K (flagSpace n K 1) = 1 := finrank_flagSpace (by omega)
  have hconn : (parabolicGraph (projectiveSL n K) p).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    set v₀ : extremalParabolics (projectiveSL n K) p := ⟨_, hmemL _ hF1⟩ with hv₀
    have hpt : ∀ (L : Submodule K (Fin n → K)) (hL : finrank K L = 1),
        (parabolicGraph (projectiveSL n K) p).Reachable v₀ ⟨_, hmemL L hL⟩ := by
      intro L hL
      by_cases hLF : L = flagSpace n K 1
      · have hv : (⟨_, hmemL L hL⟩ : extremalParabolics (projectiveSL n K) p) = v₀ :=
          Subtype.ext (show projStabilizer L = projStabilizer (flagSpace n K 1) by rw [hLF])
        rw [hv]
      · have hdim : finrank K (L ⊔ flagSpace n K 1 : Submodule K (Fin n → K)) ≤ n - 1 := by
          have := Submodule.finrank_add_le_finrank_add_finrank L (flagSpace n K 1)
          rw [hL, hF1] at this
          omega
        obtain ⟨H, hAH, hH⟩ := exists_hyperplane_ge hdim
        have h1 : (parabolicGraph (projectiveSL n K) p).Adj v₀ ⟨_, hmemH H hH⟩ :=
          (hLH _ _ _ _ hF1 hH rfl rfl).mpr (le_sup_right.trans hAH)
        have h2 : (parabolicGraph (projectiveSL n K) p).Adj ⟨_, hmemL L hL⟩ ⟨_, hmemH H hH⟩ :=
          (hLH _ _ _ _ hL hH rfl rfl).mpr (le_sup_left.trans hAH)
        exact h1.reachable.trans h2.symm.reachable
    refine ⟨v₀, fun M => ?_⟩
    rcases hcov M with ⟨L, hL, hML⟩ | ⟨H, hH, hMH⟩
    · have hv : M = ⟨_, hmemL L hL⟩ := Subtype.ext hML
      rw [hv]
      exact hpt L hL
    · have hH0 : H ≠ ⊥ := fun h => by
        rw [h, finrank_bot] at hH
        omega
      obtain ⟨v, hvH, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH0
      have hLv : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
      have hadj' : (parabolicGraph (projectiveSL n K) p).Adj ⟨_, hmemL _ hLv⟩ M :=
        (hLH _ _ _ _ hLv hH rfl hMH).mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hvH)
      exact (hpt _ hLv).trans hadj'.reachable
  exact ⟨hconn, hbip, Set.eq_univ_of_forall hcov, hpts, hhyps, hLH,
    fun φ => ⟨parabolicGraphAut p φ, fun M => rfl,
      preserves_or_swaps_parts hconn hbip hcov _⟩⟩

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
