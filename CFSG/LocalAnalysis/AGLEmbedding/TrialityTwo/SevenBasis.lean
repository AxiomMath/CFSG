module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenLine

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.LocalAnalysis.ComponentInitial (polar_sum_smul_left polar_sum_smul_right)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Hyperbolic

variable {r : ℕ} {b : Fin r ⊕ Fin r → V}
  (hlr : ∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0)
  (hll : ∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0)
  (hrr : ∀ i j, polar Q (b (.inr i)) (b (.inr j)) = 0)
include hlr hll hrr

omit hll in
theorem polar_sum_inr (x : Fin r ⊕ Fin r → K) (j : Fin r) :
    polar Q (∑ k, x k • b k) (b (.inr j)) = x (.inl j) := by
  rw [Fintype.sum_sum_type, polar_add_left, polar_sum_smul_left, polar_sum_smul_left]
  simp [hlr, hrr]

omit hrr in
theorem polar_sum_inl (x : Fin r ⊕ Fin r → K) (j : Fin r) :
    polar Q (∑ k, x k • b k) (b (.inl j)) = x (.inr j) := by
  rw [Fintype.sum_sum_type, polar_add_left, polar_sum_smul_left, polar_sum_smul_left]
  simp [hll, polar_comm Q (b (.inr _)) (b (.inl j)), hlr]

theorem linearIndependent_of_hyp : LinearIndependent K b := by
  rw [Fintype.linearIndependent_iff]
  intro x hx
  rintro (j | j)
  · have := polar_sum_inr hlr hrr x j
    rwa [hx, polar_zero_left, eq_comm] at this
  · have := polar_sum_inl hlr hll x j
    rwa [hx, polar_zero_left, eq_comm] at this

theorem map_sum_of_hyp (hQb : ∀ k, Q (b k) = 0) (x : Fin r ⊕ Fin r → K) :
    Q (∑ k, x k • b k) = ∑ i, x (.inl i) * x (.inr i) := by
  rw [Fintype.sum_sum_type]
  have hX : Q (∑ i, x (.inl i) • b (.inl i)) = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => b (.inl i))
      (by rintro _ ⟨i, rfl⟩; exact hQb _) (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hll i j)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hY : Q (∑ i, x (.inr i) • b (.inr i)) = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => b (.inr i))
      (by rintro _ ⟨i, rfl⟩; exact hQb _) (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hrr i j)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [QuadraticMap.map_add (⇑Q), hX, hY, zero_add, zero_add, polar_sum_smul_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polar_sum_smul_left]
  simp [hlr, mul_comm]

theorem exists_basis_of_hyp [FiniteDimensional K V] (hV : finrank K V = 2 * r) :
    ∃ bb : Basis (Fin r ⊕ Fin r) K V, ⇑bb = b := by
  have hli := linearIndependent_of_hyp hlr hll hrr
  have hsp : ⊤ ≤ Submodule.span K (Set.range b) := by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin, hV]
    ring
  exact ⟨Basis.mk hli hsp, Basis.coe_mk hli hsp⟩

theorem eq_sum_of_hyp [FiniteDimensional K V] (hV : finrank K V = 2 * r) (v : V) :
    v = ∑ i, polar Q v (b (.inr i)) • b (.inl i) + ∑ i, polar Q v (b (.inl i)) • b (.inr i) := by
  obtain ⟨bb, hbb⟩ := exists_basis_of_hyp hlr hll hrr hV
  have hv := bb.sum_repr v
  rw [hbb] at hv
  have h1 : ∀ i, polar Q v (b (.inr i)) = bb.repr v (.inl i) := fun i => by
    conv_lhs => rw [← hv]
    exact polar_sum_inr hlr hrr _ i
  have h2 : ∀ i, polar Q v (b (.inl i)) = bb.repr v (.inr i) := fun i => by
    conv_lhs => rw [← hv]
    exact polar_sum_inl hlr hll _ i
  simp only [h1, h2]
  conv_lhs => rw [← hv]
  rw [Fintype.sum_sum_type]

end Hyperbolic

variable {t : Module.End K V}

structure Frame (Q : QuadraticForm K V) (t : Module.End K V) where
  b : Fin 4 ⊕ Fin 4 → V
  Q_b : ∀ k, Q (b k) = 0
  polar_lr : ∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0
  polar_ll : ∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0
  polar_rr : ∀ i j, polar Q (b (.inr i)) (b (.inr j)) = 0
  mem_U₁ : ∀ i : Fin 3, b (.inl i.castSucc) ∈ spU₁ t
  mem_U₂ : ∀ i : Fin 3, b (.inr i.castSucc) ∈ spU₂ t
  mem_C₁ : b (.inl (Fin.last 3)) ∈ fixC t
  mem_C₂ : b (.inr (Fin.last 3)) ∈ fixC t
  apply_zero : t (b (.inl 0)) = b (.inl 1)
  apply_one : t (b (.inl 1)) = b (.inl 2)

section Exists

variable [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1) (ht : t ≠ 1)
  (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8)
include hK h7 ht hQt hB hV

theorem exists_frame (hT : ∃ T : Submodule K V, finrank K T = 4 ∧ ∀ x ∈ T, Q x = 0) :
    Nonempty (Frame Q t) := by
  have h2 := two_eq_zero_of_card hK
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_spU₁ hK h7 ht hQt hB hV
  set e : Fin 3 → V := ![u, t u, t (t u)] with he
  have hli : LinearIndependent K e := linearIndependent_of_mem_spU₁ hK h7 ht hQt hB hV hu hu0
  have heU : ∀ i, e i ∈ spU₁ t := by
    intro i
    fin_cases i
    · exact hu
    · exact apply_mem_spU₁ hu
    · exact apply_mem_spU₁ (apply_mem_spU₁ hu)
  obtain ⟨g, hg⟩ := exists_dual_family hB hli
  set f : Fin 3 → V := fun j => projU₂ t (g j) with hf
  have hfU : ∀ j, f j ∈ spU₂ t := fun j => projU₂_apply_mem _
  have hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0 := by
    intro i j
    rw [hf, ← polar_projU₁_left hQt h7, (mem_spU₁_iff h7 h2).1 (heU i), hg]
  obtain ⟨w₁, hw₁, w₂, hw₂, hQ₁, hQ₂, hw⟩ := exists_hypPair_fixC hK h7 ht hQt hB hV hT
  let bl : Fin 4 → V := Fin.snoc e w₁
  let br : Fin 4 → V := Fin.snoc f w₂
  have hbl : ∀ i : Fin 3, bl i.castSucc = e i := fun i => Fin.snoc_castSucc (α := fun _ => V) ..
  have hbr : ∀ i : Fin 3, br i.castSucc = f i := fun i => Fin.snoc_castSucc (α := fun _ => V) ..
  have hbl3 : bl (Fin.last 3) = w₁ := Fin.snoc_last (α := fun _ => V) ..
  have hbr3 : br (Fin.last 3) = w₂ := Fin.snoc_last (α := fun _ => V) ..
  refine ⟨⟨Sum.elim bl br, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro (i | i)
    · induction i using Fin.lastCases with
      | last => simp only [Sum.elim_inl, hbl3]; exact hQ₁
      | cast i => simp only [Sum.elim_inl, hbl]; exact map_eq_zero_of_mem_spU₁ hQt h7 h2 (heU i)
    · induction i using Fin.lastCases with
      | last => simp only [Sum.elim_inr, hbr3]; exact hQ₂
      | cast i => simp only [Sum.elim_inr, hbr]; exact map_eq_zero_of_mem_spU₂ hQt h7 h2 (hfU i)
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Sum.elim_inl, Sum.elim_inr, hbl3, hbr3, ↓reduceIte]
        exact hw
      | cast j =>
        simp only [Sum.elim_inl, Sum.elim_inr, hbl3, hbr,
          polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 hw₁ (hfU j)]
        split_ifs with h
        · exact absurd h (Fin.castSucc_ne_last j).symm
        · rfl
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Sum.elim_inl, Sum.elim_inr, hbl, hbr3]
        rw [polar_comm, polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 hw₂ (heU i)]
        split_ifs with h
        · exact absurd h (Fin.castSucc_ne_last i)
        · rfl
      | cast j =>
        simp only [Sum.elim_inl, Sum.elim_inr, hbl, hbr, hef, Fin.castSucc_inj]
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Sum.elim_inl, hbl3]; exact polar_self_eq_zero hQ₁
      | cast j =>
        simp only [Sum.elim_inl, hbl3, hbl]
        exact polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 hw₁ (heU j)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Sum.elim_inl, hbl, hbl3]
        rw [polar_comm]
        exact polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 hw₁ (heU i)
      | cast j =>
        simp only [Sum.elim_inl, hbl]
        exact polar_eq_zero_of_mem_spU₁ hQt h7 h2 (heU i) (heU j)
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Sum.elim_inr, hbr3]; exact polar_self_eq_zero hQ₂
      | cast j =>
        simp only [Sum.elim_inr, hbr3, hbr]
        exact polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 hw₂ (hfU j)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Sum.elim_inr, hbr, hbr3]
        rw [polar_comm]
        exact polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 hw₂ (hfU i)
      | cast j =>
        simp only [Sum.elim_inr, hbr]
        exact polar_eq_zero_of_mem_spU₂ hQt h7 h2 (hfU i) (hfU j)
  · intro i
    simp only [Sum.elim_inl, hbl]
    exact heU i
  · intro i
    simp only [Sum.elim_inr, hbr]
    exact hfU i
  · simp only [Sum.elim_inl, hbl3]
    exact hw₁
  · simp only [Sum.elim_inr, hbr3]
    exact hw₂
  · show t (bl (Fin.castSucc 0)) = bl (Fin.castSucc 1)
    rw [hbl, hbl]
    rfl
  · show t (bl (Fin.castSucc 1)) = bl (Fin.castSucc 2)
    rw [hbl, hbl]
    rfl

end Exists

end CFSG.AGLEmbedding.TrialityTwo.Seven
