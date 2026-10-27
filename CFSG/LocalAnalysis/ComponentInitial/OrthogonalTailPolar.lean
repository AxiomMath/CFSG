module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (finrank_span_image_lt)

variable {K : Type*} [Field K]

section TwoForms

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

variable (Q₁) in
@[expose] def IsInfOfMax : Prop :=
  ∀ W : Submodule K V₁, (∀ v ∈ W, Q₁ v = 0) →
    ∃ M₁ M₂, IsMaxSing Q₁ M₁ ∧ IsMaxSing Q₁ M₂ ∧ W = M₁ ⊓ M₂

@[expose] noncomputable def polarImage₂ (φ : Points Q₁ ≃ Points Q₂) (W : Submodule K V₁) :
    Submodule K V₂ :=
  ptSpan Q₂ (φ '' ptsIn Q₁ W)

theorem ptsIn_eq_singleton {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (L : Points Q) : ptsIn Q L.val = {L} := by
  ext M
  simp only [ptsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  have : FiniteDimensional K L.val := Module.finite_of_finrank_pos (by rw [L.2.1]; exact one_pos)
  refine ⟨fun hM => Subtype.ext (Submodule.eq_of_le_of_finrank_eq hM ?_), fun h => h ▸ le_rfl⟩
  rw [M.2.1, L.2.1]

theorem polarImage₂_point (φ : Points Q₁ ≃ Points Q₂) (L : Points Q₁) :
    polarImage₂ φ L.val = (φ L).val := by
  rw [polarImage₂, ptsIn_eq_singleton, Set.image_singleton]
  exact le_antisymm (ptSpan_le_iff.2 fun M hM => by rw [Set.mem_singleton_iff.1 hM])
    (le_ptSpan (Set.mem_singleton _))

theorem polarImage₂_bot (φ : Points Q₁ ≃ Points Q₂) : polarImage₂ φ ⊥ = ⊥ := by
  rw [polarImage₂, ptsIn_bot, Set.image_empty, ptSpan_empty]

theorem eq_polarImage₂ (φ : Points Q₁ ≃ Points Q₂) {W : Submodule K V₁} {W' : Submodule K V₂}
    (hW' : ∀ v ∈ W', Q₂ v = 0) (h : φ '' ptsIn Q₁ W = ptsIn Q₂ W') : W' = polarImage₂ φ W := by
  rw [polarImage₂, h, ptSpan_ptsIn hW']

variable (φ : Points Q₁ ≃ Points Q₂)
  (hφ : ∀ L M : Points Q₁, PolarOrtho Q₁ L.val M.val ↔ PolarOrtho Q₂ (φ L).val (φ M).val)
include hφ

theorem isMaxClique_image₂ {S : Set (Points Q₁)} (hS : IsMaxClique Q₁ S) :
    IsMaxClique Q₂ (φ '' S) := by
  refine ⟨?_, fun L hL => ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact (hφ A B).1 (hS.1 A hA B hB)
  · refine ⟨φ.symm L, hS.2 _ fun M hM => ?_, φ.apply_symm_apply L⟩
    rw [hφ, φ.apply_symm_apply]
    exact hL _ ⟨M, hM, rfl⟩

theorem polarOrtho_symm_iff₂ (L M : Points Q₂) :
    PolarOrtho Q₂ L.val M.val ↔ PolarOrtho Q₁ (φ.symm L).val (φ.symm M).val := by
  rw [hφ (φ.symm L) (φ.symm M), φ.apply_symm_apply, φ.apply_symm_apply]

theorem ptsIn_ptSpan_image_of_eq_inf₂ {W M₁ M₂ : Submodule K V₁} (h1 : IsMaxSing Q₁ M₁)
    (h2 : IsMaxSing Q₁ M₂) (hW : W = M₁ ⊓ M₂) :
    ptsIn Q₂ (ptSpan Q₂ (φ '' ptsIn Q₁ W)) = φ '' ptsIn Q₁ W := by
  obtain ⟨-, hp₁⟩ := isMaxSing_ptSpan (isMaxClique_image₂ φ hφ (isMaxClique_ptsIn h1))
  obtain ⟨-, hp₂⟩ := isMaxSing_ptSpan (isMaxClique_image₂ φ hφ (isMaxClique_ptsIn h2))
  have hptsW : ptsIn Q₁ W = ptsIn Q₁ M₁ ∩ ptsIn Q₁ M₂ := by
    ext L
    simp only [ptsIn, Set.mem_inter_iff, Set.mem_ofPred_eq, hW, le_inf_iff]
  refine Set.Subset.antisymm (fun L hL => ?_) fun L hL => le_ptSpan hL
  have hL1 : L ∈ ptsIn Q₂ (ptSpan Q₂ (φ '' ptsIn Q₁ M₁)) :=
    le_trans hL (ptSpan_mono (Set.image_mono (by rw [hptsW]; exact Set.inter_subset_left)))
  have hL2 : L ∈ ptsIn Q₂ (ptSpan Q₂ (φ '' ptsIn Q₁ M₂)) :=
    le_trans hL (ptSpan_mono (Set.image_mono (by rw [hptsW]; exact Set.inter_subset_right)))
  rw [hp₁] at hL1
  rw [hp₂] at hL2
  rw [hptsW, Set.image_inter φ.injective]
  exact ⟨hL1, hL2⟩

theorem totSing_polarImage₂ {W : Submodule K V₁} (hW : ∀ v ∈ W, Q₁ v = 0) :
    ∀ v ∈ polarImage₂ φ W, Q₂ v = 0 :=
  totSing_ptSpan (by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact (hφ A B).1 (polarOrtho_of_le hW hA hB))

variable (h₁ : IsInfOfMax Q₁)
include h₁

theorem ptsIn_polarImage₂ {W : Submodule K V₁} (hW : ∀ v ∈ W, Q₁ v = 0) :
    ptsIn Q₂ (polarImage₂ φ W) = φ '' ptsIn Q₁ W := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hM⟩ := h₁ W hW
  exact ptsIn_ptSpan_image_of_eq_inf₂ φ hφ hM₁ hM₂ hM

theorem polarImage₂_symm_polarImage₂ {W : Submodule K V₁} (hW : ∀ v ∈ W, Q₁ v = 0) :
    polarImage₂ φ.symm (polarImage₂ φ W) = W := by
  rw [polarImage₂, ptsIn_polarImage₂ φ hφ h₁ hW, Equiv.symm_image_image, ptSpan_ptsIn hW]

theorem polarImage₂_le_iff {W₁ W₂ : Submodule K V₁} (hW₁ : ∀ v ∈ W₁, Q₁ v = 0)
    (hW₂ : ∀ v ∈ W₂, Q₁ v = 0) : polarImage₂ φ W₁ ≤ polarImage₂ φ W₂ ↔ W₁ ≤ W₂ := by
  refine ⟨fun h => ?_, fun h => ptSpan_mono (Set.image_mono (ptsIn_mono h))⟩
  have hs := ptsIn_mono (Q := Q₂) h
  rw [ptsIn_polarImage₂ φ hφ h₁ hW₁, ptsIn_polarImage₂ φ hφ h₁ hW₂,
    Set.image_subset_image_iff φ.injective] at hs
  rw [← ptSpan_ptsIn hW₁, ← ptSpan_ptsIn hW₂]
  exact ptSpan_mono hs

theorem polarImage₂_injective {W₁ W₂ : Submodule K V₁} (hW₁ : ∀ v ∈ W₁, Q₁ v = 0)
    (hW₂ : ∀ v ∈ W₂, Q₁ v = 0) (h : polarImage₂ φ W₁ = polarImage₂ φ W₂) : W₁ = W₂ :=
  le_antisymm ((polarImage₂_le_iff φ hφ h₁ hW₁ hW₂).1 h.le)
    ((polarImage₂_le_iff φ hφ h₁ hW₂ hW₁).1 h.ge)

theorem finrank_le_finrank_polarImage₂ [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {W : Submodule K V₁} (hW : ∀ v ∈ W, Q₁ v = 0) :
    finrank K W ≤ finrank K (polarImage₂ φ W) := by
  set k := finrank K W with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0]
    exact Nat.zero_le _
  obtain ⟨F, ⟨hFd, hFm, hFs⟩, hFW⟩ := exists_mem_singularFlags_eq (k := k) ⟨hk.symm, hW⟩ hk0
  have hchain : ∀ i (hi : i < k), i + 1 ≤ finrank K (polarImage₂ φ (F ⟨i, hi⟩)) := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [Nat.zero_add, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro h0
      rw [← polarImage₂_bot φ] at h0
      have := polarImage₂_injective φ hφ h₁ (hFs _)
        (fun v hv => by rw [(mem_bot K).1 hv, QuadraticMap.map_zero]) h0
      have hd := hFd ⟨0, hi⟩
      rw [this, finrank_bot] at hd
      simp at hd
    | succ i ih =>
      intro hi
      have hlt : F ⟨i, by omega⟩ < F ⟨i + 1, hi⟩ := by
        refine lt_of_le_of_ne (hFm (Fin.le_def.2 (by simp only; omega))) fun he => ?_
        have h1 := hFd ⟨i, by omega⟩
        rw [he, hFd ⟨i + 1, hi⟩] at h1
        simp at h1
      have hlt' : polarImage₂ φ (F ⟨i, by omega⟩) < polarImage₂ φ (F ⟨i + 1, hi⟩) :=
        lt_of_le_of_ne ((polarImage₂_le_iff φ hφ h₁ (hFs _) (hFs _)).2 hlt.le) fun he =>
          hlt.ne (polarImage₂_injective φ hφ h₁ (hFs _) (hFs _) he)
      have := Submodule.finrank_lt_finrank_of_lt hlt'
      have := ih (by omega)
      omega
  have := hchain (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega, hFW] at this
  exact this

theorem finrank_polarImage₂ [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    (h₂ : IsInfOfMax Q₂) {W : Submodule K V₁} (hW : ∀ v ∈ W, Q₁ v = 0) :
    finrank K (polarImage₂ φ W) = finrank K W := by
  refine le_antisymm ?_ (finrank_le_finrank_polarImage₂ φ hφ h₁ hW)
  have h := finrank_le_finrank_polarImage₂ φ.symm (polarOrtho_symm_iff₂ φ hφ) h₂
    (totSing_polarImage₂ φ hφ hW)
  rwa [polarImage₂_symm_polarImage₂ φ hφ h₁ hW] at h

end TwoForms

section Tail

variable {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ}
  {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
include hani hreg

omit hreg in
theorem isMaxSing_of_finrank_eq {M : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hM : ∀ v ∈ M, quadTail r qA v = 0) (hMr : finrank K M = r) : IsMaxSing (quadTail r qA) M :=
  ⟨hM, fun W' hle hW' => (Submodule.eq_of_le_of_finrank_le hle
    (by rw [hMr]; exact finrank_le_of_totSing_tail hani hW')).symm⟩

theorem isInfOfMax_quadTail : IsInfOfMax (quadTail r qA) := by
  intro W hW
  set k := finrank K W with hkdef
  have hk : k ≤ r := finrank_le_of_totSing_tail hani hW
  set u := Module.finBasis K W
  set Wf : ℕ → Submodule K ((Fin r ⊕ Fin r → K) × A) :=
    fun i => span K ((fun j : Fin k => (u j : (Fin r ⊕ Fin r → K) × A)) '' {j | (j : ℕ) < i})
    with hWf
  have hli : LinearIndependent K (fun j : Fin k => (u j : (Fin r ⊕ Fin r → K) × A)) :=
    u.linearIndependent.map' W.subtype (ker_subtype W)
  have hWd : ∀ i ≤ k, finrank K (Wf i) = i := fun i hi => finrank_span_image_lt hli hi
  have hWm : ∀ i < k, Wf i ≤ Wf (i + 1) := fun i _ =>
    span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  have hWt : Wf k ≤ W := span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact (u j).2)
  obtain ⟨P, hPo, -, -, -, -, hPW⟩ := exists_tail_pairs_of_flag hani hreg hk hWd hWm
    (fun x hx => hW x (hWt hx))
  have hWk : W = span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < k}) := by
    rw [← hPW k le_rfl]
    exact (eq_of_le_of_finrank_eq hWt (by rw [hWd k le_rfl])).symm
  obtain ⟨hef, hfe, hee, hff⟩ := polar_pairs hPo
  have hli2 := linearIndependent_pairs hPo
  set g : Fin r → (Fin r ⊕ Fin r → K) × A := fun j => if (j : ℕ) < k then (P j).e else (P j).f
    with hg
  have hgQ : ∀ j, quadTail r qA (g j) = 0 := fun j => by
    simp only [hg]
    split_ifs
    · exact (P j).Q_e
    · exact (P j).Q_f
  have hgB : ∀ i j, polar (quadTail r qA) (g i) (g j) = 0 := fun i j => by
    simp only [hg]
    split_ifs with hi hj hj
    · exact hee i j
    · rw [hef]
      exact ite_eq_right (by rintro rfl; exact hj hi)
    · rw [hfe]
      exact ite_eq_right (by rintro rfl; exact hi hj)
    · exact hff i j
  have hgli : LinearIndependent K g := by
    have : g = (Sum.elim (fun i => (P i).e) (fun i => (P i).f)) ∘
        fun j : Fin r => if (j : ℕ) < k then Sum.inl j else Sum.inr j := by
      funext j
      simp only [hg, Function.comp_apply]
      split_ifs <;> rfl
    rw [this]
    refine hli2.comp _ fun i j hij => ?_
    split_ifs at hij <;> simpa using hij
  set M₁ := span K (Set.range fun j => (P j).e) with hM₁
  set M₂ := span K (Set.range g) with hM₂
  have hM₁s : ∀ v ∈ M₁, quadTail r qA v = 0 := fun v hv =>
    map_eq_zero_of_mem_span (by rintro _ ⟨i, rfl⟩; exact (P i).Q_e)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hee i j) hv
  have hM₂s : ∀ v ∈ M₂, quadTail r qA v = 0 := fun v hv =>
    map_eq_zero_of_mem_span (by rintro _ ⟨i, rfl⟩; exact hgQ i)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hgB i j) hv
  have hlie : LinearIndependent K fun j => (P j).e := hli2.comp Sum.inl Sum.inl_injective
  have hM₁r : finrank K M₁ = r := by
    rw [hM₁, finrank_span_eq_card hlie, Fintype.card_fin]
  have hM₂r : finrank K M₂ = r := by
    rw [hM₂, finrank_span_eq_card hgli, Fintype.card_fin]
  refine ⟨M₁, M₂, isMaxSing_of_finrank_eq hani hM₁s hM₁r,
    isMaxSing_of_finrank_eq hani hM₂s hM₂r, le_antisymm ?_ ?_⟩
  · rw [hWk]
    refine span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨subset_span ⟨j, rfl⟩, subset_span ⟨j, ?_⟩⟩
    simp only [hg, ite_eq_left (show (j : ℕ) < k from hj)]
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx₂
    have hc : ∀ i : Fin r, ¬(i : ℕ) < k → c i = 0 := by
      intro i hi
      have h0 : polar (quadTail r qA) (∑ j, c j • g j) (P i).e = 0 :=
        polar_eq_zero_of_mem_span_left (by rintro _ ⟨j, rfl⟩; exact hee j i) hx₁
      rw [polar_sum_smul_left, Finset.sum_eq_single i] at h0
      · rw [hg] at h0
        simpa [hi, hfe] using h0
      · intro j _ hji
        simp only [hg]
        split_ifs
        · rw [hee, mul_zero]
        · rw [hfe, ite_eq_right hji, mul_zero]
      · simp
    rw [hWk]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · simp only [hg, ite_eq_left hj]
      exact smul_mem _ _ (subset_span ⟨j, hj, rfl⟩)
    · rw [hc j hj, zero_smul]
      exact zero_mem _

end Tail

theorem orthogonal_geometry_tail_polar_subspaces {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {q₁ q₂ : QuadraticForm K A}
    (hani₁ : q₁.Anisotropic) (hreg₁ : (polarBilin q₁).Nondegenerate)
    (hani₂ : q₂.Anisotropic) (hreg₂ : (polarBilin q₂).Nondegenerate)
    (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val) :
    (∀ W : Submodule K ((Fin r ⊕ Fin r → K) × A), (∀ v ∈ W, quadTail r q₁ v = 0) →
      (∀ v ∈ polarImage₂ φ W, quadTail r q₂ v = 0) ∧
      φ '' ptsIn (quadTail r q₁) W = ptsIn (quadTail r q₂) (polarImage₂ φ W) ∧
      ∀ W' : Submodule K ((Fin r ⊕ Fin r → K) × A), (∀ v ∈ W', quadTail r q₂ v = 0) →
        φ '' ptsIn (quadTail r q₁) W = ptsIn (quadTail r q₂) W' → W' = polarImage₂ φ W) ∧
    (∀ W : Submodule K ((Fin r ⊕ Fin r → K) × A), (∀ v ∈ W, quadTail r q₁ v = 0) →
      finrank K (polarImage₂ φ W) = finrank K W) ∧
    (∀ W₁ W₂ : Submodule K ((Fin r ⊕ Fin r → K) × A), (∀ v ∈ W₁, quadTail r q₁ v = 0) →
      (∀ v ∈ W₂, quadTail r q₁ v = 0) → (W₁ ≤ W₂ ↔ polarImage₂ φ W₁ ≤ polarImage₂ φ W₂)) ∧
    ∀ W : Submodule K ((Fin r ⊕ Fin r → K) × A), IsMaxSing (quadTail r q₁) W →
      (∀ L : Points (quadTail r q₁), L.val ≤ W ↔ (φ L).val ≤ polarImage₂ φ W) ∧
      (∀ H : Submodule K ((Fin r ⊕ Fin r → K) × A), H ≤ W → finrank K H + 1 = finrank K W →
        polarImage₂ φ H ≤ polarImage₂ φ W ∧
          finrank K (polarImage₂ φ H) + 1 = finrank K (polarImage₂ φ W) ∧
          ∀ L : Points (quadTail r q₁), (L.val ≤ H ↔ (φ L).val ≤ polarImage₂ φ H)) ∧
      ∀ H' : Submodule K ((Fin r ⊕ Fin r → K) × A), H' ≤ polarImage₂ φ W →
        finrank K H' + 1 = finrank K (polarImage₂ φ W) →
        ∃ H : Submodule K ((Fin r ⊕ Fin r → K) × A), H ≤ W ∧ finrank K H + 1 = finrank K W ∧
          polarImage₂ φ H = H' := by
  have h₁ := isInfOfMax_quadTail (r := r) hani₁ hreg₁
  have h₂ := isInfOfMax_quadTail (r := r) hani₂ hreg₂
  refine ⟨fun W hW => ⟨totSing_polarImage₂ φ hφ hW, (ptsIn_polarImage₂ φ hφ h₁ hW).symm,
    fun W' hW' h => eq_polarImage₂ φ hW' h⟩, fun W hW => finrank_polarImage₂ φ hφ h₁ h₂ hW,
    fun W₁ W₂ hW₁ hW₂ => (polarImage₂_le_iff φ hφ h₁ hW₁ hW₂).symm, fun W hW => ⟨?_, ?_, ?_⟩⟩
  · intro L
    rw [← polarImage₂_point φ L]
    exact (polarImage₂_le_iff φ hφ h₁ L.2.2 hW.1).symm
  · intro H hH hd
    have hHs : ∀ v ∈ H, quadTail r q₁ v = 0 := fun v hv => hW.1 v (hH hv)
    refine ⟨(polarImage₂_le_iff φ hφ h₁ hHs hW.1).2 hH, by
      rw [finrank_polarImage₂ φ hφ h₁ h₂ hHs, finrank_polarImage₂ φ hφ h₁ h₂ hW.1, hd],
      fun L => ?_⟩
    rw [← polarImage₂_point φ L]
    exact (polarImage₂_le_iff φ hφ h₁ L.2.2 hHs).symm
  · intro H' hH' hd
    have hWs := totSing_polarImage₂ φ hφ hW.1
    have hHs : ∀ v ∈ H', quadTail r q₂ v = 0 := fun v hv => hWs v (hH' hv)
    have hφ' := polarOrtho_symm_iff₂ φ hφ
    set H := polarImage₂ φ.symm H' with hHdef
    have hHs' := totSing_polarImage₂ φ.symm hφ' hHs
    have hHH : polarImage₂ φ H = H' := by
      have := polarImage₂_symm_polarImage₂ φ.symm hφ' h₂ hHs
      rwa [Equiv.symm_symm] at this
    refine ⟨H, ?_, ?_, hHH⟩
    · rw [← polarImage₂_le_iff φ hφ h₁ hHs' hW.1, hHH]
      exact hH'
    · rw [← finrank_polarImage₂ φ hφ h₁ h₂ hHs', hHH, hd, finrank_polarImage₂ φ hφ h₁ h₂ hW.1]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
