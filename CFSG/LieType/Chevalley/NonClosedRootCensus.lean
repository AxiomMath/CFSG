module

public import CFSG.LieType.Chevalley.RootRatClosure
public import CFSG.LieType.Chevalley.RootGramDet
public import CFSG.LieType.Chevalley.RootComponentType

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint TauCeti
open CFSG.HardMathSupport.Timmesfeld.LangTorus (compRank)

@[expose] def RootsRationallyClosed
    (τ : Tag) (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
    (fun k => (β k : ℚ)) ∈ Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) →
      β ∈ Ψ

private def DetOfRank (r : ℕ) (d : ℤ) : Prop :=
  d = r + 1 ∨ (4 ≤ r ∧ d = 4) ∨ (r = 6 ∧ d = 3) ∨ (r = 7 ∧ d = 2) ∨ (r = 8 ∧ d = 1)

private theorem detOfRank_of_isSimplyLaced {t : DynkinType} (ht : t.Valid)
    (hs : t.IsSimplyLaced) : DetOfRank t.rank t.cartanMatrix.det := by
  rcases det_cartanMatrix_of_isSimplyLaced ht hs with h | h | h | h | h
  · exact Or.inl h.2
  · exact Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [h.1]; rfl, h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [h.1]; rfl, h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [h.1]; rfl, h.2⟩)))

private theorem census_arith {r : ℕ} (hr : r ≤ 8) {d d' k : ℤ} (hd : DetOfRank r d)
    (hd' : DetOfRank r d') (h : d = k ^ 2 * d') (hk : ¬ (k = 1 ∨ k = -1)) :
    (k = 2 ∨ k = -2) ∨ (r = 8 ∧ d = 9 ∧ (k = 3 ∨ k = -3)) := by
  have hdpos : 1 ≤ d ∧ d ≤ 9 := by
    unfold DetOfRank at hd
    rcases hd with h | h | h | h | h <;> omega
  have hd'pos : 1 ≤ d' := by
    unfold DetOfRank at hd'
    rcases hd' with h | h | h | h | h <;> omega
  have hk2 : k ^ 2 ≤ 9 := by nlinarith
  have hk3 : -3 ≤ k ∧ k ≤ 3 := ⟨by nlinarith, by nlinarith⟩
  unfold DetOfRank at hd hd'
  have hcases : k = -3 ∨ k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h' : d = 9 * d' := by rw [h]; norm_num
    exact Or.inr ⟨by omega, by omega, Or.inr rfl⟩
  · exact Or.inl (Or.inr rfl)
  · exact absurd (Or.inr rfl) hk
  · have h' : d = 0 := by rw [h]; norm_num
    omega
  · exact absurd (Or.inl rfl) hk
  · exact Or.inl (Or.inl rfl)
  · have h' : d = 9 * d' := by rw [h]; norm_num
    exact Or.inr ⟨by omega, by omega, Or.inl rfl⟩

private theorem nine_arith {d k : ℤ} (hd : DetOfRank 8 d) (h : 9 = k ^ 2 * d) :
    (k = 1 ∨ k = -1) ∨ d = 1 := by
  unfold DetOfRank at hd
  have hd1 : 1 ≤ d := by rcases hd with h' | h' | h' | h' | h' <;> omega
  have hk2 : k ^ 2 ≤ 9 := by nlinarith
  have hk3 : -3 ≤ k ∧ k ≤ 3 := ⟨by nlinarith, by nlinarith⟩
  have hcases : k = -3 ∨ k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h' : (9 : ℤ) = 9 * d := by norm_num at h; linarith
    exact Or.inr (by omega)
  · have h' : (9 : ℤ) = 4 * d := by norm_num at h; linarith
    omega
  · exact Or.inl (Or.inr rfl)
  · norm_num at h
  · exact Or.inl (Or.inl rfl)
  · have h' : (9 : ℤ) = 4 * d := by norm_num at h; linarith
    omega
  · have h' : (9 : ℤ) = 9 * d := by norm_num at h; linarith
    exact Or.inr (by omega)

private theorem one_arith {d k : ℤ} (hd : 1 ≤ d) (h : 1 = k ^ 2 * d) : k = 1 ∨ k = -1 := by
  have hk2 : k ^ 2 ≤ 1 := by nlinarith
  have hk3 : -1 ≤ k ∧ k ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hcases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact Or.inr rfl
  · have h' : (1 : ℤ) = 0 := by rw [h]; norm_num
    omega
  · exact Or.inl rfl

private theorem one_le_of_detOfRank {r : ℕ} {d : ℤ} (hd : DetOfRank r d) : 1 ≤ d := by
  unfold DetOfRank at hd
  rcases hd with h | h | h | h | h <;> omega

variable {τ : Tag}

theorem rootReflection_smul_mem_of_closed (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Set (Fin τ.rank → ℤ)} (hroot : ∀ α ∈ X, IsRoot τ α) (hneg : ∀ α ∈ X, -α ∈ X)
    (hadd : ∀ α ∈ X, ∀ β ∈ X, IsRoot τ (α + β) → α + β ∈ X) {α β : Fin τ.rank → ℤ}
    (hα : α ∈ X) (hβ : β ∈ X) : rootReflection β • α ∈ X := by
  have hnorm : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ x → iform x x = 2 := fun hx => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hx
  have hαr := hroot α hα
  have hβr := hroot β hβ
  rw [rootReflection_smul hβr, corootPair_eq_iform_of_simplyLaced hτ hβr]
  have h1 := iform_self_pos_of_isRoot hαr
  have hp : ∀ x : Fin τ.rank → ℤ, x ≠ 0 → 0 < iform x x := fun x hx => iform_self_pos hx
  have hsum := fun h => hp (α + β) h
  have hdiff := fun h => hp (α - β) h
  rw [iform_add_left, iform_add_right, iform_add_right, hnorm hαr, hnorm hβr,
    iform_comm β α] at hsum
  rw [iform_sub_left, iform_sub_right, iform_sub_right, hnorm hαr, hnorm hβr,
    iform_comm β α] at hdiff
  rw [iform_comm β α]
  by_cases hab : α = β
  · subst hab
    rw [hnorm hαr]
    have : α - (2 : ℤ) • α = -α := by rw [two_smul]; abel
    rw [this]
    exact hneg α hα
  by_cases hab' : α = -β
  · subst hab'
    have hneg' : iform (-β) β = -2 := by
      rw [show -β = (-1 : ℤ) • β by simp, iform_smul_left, hnorm hβr]; norm_num
    rw [hneg']
    have : -β - (-2 : ℤ) • β = β := by rw [neg_smul, two_smul]; abel
    rw [this]
    exact hβ
  have hs := hsum fun h => hab' (eq_neg_of_add_eq_zero_left h)
  have hd := hdiff fun h => hab (sub_eq_zero.1 h)
  have hc : iform α β = 0 ∨ iform α β = 1 ∨ iform α β = -1 := by omega
  rcases hc with hc | hc | hc
  · rw [hc, zero_smul, sub_zero]
    exact hα
  · rw [hc, one_smul, sub_eq_add_neg]
    have hr := isRoot_sub_of_iform_pos hαr hβr hab (by omega)
    rw [sub_eq_add_neg] at hr
    exact hadd α hα (-β) (hneg β hβ) hr
  · rw [hc, neg_one_smul, sub_neg_eq_add]
    exact hadd α hα β hβ (isRoot_add_of_iform_neg hαr hβr hab' (by omega))

theorem isRootComponent_of_closed (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ X : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hroot : ∀ α ∈ X, IsRoot τ α)
    (hneg : ∀ α ∈ X, -α ∈ X) (hadd : ∀ α ∈ X, ∀ β ∈ X, IsRoot τ (α + β) → α + β ∈ X)
    (hΨX : Ψ ⊆ X) (hX : X ⊆ ratClosure Ψ) : IsRootComponent X where
  isRoot := hroot
  neg_mem := hneg
  add_mem := hadd
  reflection_mem _ hα _ hβ := rootReflection_smul_mem_of_closed hτ hroot hneg hadd hα hβ
  irreducible S hS hperp := irreducible_of_subset_ratClosure hΨ hΨX hX S hS hperp

theorem exists_nested_det (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hΨ' : IsRootComponent Ψ')
    (hne : Ψ.Nonempty) (hsub : Ψ ⊆ Ψ') (hcard : (simpleRoots Ψ).card = (simpleRoots Ψ').card)
    (t : DynkinType) (e : simpleRoots Ψ ≃ Fin t.rank)
    (he : ∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ)) :
    ∃ (t' : DynkinType) (e' : simpleRoots Ψ' ≃ Fin t'.rank) (k : ℤ), t'.Valid ∧
      t'.IsSimplyLaced ∧
      (∀ β γ : simpleRoots Ψ', iform (β : Fin τ.rank → ℤ) γ = t'.cartanMatrix (e' β) (e' γ)) ∧
      t'.rank = (simpleRoots Ψ').card ∧ Ψ'.ncard = t'.numRoots ∧
      t.cartanMatrix.det = k ^ 2 * t'.cartanMatrix.det ∧
      ((k = 1 ∨ k = -1) → Ψ' ⊆ Ψ) ∧ ∀ β ∈ Ψ', k • β ∈ AddSubgroup.closure Ψ := by
  classical
  have htr : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  obtain ⟨t', e', ht', hts', he', ht'r, hN'⟩ := exists_dynkinType hτ hΨ' (hne.mono hsub)
  have hrr : t'.rank = t.rank := by rw [← htr, ← ht'r, hcard]
  set e'' : simpleRoots Ψ' ≃ Fin t.rank := e'.trans (finCongr hrr) with he''
  obtain ⟨M, hM⟩ := exists_simpleRoots_coeff hΨ' hsub e e''
  set D : Fin t.rank → Fin τ.rank → ℤ := fun i => ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ)
  set D' : Fin t.rank → Fin τ.rank → ℤ :=
    fun j => ((e''.symm j : simpleRoots Ψ') : Fin τ.rank → ℤ)
  have hG : (Matrix.of fun i j => iform (D i) (D j)) = t.cartanMatrix := by
    ext i j
    simp only [Matrix.of_apply, D, he, Equiv.apply_symm_apply]
  have hG' : (Matrix.of fun i j => iform (D' i) (D' j)) =
      t'.cartanMatrix.submatrix (finCongr hrr.symm) (finCongr hrr.symm) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, D', he', he'', Equiv.symm_trans_apply,
      Equiv.apply_symm_apply, finCongr_symm]
  have hdet := det_gram_eq_det_sq_mul D D' M hM
  rw [hG, hG', Matrix.det_submatrix_equiv_self] at hdet
  refine ⟨t', e', M.det, ht', hts', he', ht'r.symm, hN', hdet,
    subset_of_isUnit_det hτ hΨ hΨ' e e'' M hM, fun β hβ => ?_⟩
  obtain ⟨c, hc⟩ := exists_coords hΨ' hβ
  rw [hc, Finset.smul_sum, ← Finset.sum_coe_sort (simpleRoots Ψ')]
  refine AddSubgroup.sum_mem _ fun γ _ => ?_
  rw [smul_comm]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have h := det_smul_eq_sum_adjugate D D' M hM (e'' γ)
  have hγ : D' (e'' γ) = (γ : Fin τ.rank → ℤ) := by simp [D']
  rw [hγ] at h
  rw [h]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _
    (AddSubgroup.subset_closure (simpleRoots_subset (e.symm i).2)) _

theorem ratClosure_eq_of_compRank_eq {Ψ : Set (Fin τ.rank → ℤ)} (h : compRank Ψ = τ.rank) :
    ratClosure Ψ = {γ | IsRoot τ γ} := by
  have htop : Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
  ext γ
  simp only [mem_ratClosure, htop, Submodule.mem_top, and_true, Set.mem_setOf_eq]

theorem nonClosedRootCensus_holds :
    ∀ τ : Tag, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ Ψ : Set (Fin τ.rank → ℤ),
      IsRootComponent Ψ → ¬ RootsRationallyClosed τ Ψ →
        (∀ β : Fin τ.rank → ℤ, IsRoot τ β →
          (fun k => (β k : ℚ)) ∈ Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) →
            (2 : ℤ) • β ∈ AddSubgroup.closure Ψ) ∨
        (τ = .E8 ∧ compRank Ψ = 8 ∧ Ψ.ncard = 72 ∧
          ∀ Ψ' : Set (Fin τ.rank → ℤ), (∀ α ∈ Ψ', IsRoot τ α) → (∀ α ∈ Ψ', -α ∈ Ψ') →
            (∀ α ∈ Ψ', ∀ β ∈ Ψ', IsRoot τ (α + β) → α + β ∈ Ψ') → Ψ ⊆ Ψ' →
              Ψ' = Ψ ∨ Ψ' = {γ | IsRoot τ γ}) := by
  intro τ hτ Ψ hΨ hncl
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hcardΨ := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ
  have hle8 : compRank Ψ ≤ 8 :=
    (CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le Ψ).trans
      (CFSG.HardMathSupport.Timmesfeld.RootAut.rank_le_eight τ)
  have hne : Ψ.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    subst h0
    refine hncl fun β hβ hsp => ?_
    rw [Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hsp
    have hβ0 : β = 0 := funext fun k => by
      have h := congrFun hsp k
      simp only [Pi.zero_apply] at h
      exact_mod_cast h
    have hpos := iform_self_pos_of_isRoot hβ
    rw [hβ0] at hpos
    simp [iform] at hpos
  obtain ⟨t, e, ht, hts, he, htr, hN⟩ := exists_dynkinType hτ' hΨ hne
  have hr8 : t.rank ≤ 8 := by rw [← htr, ← hcardΨ]; exact hle8
  have hd := detOfRank_of_isSimplyLaced ht hts
  have hΦ := isRootComponent_ratClosure hΨ
  have hsub := subset_ratClosure hΨ.isRoot
  have hcard : (simpleRoots Ψ).card = (simpleRoots (ratClosure Ψ)).card := by
    rw [← hcardΨ, ← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΦ, compRank,
      compRank, span_ratClosure hΨ.isRoot]
  obtain ⟨t', -, k, ht', hts', -, ht'r, -, hdet, hunit, hkmem⟩ :=
    exists_nested_det hτ' hΨ hΦ hne hsub hcard t e he
  have hk : ¬ (k = 1 ∨ k = -1) := fun hu => hncl fun β hβ hsp => hunit hu ⟨hβ, hsp⟩
  have hrr : t'.rank = t.rank := by rw [ht'r, ← hcard, htr]
  have hd' : DetOfRank t.rank t'.cartanMatrix.det := hrr ▸ detOfRank_of_isSimplyLaced ht' hts'
  rcases census_arith hr8 hd hd' hdet hk with hk2 | ⟨hr, h9, -⟩
  ·
    left
    intro β hβ hsp
    have h := hkmem β ⟨hβ, hsp⟩
    rcases hk2 with rfl | rfl
    · exact h
    · simpa using AddSubgroup.neg_mem _ h
  right
  have hA : t = .A 8 := by
    rcases det_cartanMatrix_of_isSimplyLaced ht hts with h | h | h | h | h
    · rw [h.1, hr]
    · rw [h.2.2] at h9; norm_num at h9
    · rw [h.2] at h9; norm_num at h9
    · rw [h.2] at h9; norm_num at h9
    · rw [h.2] at h9; norm_num at h9
  have hrk8 : compRank Ψ = 8 := by rw [hcardΨ, htr, hr]
  have hτE8 : τ = .E8 := by
    have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le Ψ
    rw [hrk8] at h
    rcases hτ with rfl | rfl | rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
  subst hτE8
  refine ⟨rfl, hrk8, by rw [hN, hA, DynkinType.numRoots_A], fun Ψ' hroot hneg hadd hΨΨ' => ?_⟩
  have hfull : ratClosure Ψ = {γ | IsRoot Tag.E8 γ} := ratClosure_eq_of_compRank_eq hrk8
  have hΨ'r : Ψ' ⊆ ratClosure Ψ := fun α hα => by rw [hfull]; exact hroot α hα
  have hΨ'c := isRootComponent_of_closed hτ' hΨ hroot hneg hadd hΨΨ' hΨ'r
  have hrk8' : compRank Ψ' = 8 := by
    have h1 : compRank Ψ ≤ compRank Ψ' := by
      unfold compRank
      exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono hΨΨ'))
    have h2 := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le Ψ'
    change compRank Ψ' ≤ 8 at h2
    omega
  have hcard' : (simpleRoots Ψ).card = (simpleRoots Ψ').card := by
    rw [← hcardΨ, ← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ'c, hrk8, hrk8']
  obtain ⟨t₂, e₂, k₂, ht₂, hts₂, he₂, ht₂r, -, hdet₂, hunit₂, -⟩ :=
    exists_nested_det hτ' hΨ hΨ'c hne hΨΨ' hcard' t e he
  have hd₂ : DetOfRank 8 t₂.cartanMatrix.det := by
    have h := detOfRank_of_isSimplyLaced ht₂ hts₂
    have hr2 : t₂.rank = 8 := by rw [ht₂r, ← hcard', htr, hr]
    generalize t₂.cartanMatrix.det = d₂ at h ⊢
    rwa [hr2] at h
  have hdA : t.cartanMatrix.det = 9 := by
    rcases hd with h | h | h | h | h
    · rw [h, hr]; norm_num
    all_goals omega
  rw [hdA] at hdet₂
  rcases nine_arith hd₂ hdet₂ with hu | hd₁
  ·
    exact Or.inl (Set.Subset.antisymm (hunit₂ hu) hΨΨ')
  ·
    right
    have hfull' : ratClosure Ψ' = {γ | IsRoot Tag.E8 γ} := ratClosure_eq_of_compRank_eq hrk8'
    have hΦ' := isRootComponent_ratClosure hΨ'c
    have hcard'' : (simpleRoots Ψ').card = (simpleRoots (ratClosure Ψ')).card := by
      rw [← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ'c,
        ← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΦ', compRank, compRank,
        span_ratClosure hΨ'c.isRoot]
    obtain ⟨t₃, -, k₃, ht₃, hts₃, -, -, -, hdet₃, hunit₃, -⟩ :=
      exists_nested_det hτ' hΨ'c hΦ' (hne.mono hΨΨ') (subset_ratClosure hΨ'c.isRoot) hcard''
        t₂ e₂ he₂
    rw [hd₁] at hdet₃
    have hk₃ := one_arith (one_le_of_detOfRank (detOfRank_of_isSimplyLaced ht₃ hts₃)) hdet₃
    refine Set.Subset.antisymm (fun γ hγ => hroot γ hγ) ?_
    rw [← hfull']
    exact hunit₃ hk₃

end CFSG.LieType.Chevalley
