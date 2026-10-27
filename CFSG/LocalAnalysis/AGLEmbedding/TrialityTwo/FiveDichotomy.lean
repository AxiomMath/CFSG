module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveQuadratic

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Five

open Module QuadraticMap

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {φ : V ≃ₗ[K] V}

theorem finrank_fixedSpace_eq_four (hK : Nat.card K = 2) (hV : finrank K V = 8)
    (hφ5 : φ ^ 5 = 1) (hφ1 : φ ≠ 1) (hC : fixedSpace φ ≠ ⊥) : finrank K (fixedSpace φ) = 4 := by
  obtain ⟨k, hk⟩ := four_dvd_finrank_fixedSpace hK hφ5 (by rw [hV]; norm_num)
  have hle : finrank K (fixedSpace φ) ≤ 8 := hV ▸ Submodule.finrank_le _
  have hne0 : finrank K (fixedSpace φ) ≠ 0 := fun h => hC (Submodule.finrank_eq_zero.mp h)
  have hne8 : finrank K (fixedSpace φ) ≠ 8 := by
    intro h
    apply hφ1
    have htop : fixedSpace φ = ⊤ := Submodule.eq_top_of_finrank_eq (h.trans hV.symm)
    ext x
    have hx : x ∈ fixedSpace φ := by rw [htop]; trivial
    exact mem_fixedSpace.mp hx
  omega

theorem false_of_fixed_of_solid (hK : Nat.card K = 2) (hV : finrank K V = 8)
    (hQ : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (hφQ : ∀ x, Q (φ x) = Q x) (hφ5 : φ ^ 5 = 1)
    (hφ1 : φ ≠ 1) {v : V} (hv : v ≠ 0) (hφv : φ v = v) {U : Submodule K V}
    (hU4 : finrank K U = 4) (hUQ : ∀ x ∈ U, Q x = 0) (hUφ : ∀ x ∈ U, φ x ∈ U) : False := by
  have h2 := two_eq_zero hK
  have hC4 : finrank K (fixedSpace φ) = 4 := by
    refine finrank_fixedSpace_eq_four hK hV hφ5 hφ1 fun h => hv ?_
    have hvC : v ∈ fixedSpace φ := mem_fixedSpace.mpr hφv
    rwa [h, Submodule.mem_bot] at hvC
  have hdvd := four_dvd_finrank_inf hK hφ5 hUφ (by rw [hU4])
  have hle : finrank K ↥(U ⊓ fixedSpace φ) ≤ 4 := hU4 ▸ Submodule.finrank_mono inf_le_left
  obtain ⟨k, hk⟩ := hdvd
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  ·
    have hbot : U ⊓ fixedSpace φ = ⊥ := Submodule.finrank_eq_zero.mp hk
    have hUC : ∀ u ∈ U, ∀ c ∈ fixedSpace φ, polar Q c u = 0 := by
      intro u hu c hc
      rw [← polar_normSum hφQ h2 hc u]
      have hN : normSum φ u ∈ U ⊓ fixedSpace φ :=
        ⟨normSum_mem hUφ hu, normSum_mem_fixedSpace hφ5 u⟩
      rw [hbot, Submodule.mem_bot] at hN
      rw [hN, polar_zero_right]
    have hsup : U ⊔ fixedSpace φ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_sup_add_finrank_inf_eq U (fixedSpace φ)
      rw [hk, hU4, hC4] at this
      omega
    have hUbot : U = ⊥ := by
      refine (Submodule.eq_bot_iff U).mpr fun u hu => hQ u fun y => ?_
      have hy : y ∈ U ⊔ fixedSpace φ := by rw [hsup]; trivial
      obtain ⟨u', hu', c, hc, rfl⟩ := Submodule.mem_sup.mp hy
      rw [polar_add_right, polar_eq_zero_of_forall hUQ hu hu', polar_comm, hUC u hu c hc,
        add_zero]
    rw [hUbot, finrank_bot] at hU4
    omega
  ·
    have hUC : U ⊓ fixedSpace φ = U :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hk, hU4])
    have hUeq : U = fixedSpace φ :=
      Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp hUC) (by rw [hU4, hC4])
    have hCbot : fixedSpace φ = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun c hc => hQ c fun y => ?_
      rw [← polar_normSum hφQ h2 hc y]
      exact polar_eq_zero_of_forall hUQ (hUeq ▸ hc) (hUeq ▸ normSum_mem_fixedSpace hφ5 y)
    rw [hCbot, finrank_bot] at hC4
    omega

omit [Finite K] [FiniteDimensional K V] in
theorem pow_four_apply_mem_span (hφ5 : φ ^ 5 = 1) (hC : fixedSpace φ = ⊥) (v : V) :
    (φ ^ 4) v ∈ Submodule.span K (Set.range fun k : Fin 4 => (φ ^ (k : ℕ)) v) := by
  have hN := normSum_mem_fixedSpace hφ5 v
  rw [hC, Submodule.mem_bot, normSum, Finset.sum_range_succ] at hN
  rw [eq_neg_of_add_eq_zero_right hN]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.subset_span ?_)
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩

theorem exists_solid_of_forall_fixed (hK : Nat.card K = 2) (hV : finrank K V = 8)
    (hφQ : ∀ x, Q (φ x) = Q x) (hφ5 : φ ^ 5 = 1) (hfix : ∀ c, φ c = c → Q c = 0 → c = 0)
    {v : V} (hv : v ≠ 0) (h0 : Q v = 0) (h1 : polar Q v (φ v) = 0)
    (h2 : polar Q v ((φ ^ 2) v) = 0) :
    ∃ U : Submodule K V, finrank K U = 4 ∧ (∀ x ∈ U, Q x = 0) ∧ U.map φ.toLinearMap = U := by
  have hC : fixedSpace φ = ⊥ := by
    by_contra hC
    obtain ⟨k, hk⟩ := four_dvd_finrank_fixedSpace hK hφ5 (by rw [hV]; norm_num)
    have hne0 : finrank K (fixedSpace φ) ≠ 0 := fun h => hC (Submodule.finrank_eq_zero.mp h)
    obtain ⟨c, hc, hc0, hQc⟩ :=
      exists_ne_zero_eq_zero_of_three_le hK Q (U := fixedSpace φ) (by omega)
    exact hc0 (hfix c (mem_fixedSpace.mp hc) hQc)
  set f : Fin 4 → V := fun k => (φ ^ (k : ℕ)) v with hf
  set U := Submodule.span K (Set.range f) with hU
  have hmem : ∀ k : ℕ, k < 4 → (φ ^ k) v ∈ U := fun k hk =>
    Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  have hle : U.map φ.toLinearMap ≤ U := by
    rw [hU, Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    change φ ((φ ^ (k : ℕ)) v) ∈ U
    rw [← LinearEquiv.mul_apply, ← pow_succ']
    have hk := k.isLt
    rcases Nat.lt_or_ge ((k : ℕ) + 1) 4 with hk' | hk'
    · exact hmem _ hk'
    · rw [show (k : ℕ) + 1 = 4 by omega]
      exact pow_four_apply_mem_span hφ5 hC v
  have hφU : ∀ x ∈ U, φ x ∈ U := fun x hx => hle (Submodule.mem_map_of_mem hx)
  have e : (φ ^ 3) ((φ ^ 2) v) = v := by
    rw [← LinearEquiv.mul_apply, ← pow_add, show 3 + 2 = 5 from rfl, hφ5]
    rfl
  have hpolar : ∀ k : ℕ, k < 4 → polar Q v ((φ ^ k) v) = 0 := by
    intro k hk
    interval_cases k
    · simp [polar_self, h0]
    · rwa [pow_one]
    · exact h2
    · calc polar Q v ((φ ^ 3) v) = polar Q ((φ ^ 3) ((φ ^ 2) v)) ((φ ^ 3) v) := by rw [e]
        _ = polar Q ((φ ^ 2) v) v := polar_pow_apply hφQ 3 _ _
        _ = 0 := by rw [polar_comm]; exact h2
  have hpair : ∀ i j : ℕ, i ≤ j → j < 4 → polar Q ((φ ^ i) v) ((φ ^ j) v) = 0 := by
    intro i j hij hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [pow_add, LinearEquiv.mul_apply, polar_pow_apply hφQ]
    exact hpolar d (by omega)
  have hUQ : ∀ x ∈ U, Q x = 0 := by
    refine forall_mem_span_eq_zero ?_ ?_
    · rintro _ ⟨k, rfl⟩
      exact (map_pow_apply hφQ _ v).trans h0
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rcases le_total (i : ℕ) j with hij | hji
      · exact hpair i j hij j.isLt
      · rw [polar_comm]
        exact hpair j i hji i.isLt
  have hU4 : finrank K U = 4 := by
    have hle4 : finrank K U ≤ 4 := (finrank_range_le_card (R := K) f).trans_eq (Fintype.card_fin 4)
    obtain ⟨k, hk⟩ := four_dvd_finrank_of_inf_eq_bot hK hφ5 hφU (by rw [hC, inf_bot_eq])
    have hne : finrank K U ≠ 0 := by
      intro h
      have hvU : v ∈ U := by simpa using hmem 0 (by norm_num)
      rw [Submodule.finrank_eq_zero.mp h, Submodule.mem_bot] at hvU
      exact hv hvU
    omega
  exact ⟨U, hU4, hUQ, Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq φ U)⟩

end CFSG.AGLEmbedding.TrialityTwo.Five
