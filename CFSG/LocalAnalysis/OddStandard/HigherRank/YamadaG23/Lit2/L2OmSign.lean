module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthWitness

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

private theorem l2_reflect_apply_self {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {v : V} (hv : Q v ≠ 0) : reflect Q v v = -v := by
  rw [reflect_apply hv, polar_self_eq_two_mul, mul_div_assoc, div_self hv, mul_one]
  rw [two_smul, sub_eq_add_neg, neg_add, ← add_assoc, add_neg_cancel, zero_add]

theorem l2_om_sign_family {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {x : Fin 4 → V ≃ₗ[K] V}
    (hxO : ∀ i, x i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {w : Fin 8 → V}
    (hw0 : ∀ j, Q (w j) ≠ 0) (hwo : ∀ j k, j ≠ k → polar Q (w j) (w k) = 0)
    (hwe : ∀ i j, ∃ s : K, x i (w j) = s • w j) (c : Fin 8 → Prop) [DecidablePred c]
    (hc : ∀ j k, (c j ↔ c k) → IsSquare (Q (w j) * Q (w k))) :
    ∃ g : Finset (Fin 8) → (V ≃ₗ[K] V),
      (∀ J, g J ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧ (∀ J, g J * g J = 1) ∧
      (∀ J i, x i * g J = g J * x i) ∧
      (∀ J k, g J (w k) = if k ∈ J then -w k else w k) ∧
      ∀ J : Finset (Fin 8), Even (J.filter c).card → Even (J.filter fun j => ¬ c j).card →
        g J ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  classical
  let r : Fin 8 → V ≃ₗ[K] V := fun j => reflect Q (w j)
  have hr_comm : ∀ j k, r j * r k = r k * r j := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; rfl
    · exact CFSG.ComponentClassification.OddClassSelector.reflect_comm_of_polar_eq_zero
        (hwo j k hjk)
  have hpair : (Set.range r).Pairwise Commute := by
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _
    exact hr_comm j k
  let C : Subgroup (V ≃ₗ[K] V) := Subgroup.closure (Set.range r)
  letI : CommGroup C := Subgroup.closureCommGroupOfComm hpair
  let f : Fin 8 → C := fun j => ⟨r j, Subgroup.subset_closure ⟨j, rfl⟩⟩
  let g : Finset (Fin 8) → V ≃ₗ[K] V := fun J => ((∏ j ∈ J, f j : C) : V ≃ₗ[K] V)
  have hC_le_O : C ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    change Subgroup.closure (Set.range r) ≤ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact reflect_mem_orthogonalGroup Q (w j)
  have hg_insert : ∀ (a : Fin 8) (s : Finset (Fin 8)), a ∉ s → g (insert a s) = r a * g s := by
    intro a s ha
    show ((∏ j ∈ insert a s, f j : C) : V ≃ₗ[K] V) =
      r a * ((∏ j ∈ s, f j : C) : V ≃ₗ[K] V)
    rw [Finset.prod_insert ha, Subgroup.coe_mul]
  have hg_empty : g ∅ = 1 := by
    show ((∏ j ∈ (∅ : Finset (Fin 8)), f j : C) : V ≃ₗ[K] V) = 1
    rw [Finset.prod_empty, Subgroup.coe_one]
  have hxr : ∀ i j, x i * r j = r j * x i := by
    intro i j
    obtain ⟨s, hs⟩ := hwe i j
    have hQ : Q (x i (w j)) = Q (w j) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hxO i) (w j)
    have hs2 : s * s = 1 := by
      have h1 : (s * s) * Q (w j) = Q (w j) := by
        calc (s * s) * Q (w j) = Q (s • w j) := by
              rw [QuadraticMap.map_smul, smul_eq_mul]
          _ = Q (x i (w j)) := by rw [hs]
          _ = Q (w j) := hQ
      exact mul_right_cancel₀ (hw0 j) (by rw [h1, one_mul])
    have hs0 : s ≠ 0 := by
      rintro rfl
      simpa using hs2
    have hconj : x i * r j * (x i)⁻¹ = r j := by
      rw [reflect_conj (hxO i) (w j), hs,
        CFSG.LocalAnalysis.ComponentInitial.reflect_smul_of_ne_zero hs0 (w j)]
    exact (mul_inv_eq_iff_eq_mul).mp hconj
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro J
    exact hC_le_O (∏ j ∈ J, f j : C).2
  · intro J
    have h : (∏ j ∈ J, f j : C) * (∏ j ∈ J, f j : C) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one ?_
      intro j _
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact reflect_mul_self Q (w j)
    show ((∏ j ∈ J, f j : C) : V ≃ₗ[K] V) * ((∏ j ∈ J, f j : C) : V ≃ₗ[K] V) = 1
    rw [← Subgroup.coe_mul, h, Subgroup.coe_one]
  · intro J i
    induction J using Finset.induction_on with
    | empty => rw [hg_empty, mul_one, one_mul]
    | insert a s ha ih =>
      rw [hg_insert a s ha, ← mul_assoc, hxr i a, mul_assoc, ih, mul_assoc]
  · intro J k
    induction J using Finset.induction_on with
    | empty =>
      rw [hg_empty]
      simp
    | insert a s ha ih =>
      rw [hg_insert a s ha, LinearEquiv.mul_apply]
      by_cases hka : k = a
      · rw [hka] at ih ⊢
        rw [ih, if_neg ha, l2_reflect_apply_self (hw0 a)]
        rw [if_pos (Finset.mem_insert_self a s)]
      · have hak : a ≠ k := fun h => hka h.symm
        have hfix : r a (w k) = w k :=
          reflect_apply_of_polar_eq_zero (hwo a k hak)
        rw [ih]
        by_cases hks : k ∈ s
        · rw [if_pos hks, map_neg, hfix, if_pos (Finset.mem_insert_of_mem hks)]
        · rw [if_neg hks, hfix, if_neg (by simp [hks, hka])]
  · intro J hJe1 hJe2
    change ((∏ j ∈ J, f j : C) : V ≃ₗ[K] V) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆
    have key : ∀ T : Finset (Fin 8), Even T.card →
        (∀ j ∈ T, ∀ k ∈ T, IsSquare (Q (w j) * Q (w k))) →
        ((∏ j ∈ T, f j : C) : V ≃ₗ[K] V) ∈
          ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
            TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
      intro T
      induction T using Finset.strongInductionOn with
      | _ T ih =>
        intro hEven hSq
        rcases T.eq_empty_or_nonempty with rfl | hne
        · have h0 : ((∏ j ∈ (∅ : Finset (Fin 8)), f j : C) : V ≃ₗ[K] V) = 1 := by
            rw [Finset.prod_empty, Subgroup.coe_one]
          rw [h0]
          exact Subgroup.one_mem _
        · obtain ⟨m, hm⟩ := hEven
          have hcard2 : 2 ≤ T.card := by
            have := Finset.card_pos.mpr hne
            omega
          obtain ⟨a, haT, b, hbT, hab⟩ :=
            Finset.one_lt_card.mp (by omega : 1 < T.card)
          have hb : b ∈ T.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbT⟩
          set T' : Finset (Fin 8) := (T.erase a).erase b with hT'def
          have hT'_sub : T' ⊆ T := by
            intro x hx
            rw [hT'def] at hx
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
          have hnot : a ∉ T' := by
            rw [hT'def]
            exact fun h => Finset.notMem_erase a T (Finset.mem_of_mem_erase h)
          have hT'_ssub : T' ⊂ T := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨hT'_sub, fun h => hnot (h ▸ haT)⟩
          have hT'card : T'.card = T.card - 2 := by
            have h1 : T'.card = (T.erase a).card - 1 := Finset.card_erase_of_mem hb
            have h2 : (T.erase a).card = T.card - 1 := Finset.card_erase_of_mem haT
            omega
          have hEven' : Even T'.card := ⟨m - 1, by omega⟩
          have hSq' : ∀ j ∈ T', ∀ k ∈ T', IsSquare (Q (w j) * Q (w k)) :=
            fun j hj k hk => hSq j (hT'_sub hj) k (hT'_sub hk)
          have hIH := ih T' hT'_ssub hEven' hSq'
          have hprod : (∏ j ∈ T, f j : C) = (f a * f b) * (∏ j ∈ T', f j : C) := by
            rw [← Finset.mul_prod_erase T f haT, ← Finset.mul_prod_erase (T.erase a) f hb]
            simp only [hT'def, mul_assoc]
          have hmem1 : ((f a * f b : C) : V ≃ₗ[K] V) ∈
              ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
                TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
            rw [Subgroup.coe_mul]
            exact CFSG.ComponentClassification.OddClassSelector.reflect_mul_reflect_mem
              h2 (hw0 a) (hw0 b) (hSq a haT b hbT)
          rw [show ((∏ j ∈ T, f j : C) : V ≃ₗ[K] V) =
              ((f a * f b : C) : V ≃ₗ[K] V) * ((∏ j ∈ T', f j : C) : V ≃ₗ[K] V) from by
            rw [hprod, Subgroup.coe_mul]]
          exact Subgroup.mul_mem _ hmem1 hIH
    have hsq1 : ∀ j ∈ J.filter c, ∀ k ∈ J.filter c, IsSquare (Q (w j) * Q (w k)) := by
      intro j hj k hk
      exact hc j k (iff_of_true (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2)
    have hsq2 : ∀ j ∈ J.filter (fun j => ¬ c j), ∀ k ∈ J.filter (fun j => ¬ c j),
        IsSquare (Q (w j) * Q (w k)) := by
      intro j hj k hk
      exact hc j k (iff_of_false (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2)
    have h1 := key (J.filter c) hJe1 hsq1
    have h2' := key (J.filter (fun j => ¬ c j)) hJe2 hsq2
    have hprodC : (∏ j ∈ J, f j : C) =
        (∏ j ∈ J.filter c, f j : C) * (∏ j ∈ J.filter (fun j => ¬ c j), f j : C) :=
      (Finset.prod_filter_mul_prod_filter_not J c f).symm
    have hprodV : ((∏ j ∈ J, f j : C) : V ≃ₗ[K] V) =
        ((∏ j ∈ J.filter c, f j : C) : V ≃ₗ[K] V) *
        ((∏ j ∈ J.filter (fun j => ¬ c j), f j : C) : V ≃ₗ[K] V) := by
      rw [hprodC, Subgroup.coe_mul]
    rw [hprodV]
    exact Subgroup.mul_mem _ h1 h2'

end CFSG.OddStandard.HigherRank.YamadaG23
