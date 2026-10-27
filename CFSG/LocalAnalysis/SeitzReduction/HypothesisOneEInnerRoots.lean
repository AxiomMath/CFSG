module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def coPair (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, τ.cartan i j * v j

theorem reflect_eq_sub_coPair {τ : Tag} (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i v = v - coPair τ i v • Pi.single i 1 :=
  rfl

theorem reflect_eq_add_single {τ : Tag} {i : Fin τ.rank} {v : Fin τ.rank → ℤ}
    (h : coPair τ i v = -1) : reflect τ i v = v + Pi.single i 1 := by
  rw [reflect_eq_sub_coPair, h, neg_smul, one_smul, sub_neg_eq_add]

theorem reflect_eq_sub_single {τ : Tag} {i : Fin τ.rank} {v : Fin τ.rank → ℤ}
    (h : coPair τ i v = 1) : reflect τ i v = v - Pi.single i 1 := by
  rw [reflect_eq_sub_coPair, h, one_smul]

@[expose] def eRootCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (height (τ.rootCertificate.root k) ≤ 0) ||
      (List.ofFn (τ.rootCertificate.root k) == List.ofFn (highRoot τ)) ||
      (((List.finRange τ.rank).any fun i => decide (coPair τ i (τ.rootCertificate.root k) = -1)) &&
        (List.finRange τ.rank).any fun i => decide (coPair τ i (highRoot τ) = 0) &&
          decide (coPair τ i (τ.rootCertificate.root k) ∈ [1, -1, 2, -2]))

theorem eRootCheck_E6 : eRootCheck .E6 = true := by decide +kernel

theorem eRootCheck_E7 : eRootCheck .E7 = true := by decide +kernel

theorem eRootCheck_E8 : eRootCheck .E8 = true := by decide +kernel

theorem eRootCheck_eq_true {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : eRootCheck τ = true := by
  rcases hτ with rfl | rfl | rfl
  exacts [eRootCheck_E6, eRootCheck_E7, eRootCheck_E8]

@[expose] def highNode : (τ : Tag) → Fin τ.rank
  | .E6 => (1 : Fin 6)
  | .E7 => (0 : Fin 7)
  | .E8 => (7 : Fin 8)
  | .G2 => (0 : Fin 2)
  | .F4 => (0 : Fin 4)
  | .D4 => (0 : Fin 4)

theorem coPair_highNode {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    coPair τ (highNode τ) (highRoot τ) = 1 ∧ 3 ≤ height (highRoot τ) := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel


theorem eRootCheck_sound {τ : Tag} (h : eRootCheck τ = true) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hpos : 0 < height γ) (hne : γ ≠ highRoot τ) :
    (∃ i, coPair τ i γ = -1) ∧
      ∃ i, coPair τ i (highRoot τ) = 0 ∧ coPair τ i γ ∈ [1, -1, 2, -2] := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  simp only [eRootCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, List.any_eq_true, List.mem_finRange, true_and] at h
  rcases h k hk with (h1 | h2) | ⟨⟨i, hi⟩, ⟨j, hj1, hj2⟩⟩
  · exact absurd h1 (not_le.2 hpos)
  · exact absurd (RootCertificate.eq_of_ofFn_beq h2) hne
  · exact ⟨⟨i, hi⟩, j, hj1, hj2⟩

theorem exists_isRoot_add_single {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < height γ) (hne : γ ≠ highRoot τ) :
    ∃ i, coPair τ i γ = -1 ∧ IsRoot τ (γ + Pi.single i 1) := by
  obtain ⟨⟨i, hi⟩, -⟩ := eRootCheck_sound (eRootCheck_eq_true hτ) hγ hpos hne
  exact ⟨i, hi, reflect_eq_add_single hi ▸ IsRoot.reflect i hγ⟩

theorem exists_coPair_highRoot_eq_zero {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < height γ) (hne : γ ≠ highRoot τ) :
    ∃ i, coPair τ i (highRoot τ) = 0 ∧ coPair τ i γ ∈ [1, -1, 2, -2] :=
  (eRootCheck_sound (eRootCheck_eq_true hτ) hγ hpos hne).2

theorem highRoot_decomp {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    IsRoot τ (highRoot τ - Pi.single (highNode τ) 1) ∧
      highRoot τ - Pi.single (highNode τ) 1 + Pi.single (highNode τ) 1 = highRoot τ ∧
      0 < height (highRoot τ - Pi.single (highNode τ) 1) ∧
      highRoot τ - Pi.single (highNode τ) 1 ≠ highRoot τ ∧
      highRoot τ - Pi.single (highNode τ) 1 ≠ Pi.single (highNode τ) 1 ∧
      highRoot τ - Pi.single (highNode τ) 1 ≠ -Pi.single (highNode τ) 1 ∧
      (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ) ≠ highRoot τ := by
  obtain ⟨h1, h3⟩ := coPair_highNode hτ
  have hr : IsRoot τ (highRoot τ - Pi.single (highNode τ) 1) :=
    reflect_eq_sub_single h1 ▸ IsRoot.reflect (highNode τ) (isRoot_highRoot τ)
  have hht : height (highRoot τ - Pi.single (highNode τ) 1) = height (highRoot τ) - 1 := by
    have h1 := height_single (τ := τ) (highNode τ)
    simp only [height, Pi.sub_apply, Finset.sum_sub_distrib] at h1 ⊢
    rw [h1]
  have hne : ∀ u v : Fin τ.rank → ℤ, height u ≠ height v → u ≠ v := fun u v h e => h (e ▸ rfl)
  refine ⟨hr, sub_add_cancel _ _, by omega, hne _ _ (by omega), hne _ _ ?_, hne _ _ ?_,
    hne _ _ ?_⟩
  · rw [hht, height_single]
    omega
  · rw [hht, height_neg, height_single]
    omega
  · rw [height_single]
    omega

end CFSG.SeitzReduction
