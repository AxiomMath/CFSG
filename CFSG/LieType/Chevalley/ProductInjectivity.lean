module

public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Steinberg.Adjoint.Unipotent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem raises_zero_one {R : Type} [CommRing R] {φ : (Fin τ.rank → ℤ) →+ ℤ} :
    Raises φ 0 (1 : Module.End R (RootModule τ R)) := fun a b hab => by
  rw [Module.End.one_apply, Finsupp.single_apply] at hab
  split_ifs at hab with h
  · subst h
    omega
  · exact absurd rfl hab

theorem mul_sub_mul_apply {R : Type} [CommRing R] (X X' P P' : Module.End R (RootModule τ R))
    (a b : Label τ) :
    (X * P - X' * P') (Finsupp.single b 1) a =
      (P - P') (Finsupp.single b 1) a + ((X - 1) * (P - P')) (Finsupp.single b 1) a +
        ((X - X') (Finsupp.single b 1) a + ((X - X') * (P' - 1)) (Finsupp.single b 1) a) := by
  rw [show X * P - X' * P' = (P - P') + (X - 1) * (P - P') + ((X - X') + (X - X') * (P' - 1)) by
    simp only [mul_sub, sub_mul, one_mul, mul_one]
    abel]
  simp only [LinearMap.add_apply, Finsupp.add_apply]

namespace RootOperatorFamily

variable
    (F : RootOperatorFamily τ) {R : Type} [CommRing R] {φ : (Fin τ.rank → ℤ) →+ ℤ}

theorem eltOr_raises_zero
    {γ : Fin τ.rank → ℤ} (hγ : 0 ≤ φ γ) (c : R) :
    Raises φ 0 (RootOperatorFamily'.eltOr F R γ c) := by
  have h := (raises_zero_one (φ := φ)).add
    ((RootOperatorFamily'.eltOr_sub_one_raises F hγ c).mono hγ)
  rwa [add_sub_cancel] at h

theorem prod_raises_zero
    (c : (Fin τ.rank → ℤ) → R) (L : List (Fin τ.rank → ℤ))
    (hL : ∀ γ ∈ L, 0 ≤ φ γ) :
    Raises φ 0 (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod := by
  have h := (raises_zero_one (φ := φ)).add
    (RootOperatorFamily'.prod_sub_one_raises F le_rfl c L hL)
  rwa [add_sub_cancel] at h

theorem eltOr_sub_eltOr_raises
    {γ : Fin τ.rank → ℤ} (hγ : 0 ≤ φ γ) (c c' : R) :
    Raises φ (φ γ) (RootOperatorFamily'.eltOr F R γ c - RootOperatorFamily'.eltOr F R γ c') := by
  have h := (RootOperatorFamily'.eltOr_sub_one_raises F hγ c).sub
    (RootOperatorFamily'.eltOr_sub_one_raises F hγ c')
  rwa [sub_sub_sub_cancel_right] at h

theorem prod_sub_prod_raises
    {s : ℤ} (c c' : (Fin τ.rank → ℤ) → R) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ γ ∈ L, 0 ≤ φ γ) → (∀ γ ∈ L, φ γ < s → c γ = c' γ) →
      Raises φ s ((L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod -
        (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c' γ)).prod)
  | [], _, _ => by simpa using Raises.zero (R := R) (τ := τ) (φ := φ) s
  | γ :: L, hL, hc => by
    have hγ := hL γ List.mem_cons_self
    have hL' : ∀ δ ∈ L, 0 ≤ φ δ := fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ)
    have ih := prod_sub_prod_raises c c' L hL' fun δ hδ => hc δ (List.mem_cons_of_mem _ hδ)
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      show ∀ X X' P P' : Module.End R (RootModule τ R),
        X * P - X' * P' = X * (P - P') + (X - X') * P' from fun X X' P P' => by
          simp only [mul_sub, sub_mul]
          abel]
    have h1 := (eltOr_raises_zero F hγ (c γ)).mul ih
    rw [zero_add] at h1
    refine h1.add ?_
    by_cases hs : φ γ < s
    · rw [hc γ List.mem_cons_self hs, sub_self, zero_mul]
      exact Raises.zero s
    · have h2 := ((eltOr_sub_eltOr_raises F hγ (c γ) (c' γ)).mono (not_lt.1 hs)).mul
        (prod_raises_zero F c' L hL')
      rwa [add_zero] at h2

theorem eltOr_sub_eltOr_apply_of_shift
    {γ₀ γ : Fin τ.rank → ℤ} (h₀ : IsRoot τ γ₀)
    (h₀φ : 1 ≤ φ γ₀) (hγ : φ γ₀ ≤ φ γ) (c c' : (Fin τ.rank → ℤ) → R) {a b : Label τ}
    (hab : labelWt τ a = labelWt τ b + γ₀) :
    (RootOperatorFamily'.eltOr F R γ (c γ) - RootOperatorFamily'.eltOr F R γ (c' γ))
        (Finsupp.single b 1) a =
      (if γ = γ₀ then 1 else 0) * ((c γ₀ - c' γ₀) * F.D R ⟨γ₀, h₀⟩ 1 (Finsupp.single b 1) a) := by
  by_cases h : γ = γ₀
  · subst h
    simp only [↓reduceIte, one_mul, LinearMap.sub_apply, Finsupp.sub_apply,
      RootOperatorFamily'.eltOr_of_isRoot F R h₀,
      RootOperatorFamily'.elt_apply_of_shift F ⟨γ, h₀⟩ _ hab, sub_mul]
  · have hL : ∀ δ ∈ [γ], δ ≠ γ₀ ∧ φ γ₀ ≤ φ δ := by simpa using ⟨h, hγ⟩
    have e1 := RootOperatorFamily'.prod_sub_one_apply_eq_zero F h₀ h₀φ c hab [γ] hL
    have e2 := RootOperatorFamily'.prod_sub_one_apply_eq_zero F h₀ h₀φ c' hab [γ] hL
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      LinearMap.sub_apply, Finsupp.sub_apply] at e1 e2
    simp only [h, ↓reduceIte, zero_mul, LinearMap.sub_apply, Finsupp.sub_apply,
      sub_eq_zero.1 e1, sub_eq_zero.1 e2, sub_self]

theorem prod_sub_prod_apply_of_shift
    {γ₀ : Fin τ.rank → ℤ} (h₀ : IsRoot τ γ₀) (h₀φ : 1 ≤ φ γ₀)
    (c c' : (Fin τ.rank → ℤ) → R) {a b : Label τ} (hab : labelWt τ a = labelWt τ b + γ₀) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ γ ∈ L, 1 ≤ φ γ) → (∀ γ ∈ L, φ γ < φ γ₀ → c γ = c' γ) →
      ((L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod -
          (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c' γ)).prod) (Finsupp.single b 1) a =
        (L.count γ₀ : R) * ((c γ₀ - c' γ₀) * F.D R ⟨γ₀, h₀⟩ 1 (Finsupp.single b 1) a)
  | [], _, _ => by simp
  | γ :: L, hL, hc => by
    have hφab : φ (labelWt τ a) = φ (labelWt τ b) + φ γ₀ := by rw [hab, map_add]
    have hγ := hL γ List.mem_cons_self
    have hL' : ∀ δ ∈ L, 1 ≤ φ δ := fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ)
    have hc' : ∀ δ ∈ L, φ δ < φ γ₀ → c δ = c' δ := fun δ hδ => hc δ (List.mem_cons_of_mem _ hδ)
    have hγ0 : 0 ≤ φ γ := by omega
    have ih := prod_sub_prod_apply_of_shift h₀ h₀φ c c' hab L hL' hc'
    have hdiff := prod_sub_prod_raises F c c' L (fun δ hδ => by have := hL' δ hδ; omega) hc'
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, mul_sub_mul_apply, ih,
      Raises.apply_eq_zero ((RootOperatorFamily'.eltOr_sub_one_raises F hγ0 (c γ)).mul hdiff)
        (by omega), add_zero]
    by_cases hs : φ γ < φ γ₀
    · have hne : γ ≠ γ₀ := fun h => by rw [h] at hs; exact lt_irrefl _ hs
      rw [hc γ List.mem_cons_self hs, sub_self, zero_mul, LinearMap.zero_apply,
        Finsupp.zero_apply, add_zero, add_zero, List.count_cons_of_ne hne]
    · push Not at hs
      rw [Raises.apply_eq_zero ((eltOr_sub_eltOr_raises F hγ0 (c γ) (c' γ)).mul
          (RootOperatorFamily'.prod_sub_one_raises F zero_le_one c' L hL')) (by omega), add_zero,
        eltOr_sub_eltOr_apply_of_shift F h₀ h₀φ hs c c' hab, List.count_cons]
      by_cases hγ₀ : γ = γ₀
      · simp only [hγ₀, beq_self_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        ring
      · simp [hγ₀]

theorem eq_zero_of_smul_D_one_eq_zero
    (α : Root τ) {d : R} (h : d • F.D R α 1 = 0) : d = 0 := by
  obtain ⟨j, ε, w, hε, hw⟩ := RootOperatorFamily'.exists_D_eq_word F α
  set W := (w.map fun i => weylElt τ R i 1).prod
  have h1 : (W : Module.End R (RootModule τ R)) * (d • xCoeff τ R j 1) *
      ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) = 0 := by
    have h2 := congrArg (((ε : ℤ) : R) • ·) h
    simp only [hw R 1, pow_one, smul_smul, smul_zero] at h2
    rw [show (ε : R) * (d * (ε : R)) = d by linear_combination d * sign_cast_eq (R := R) hε]
      at h2
    rw [mul_smul_comm, smul_mul_assoc]
    exact h2
  have h3 : d • xCoeff τ R j 1 = 0 := by
    have := congrArg (fun A => ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) * A * (W : Module.End R (RootModule τ R))) h1
    simpa [mul_assoc] using this
  have h4 := congrArg (fun A : Module.End R (RootModule τ R) =>
    A (rootVec τ R (-Pi.single j 1)) (Sum.inl j)) h3
  simpa [xCoeff_one, infE_rootVec_neg_single, hVec] using h4

theorem prod_eltOr_injective_of_ring
    (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ γ ∈ L, IsRoot τ γ ∧ 0 < φ γ) (c c' : (Fin τ.rank → ℤ) → R)
    (heq : (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod =
      (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c' γ)).prod) :
    ∀ γ ∈ L, c γ = c' γ := by
  have hL1 : ∀ γ ∈ L, 1 ≤ φ γ := fun γ hγ => (hL γ hγ).2
  have key : ∀ n : ℕ, ∀ γ ∈ L, φ γ < n → c γ = c' γ := by
    intro n
    induction n with
    | zero =>
      intro γ hγ hn
      have := (hL γ hγ).2
      omega
    | succ n ih =>
      intro γ hγ hn
      by_cases hlt : φ γ < n
      · exact ih γ hγ hlt
      obtain ⟨h₀, h₀φ⟩ := hL γ hγ
      have hlow : ∀ δ ∈ L, φ δ < φ γ → c δ = c' δ := fun δ hδ hδφ => ih δ hδ (by omega)
      refine sub_eq_zero.1 (eq_zero_of_smul_D_one_eq_zero F ⟨γ, h₀⟩ ?_)
      refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply,
        Finsupp.smul_apply, smul_eq_mul, LinearMap.zero_comp, LinearMap.zero_apply,
        Finsupp.zero_apply]
      by_cases hD : F.D R ⟨γ, h₀⟩ 1 (Finsupp.single b 1) a = 0
      · rw [hD, mul_zero]
      have hab : labelWt τ a = labelWt τ b + γ := by
        have := F.mapsLabelWt_D (R := R) ⟨γ, h₀⟩ le_rfl a b hD
        rwa [one_nsmul] at this
      have h := prod_sub_prod_apply_of_shift F h₀ h₀φ c c' hab L hL1 hlow
      rw [heq, sub_self, LinearMap.zero_apply, Finsupp.zero_apply,
        List.count_eq_one_of_mem hnd hγ, Nat.cast_one, one_mul] at h
      exact h.symm
  intro γ hγ
  exact key ((φ γ).toNat + 1) γ hγ (by have := Int.self_le_toNat (φ γ); push_cast; omega)

end RootOperatorFamily

theorem coe_list_prod_pinnedX
    {R : Type} [CommRing R] (c : (Fin τ.rank → ℤ) → R) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ α ∈ L, IsRoot τ α) →
      (((L.map fun α => pinnedX τ R α (c α)).prod : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
        (L.map fun α => RootOperatorFamily'.eltOr (rootOperatorFamily τ) R α
          (((rootOperatorFamily τ).pinnedFamilySign α : R) * c α)).prod
  | [], _ => by simp
  | α :: L, hL => by
    rw [List.map_cons, List.prod_cons, Units.val_mul, List.map_cons, List.prod_cons,
      coe_list_prod_pinnedX c L fun β hβ => hL β (List.mem_cons_of_mem _ hβ),
      (rootOperatorFamily τ).pinnedX_eq_eltUnit R (hL α List.mem_cons_self),
      RootOperatorFamily.coe_eltUnit,
      RootOperatorFamily'.eltOr_of_isRoot _ R (hL α List.mem_cons_self)]

theorem pinnedX_list_prod_mem_posUnipotent
    {R : Type*} [CommRing R] (L : List (Fin τ.rank → ℤ))
    (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α) (c : (Fin τ.rank → ℤ) → R) :
    (L.map fun α => pinnedX τ R α (c α)).prod ∈ posUnipotent τ R := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
  have hle : rootSubgroup τ R α ≤ posUnipotent τ R := le_iSup₂_of_le α (hL α hα) le_rfl
  exact hle (Subgroup.subset_closure ⟨c α, rfl⟩)

theorem pinnedX_list_prod_injective
    {R : Type} [CommRing R] (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α) (c c' : (Fin τ.rank → ℤ) → R)
    (heq : (L.map fun α => pinnedX τ R α (c α)).prod =
      (L.map fun α => pinnedX τ R α (c' α)).prod) :
    ∀ α ∈ L, c α = c' α := by
  have h := congrArg (fun g : (Module.End R (RootModule τ R))ˣ =>
    (g : Module.End R (RootModule τ R))) heq
  rw [coe_list_prod_pinnedX c L fun α hα => (hL α hα).1,
    coe_list_prod_pinnedX c' L fun α hα => (hL α hα).1] at h
  have key := RootOperatorFamily.prod_eltOr_injective_of_ring (rootOperatorFamily τ)
    (φ := AddMonoidHom.mk' (height (τ := τ)) fun u v => by
      simp only [height, Pi.add_apply, Finset.sum_add_distrib])
    L hnd hL _ _ h
  intro α hα
  have h1 := congrArg (((rootOperatorFamily τ).pinnedFamilySign α : R) * ·) (key α hα)
  simp only [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self, one_mul] at h1
  exact h1

theorem positive_root_product_injectivity
    (τ : Tag) (R : Type) [CommRing R] {m : ℕ}
    (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α)
    (hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i)) :
    (∀ c : Fin m → R, (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod ∈ posUnipotent τ R) ∧
      Function.Injective fun c : Fin m → R =>
        (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod := by
  have hL : ∀ γ ∈ List.ofFn α, IsRoot τ γ ∧ 0 < height γ := by
    intro γ hγ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hγ
    exact hpos i
  have hprod : ∀ c : Fin m → R, (List.ofFn fun i => pinnedX τ R (α i) (c i)) =
      (List.ofFn α).map fun γ => pinnedX τ R γ (Function.extend α c 0 γ) := by
    intro c
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, hα.extend_apply]
  refine ⟨fun c => ?_, fun c c' h => ?_⟩
  · rw [hprod]
    exact pinnedX_list_prod_mem_posUnipotent _ hL _
  · simp only [hprod] at h
    funext i
    have := pinnedX_list_prod_injective (List.ofFn α) (List.nodup_ofFn.2 hα) hL _ _ h (α i)
      (List.mem_ofFn.2 ⟨i, rfl⟩)
    rwa [hα.extend_apply, hα.extend_apply] at this

end CFSG.LieType.Chevalley
