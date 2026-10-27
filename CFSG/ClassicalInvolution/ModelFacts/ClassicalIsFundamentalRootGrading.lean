module

public import CFSG.LieType.Chevalley.ParabolicGradedAction

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Grading

variable {τ : Tag} {K : Type} [Field K]

@[expose] def PreservesGrading (ℓ : (Fin τ.rank → ℤ) → ℤ)
    (f : Module.End K (RootModule τ K)) : Prop :=
  ∀ a b : Label τ, f (Finsupp.single b 1) a ≠ 0 → ℓ (labelWt τ a) = ℓ (labelWt τ b)

namespace PreservesGrading

variable {ℓ : (Fin τ.rank → ℤ) → ℤ} {f g : Module.End K (RootModule τ K)}

theorem one : PreservesGrading (K := K) ℓ (1 : Module.End K (RootModule τ K)) := by
  intro a b hab
  rw [Module.End.one_apply, Finsupp.single_apply] at hab
  split_ifs at hab with h
  · rw [h]
  · exact absurd rfl hab

theorem mul (hf : PreservesGrading ℓ f) (hg : PreservesGrading ℓ g) :
    PreservesGrading ℓ (f * g) := by
  intro a b hab
  rw [Module.End.mul_apply, ← Finsupp.sum_single (g (Finsupp.single b 1)), Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  rw [hf a c (right_ne_zero_of_mul hc'), hg c b (Finsupp.mem_support_iff.mp hc)]

theorem add (hf : PreservesGrading ℓ f) (hg : PreservesGrading ℓ g) :
    PreservesGrading ℓ (f + g) := by
  intro a b hab
  rw [LinearMap.add_apply, Finsupp.add_apply] at hab
  by_cases h1 : f (Finsupp.single b 1) a = 0
  · rw [h1, zero_add] at hab
    exact hg a b hab
  · exact hf a b h1

theorem smul (hf : PreservesGrading ℓ f) (r : K) : PreservesGrading ℓ (r • f) := fun a b hab => by
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hab
  exact hf a b (right_ne_zero_of_mul hab)

theorem zero : PreservesGrading (K := K) ℓ (0 : Module.End K (RootModule τ K)) := fun a b hab => by
  simp at hab

theorem sum {ι : Type*} (s : Finset ι) {F : ι → Module.End K (RootModule τ K)}
    (h : ∀ i ∈ s, PreservesGrading ℓ (F i)) : PreservesGrading ℓ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end PreservesGrading

@[expose] def gradingSubgroup (K : Type) [Field K] (ℓ : (Fin τ.rank → ℤ) →+ ℤ) :
    Subgroup (Module.End K (RootModule τ K))ˣ where
  carrier := {g | PreservesGrading (K := K) ℓ (g : Module.End K (RootModule τ K)) ∧
    PreservesGrading (K := K) ℓ ((g⁻¹ : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K))}
  mul_mem' := fun {g h} hg hh => ⟨by
      rw [Units.val_mul]; exact hg.1.mul hh.1, by
      rw [mul_inv_rev, Units.val_mul]; exact hh.2.mul hg.2⟩
  one_mem' := ⟨by rw [Units.val_one]; exact PreservesGrading.one, by
      rw [inv_one, Units.val_one]; exact PreservesGrading.one⟩
  inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem pinnedX_mem_gradingSubgroup (ℓ : (Fin τ.rank → ℤ) →+ ℤ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hℓ : ℓ γ = 0) (c : K) : pinnedX τ K γ c ∈ gradingSubgroup K ℓ := by
  have key : ∀ c : K, PreservesGrading (K := K) ℓ
      (pinnedX τ K γ c : Module.End K (RootModule τ K)) := by
    intro c
    rw [pinnedX_eq_sum]
    refine PreservesGrading.sum _ fun k _ => (?_ : PreservesGrading ℓ _).smul _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pinnedCoeff_zero]
      exact PreservesGrading.one
    · intro a b hab
      rw [mapsLabelWt_pinnedCoeff hγ hk a b hab, map_add, map_nsmul, hℓ, smul_zero, add_zero]
  exact ⟨key c, by rw [pinnedX_neg]; exact key (-c)⟩

theorem rootSubgroup_sup_le_gradingSubgroup (ℓ : (Fin τ.rank → ℤ) →+ ℤ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hℓ : ℓ γ = 0) :
    rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ≤ gradingSubgroup K ℓ := by
  have hℓ' : ℓ (-γ) = 0 := by rw [map_neg, hℓ, neg_zero]
  refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_gradingSubgroup ℓ hγ hℓ c
  · rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_gradingSubgroup ℓ (IsRoot.neg hγ) hℓ' c

theorem pinnedX_one_not_mem_gradingSubgroup (ℓ : (Fin τ.rank → ℤ) →+ ℤ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hℓ : ℓ δ ≠ 0) :
    pinnedX τ K δ 1 ∉ gradingSubgroup K ℓ := by
  intro hmem
  have hδ0 : δ ≠ 0 := hδ.ne_zero
  have hE : pinnedE τ K δ ≠ 0 := by
    intro h0
    have := smul_pinnedE_injective (R := K) (τ := τ) δ (a₁ := 1) (a₂ := 0) (by simp [h0])
    exact one_ne_zero this
  obtain ⟨a, b, hab⟩ : ∃ a b : Label τ, pinnedE τ K δ (Finsupp.single b 1) a ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => by
      simpa using h a b))
  have hab1 : pinnedCoeff τ K δ 1 (Finsupp.single b 1) a ≠ 0 := by
    rw [pinnedCoeff_one]
    exact hab
  have hshift : labelWt τ a = labelWt τ b + δ := by
    have := mapsLabelWt_pinnedCoeff (K := K) hδ (le_refl 1) a b hab1
    rwa [one_nsmul] at this
  have hne : a ≠ b := by
    rintro rfl
    exact hδ0 (by simpa using hshift)
  have hk : ∀ k : ℕ, k ≠ 1 →
      (pinnedCoeff τ K δ k : Module.End K (RootModule τ K)) (Finsupp.single b 1) a = 0 := by
    intro k hk1
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pinnedCoeff_zero, Module.End.one_apply, Finsupp.single_apply]
      simp [hne.symm]
    · by_contra hne'
      have h2 := mapsLabelWt_pinnedCoeff (K := K) hδ hk0 a b hne'
      rw [hshift] at h2
      have h3 : (k • δ : Fin τ.rank → ℤ) = δ := add_left_cancel h2.symm
      obtain ⟨j, hj⟩ : ∃ j, δ j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hδ0 (funext hcon)
      have h4 := congrFun h3 j
      simp only [Pi.smul_apply, nsmul_eq_mul] at h4
      have h5 : ((k : ℤ) - 1) * δ j = 0 := by linarith
      have h6 : (k : ℤ) - 1 = 0 := (mul_eq_zero.1 h5).resolve_right hj
      omega
  have hentry : (pinnedX τ K δ 1 : Module.End K (RootModule τ K)) (Finsupp.single b 1) a ≠ 0 := by
    have hsum : (pinnedX τ K δ 1 : Module.End K (RootModule τ K)) (Finsupp.single b 1) a =
        ∑ k ∈ Finset.range 4, (pinnedCoeff τ K δ k : Module.End K (RootModule τ K))
          (Finsupp.single b 1) a := by
      rw [pinnedX_eq_sum]
      simp [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    rw [hsum, Finset.sum_eq_single 1 (fun k _ hk1 => hk k hk1) (fun h => absurd (by decide) h)]
    exact hab1
  have hpres := hmem.1 a b hentry
  rw [hshift, map_add] at hpres
  exact hℓ (by omega)

theorem not_rootSubgroup_le_rootSubgroup_sup {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : δ ≠ γ) (hne' : δ ≠ -γ) :
    ¬ rootSubgroup τ K δ ≤ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  let ℓ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun v => iform γ γ * iform v δ - iform δ γ * iform v γ
      map_zero' := by
        have h1 := iform_smul_left (τ := τ) 0 0 δ
        have h2 := iform_smul_left (τ := τ) 0 0 γ
        simp only [smul_zero, zero_mul] at h1 h2
        rw [h1, h2]
        ring
      map_add' := fun u v => by
        rw [iform_add_left, iform_add_left]
        ring }
  have hℓγ : ℓ γ = 0 := by
    change iform γ γ * iform γ δ - iform δ γ * iform γ γ = 0
    rw [iform_comm δ γ]
    ring
  have hℓδ : ℓ δ ≠ 0 := by
    change iform γ γ * iform δ δ - iform δ γ * iform δ γ ≠ 0
    have h := iform_sq_lt hδ hγ hne hne'
    nlinarith
  intro hle
  have hmem : pinnedX τ K δ 1 ∈ gradingSubgroup K ℓ :=
    rootSubgroup_sup_le_gradingSubgroup ℓ hγ hℓγ (hle (Subgroup.subset_closure ⟨1, rfl⟩))
  exact pinnedX_one_not_mem_gradingSubgroup ℓ hδ hℓδ hmem

end Grading

end CFSG.ClassicalInvolution.ModelFacts
