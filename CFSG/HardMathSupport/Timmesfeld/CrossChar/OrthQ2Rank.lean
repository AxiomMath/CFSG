module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Iso

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

section Rank

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem finrank_range_add_of_orth [FiniteDimensional K V] {A B : Module.End K V}
    (hA : ∀ v, A (A v) = A v) (hAB : ∀ v, A (B v) = 0) (hBA : ∀ v, B (A v) = 0)
    (hB : ∀ v, B (B v) = B v) :
    finrank K (LinearMap.range (A + B)) =
      finrank K (LinearMap.range A) + finrank K (LinearMap.range B) := by
  have hsup : LinearMap.range (A + B) = LinearMap.range A ⊔ LinearMap.range B := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        exact ⟨A v, by rw [LinearMap.add_apply, hA, hBA, add_zero]⟩
      · rintro _ ⟨v, rfl⟩
        exact ⟨B v, by rw [LinearMap.add_apply, hB, hAB, zero_add]⟩
  have hinf : LinearMap.range A ⊓ LinearMap.range B = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rw [Submodule.mem_bot]
    calc A a = A (A a) := (hA a).symm
      _ = A (B b) := by rw [hb]
      _ = 0 := hAB b
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A) (LinearMap.range B)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  exact h

variable {ι : Type*} [DecidableEq ι] (P : ι → Module.End K V)

omit [DecidableEq ι] in
theorem sum_apply_sum_of_orth (s : Finset ι) (hP : ∀ i ∈ s, ∀ v, P i (P i v) = P i v)
    (hPP : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ v, P i (P j v) = 0) (v : V) :
    (∑ i ∈ s, P i) ((∑ i ∈ s, P i) v) = (∑ i ∈ s, P i) v := by
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_sum, Finset.sum_eq_single i (fun j hj hji => hPP i hi j hj (Ne.symm hji) v)
    (fun h => absurd hi h)]
  exact hP i hi v

theorem finrank_range_sum_of_orth [FiniteDimensional K V] (s : Finset ι)
    (hP : ∀ i ∈ s, ∀ v, P i (P i v) = P i v)
    (hPP : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ v, P i (P j v) = 0) :
    finrank K (LinearMap.range (∑ i ∈ s, P i)) = ∑ i ∈ s, finrank K (LinearMap.range (P i)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    show finrank K (LinearMap.range (0 : V →ₗ[K] V)) = 0
    rw [LinearMap.range_zero, finrank_bot]
  | insert a s ha ih =>
    have hP' : ∀ i ∈ s, ∀ v, P i (P i v) = P i v := fun i hi => hP i (Finset.mem_insert_of_mem hi)
    have hPP' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ v, P i (P j v) = 0 := fun i hi j hj =>
      hPP i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih hP' hPP']
    refine finrank_range_add_of_orth (hP a (Finset.mem_insert_self a s)) (fun v => ?_)
      (fun v => ?_) (sum_apply_sum_of_orth P s hP' hPP')
    · rw [LinearMap.sum_apply, map_sum]
      exact Finset.sum_eq_zero fun j hj => hPP a (Finset.mem_insert_self a s) j
        (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj)) v
    · rw [LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun i hi => hPP i (Finset.mem_insert_of_mem hi) a
        (Finset.mem_insert_self a s) (fun h => ha (h ▸ hi)) v

end Rank

theorem two_smul_eq_zero (K : Type*) [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module K V] (v : V) : v + v = 0 := by
  rw [← two_nsmul]
  exact two_nsmul_eq_zero' (K := K) v

section Iso

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : Multiplicative Z3 →* Module.End K V)

theorem isoP_isoP {φ : Z3} (hφ : φ ∈ Rset) (v : V) : isoP ρ φ (isoP ρ φ v) = isoP ρ φ v := by
  simp only [isoP, LinearMap.add_apply, map_add, eN_eN ρ hφ, eN_e0 ρ φ hφ, e0_eN ρ φ hφ, e0_e0]
  rw [show eN ρ φ v + e0 ρ v + (e0 ρ v + e0 ρ v) = eN ρ φ v + e0 ρ v by
    rw [two_smul_eq_zero K, add_zero]]

theorem e0_isoP {φ : Z3} (hφ : φ ∈ Rset) (v : V) : e0 ρ (isoP ρ φ v) = 0 := by
  simp only [isoP, LinearMap.add_apply, map_add, e0_eN ρ φ hφ, e0_e0]
  exact two_smul_eq_zero K _

theorem isoP_e0 {φ : Z3} (hφ : φ ∈ Rset) (v : V) : isoP ρ φ (e0 ρ v) = 0 := by
  simp only [isoP, LinearMap.add_apply, eN_e0 ρ φ hφ, e0_e0]
  exact two_smul_eq_zero K _

theorem isoP_isoP_of_ne {φ ψ : Z3} (hφ : φ ∈ Rset) (hψ : ψ ∈ Rset) (hne : φ ≠ ψ) (v : V) :
    isoP ρ φ (isoP ρ ψ v) = 0 := by
  simp only [isoP, LinearMap.add_apply, map_add, eN_eN_of_ne ρ hφ hψ hne, eN_e0 ρ φ hφ,
    e0_eN ρ ψ hψ, e0_e0]
  rw [two_smul_eq_zero K]

theorem e0_add_sum_isoP (v : V) : e0 ρ v + ∑ φ ∈ Rset, isoP ρ φ v = v := by
  have h1 := sum_eN (K := K) ρ v
  simp only [isoP, LinearMap.add_apply, Finset.sum_add_distrib, Finset.sum_const]
  rw [h1]
  have h13 : Rset.card = 13 := by decide
  rw [h13, odd_smul (K := K) (by decide), add_comm, add_assoc, two_smul_eq_zero K,
    add_zero]

theorem eCyc_isoP (φ x : Z3) (v : V) :
    eCyc ρ x (isoP ρ φ v) = if dot φ x = 0 then isoP ρ φ v else 0 := by
  have he0 : eCyc ρ x (e0 ρ v) = e0 ρ v := eCyc_of_mem ρ (e0_mem_fixOf ρ _ v)
  split_ifs with hx
  · refine eCyc_of_mem ρ fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp only [isoP, LinearMap.add_apply, map_add]
    rw [eN_mem_fixOf ρ φ v y (by simpa [dot_comm] using hx), act_e0]
  · simp only [isoP, LinearMap.add_apply, map_add, eCyc_eN_of_ne ρ hx, he0]
    exact two_smul_eq_zero K _

theorem eCyc_eq_sum_isoP (x : Z3) (v : V) :
    eCyc ρ x v = e0 ρ v + ∑ φ ∈ Rset.filter (fun φ => dot φ x = 0), isoP ρ φ v := by
  conv_lhs => rw [← e0_add_sum_isoP ρ v]
  rw [map_add, map_sum, eCyc_of_mem ρ (e0_mem_fixOf ρ _ v), Finset.sum_filter]
  congr 1
  exact Finset.sum_congr rfl fun φ _ => eCyc_isoP ρ φ x v

theorem range_e0 : LinearMap.range (e0 ρ) = fixOf ρ Set.univ := by
  refine le_antisymm ?_ fun v hv => ⟨v, e0_of_mem ρ hv⟩
  rintro _ ⟨v, rfl⟩
  exact e0_mem_fixOf ρ _ v

theorem range_eCyc (x : Z3) : LinearMap.range (eCyc ρ x) = fixOf ρ {x} := by
  refine le_antisymm ?_ fun v hv => ⟨v, eCyc_of_mem ρ hv⟩
  rintro _ ⟨v, rfl⟩
  exact eCyc_mem_fixOf ρ x v

variable [FiniteDimensional K V]

theorem finrank_range_e0_add_sum (s : Finset Z3) (hs : s ⊆ Rset) :
    finrank K (LinearMap.range (e0 ρ + ∑ φ ∈ s, isoP ρ φ)) =
      finrank K (LinearMap.range (e0 ρ)) + ∑ φ ∈ s, finrank K (LinearMap.range (isoP ρ φ)) := by
  have hP : ∀ φ ∈ s, ∀ v, isoP ρ φ (isoP ρ φ v) = isoP ρ φ v := fun φ hφ =>
    isoP_isoP ρ (hs hφ)
  have hPP : ∀ φ ∈ s, ∀ ψ ∈ s, φ ≠ ψ → ∀ v, isoP ρ φ (isoP ρ ψ v) = 0 := fun φ hφ ψ hψ hne =>
    isoP_isoP_of_ne ρ (hs hφ) (hs hψ) hne
  rw [finrank_range_add_of_orth (e0_e0 ρ) (fun v => ?_) (fun v => ?_)
    (sum_apply_sum_of_orth (isoP ρ) s hP hPP), finrank_range_sum_of_orth (isoP ρ) s hP hPP]
  · rw [LinearMap.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun φ hφ => e0_isoP ρ (hs hφ) v
  · rw [LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun φ hφ => isoP_e0 ρ (hs hφ) v

theorem finrank_eq_sum_isoP :
    finrank K V = finrank K (LinearMap.range (e0 ρ)) +
      ∑ φ ∈ Rset, finrank K (LinearMap.range (isoP ρ φ)) := by
  rw [← finrank_range_e0_add_sum ρ Rset subset_rfl]
  have h : e0 ρ + ∑ φ ∈ Rset, isoP ρ φ = LinearMap.id := by
    ext v
    rw [LinearMap.add_apply, LinearMap.sum_apply, e0_add_sum_isoP, LinearMap.id_apply]
  rw [h, LinearMap.range_id, finrank_top]

theorem finrank_fixOf_single_eq (x : Z3) :
    finrank K (fixOf ρ {x}) = finrank K (LinearMap.range (e0 ρ)) +
      ∑ φ ∈ Rset.filter (fun φ => dot φ x = 0), finrank K (LinearMap.range (isoP ρ φ)) := by
  rw [← finrank_range_e0_add_sum ρ _ (Finset.filter_subset _ _), ← range_eCyc ρ x]
  have h : eCyc ρ x = e0 ρ + ∑ φ ∈ Rset.filter (fun φ => dot φ x = 0), isoP ρ φ := by
    ext v
    rw [LinearMap.add_apply, LinearMap.sum_apply, eCyc_eq_sum_isoP]
  rw [h]

theorem finrank_fixOf_N_eq {φ : Z3} (hφ : φ ∈ Rset) :
    finrank K (fixOf ρ {x | dot φ x = 0}) = finrank K (LinearMap.range (e0 ρ)) +
      finrank K (LinearMap.range (isoP ρ φ)) := by
  rw [← range_eN ρ hφ]
  have h := finrank_range_e0_add_sum ρ {φ} (Finset.singleton_subset_iff.2 hφ)
  rw [Finset.sum_singleton, Finset.sum_singleton] at h
  rw [← h]
  have h' : eN ρ φ = e0 ρ + isoP ρ φ := by
    ext v
    rw [isoP, LinearMap.add_apply, LinearMap.add_apply, add_comm (eN ρ φ v), ← add_assoc,
      two_smul_eq_zero K, zero_add]
  rw [h']

end Iso

end CFSG.HardMathSupport.Timmesfeld.CrossChar
