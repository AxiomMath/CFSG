module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherReducedWord
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBruhat

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

@[expose] noncomputable def reflElt (n : ℕ) (K : Type*) [Field K] (j : ℕ) :
    SpecialLinearGroup (Fin n) K :=
  if h : 1 ≤ j ∧ j < n then reflection n K j h.1 h.2 else 1

theorem reflElt_of_lt {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    reflElt n K j = reflection n K j hj hjn :=
  dite_eq_left ⟨hj, hjn⟩

theorem isMonomial_reflElt (j : ℕ) :
    IsMonomial ((reflElt n K j : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (adjSwap n j) := by
  by_cases h : 1 ≤ j ∧ j < n
  · rw [reflElt_of_lt h.1 h.2, coe_reflection]
    exact isMonomial_reflection j h.1 h.2
  · rw [reflElt, dite_eq_right h, adjSwap, dite_eq_right h, SpecialLinearGroup.coe_one]
    exact ⟨fun _ => 1, fun j => by rw [one_mulVec, Units.val_one, one_smul, Equiv.Perm.one_apply]⟩

theorem isMonomial_prod_reflElt (l : List ℕ) :
    IsMonomial ((((l.map (reflElt n K)).prod : SpecialLinearGroup (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) (adjWordProd n l) := by
  induction l with
  | nil =>
    exact ⟨fun _ => 1, fun j => by
      rw [List.map_nil, List.prod_nil, SpecialLinearGroup.coe_one, one_mulVec, Units.val_one,
        one_smul, adjWordProd, List.map_nil, List.prod_nil, Equiv.Perm.one_apply]⟩
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, SpecialLinearGroup.coe_mul, adjWordProd_cons]
    exact (isMonomial_reflElt j).mul ih

theorem mem_stabilizer_of_map_le {g : SpecialLinearGroup (Fin n) K} {W : Submodule K (Fin n → K)}
    (h : W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) ≤ W) : g ∈ stabilizer W := by
  rw [mem_stabilizer]
  refine Submodule.eq_of_le_of_finrank_eq h ?_
  exact LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) W

theorem map_flagSpace_le_of_isMonomial {M : Matrix (Fin n) (Fin n) K} {σ : Equiv.Perm (Fin n)}
    (hM : IsMonomial M σ) {i : ℕ} (hσ : ∀ c : Fin n, (c : ℕ) < i → (σ c : ℕ) < i) :
    (flagSpace n K i).map (mulVecLin M) ≤ flagSpace n K i := by
  obtain ⟨d, hd⟩ := hM
  rw [flagSpace, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  rw [mulVecLin_apply, hd]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ c, hσ c hc, rfl⟩)

theorem lt_of_isMonomial_of_map_le {M : Matrix (Fin n) (Fin n) K} {σ : Equiv.Perm (Fin n)}
    (hM : IsMonomial M σ) {i : ℕ} (h : (flagSpace n K i).map (mulVecLin M) ≤ flagSpace n K i)
    (c : Fin n) (hc : (c : ℕ) < i) : (σ c : ℕ) < i := by
  obtain ⟨d, hd⟩ := hM
  have hmem : M *ᵥ Pi.single c 1 ∈ flagSpace n K i :=
    h ⟨_, Submodule.subset_span ⟨c, hc, rfl⟩, rfl⟩
  rw [hd, mem_flagSpace] at hmem
  by_contra hlt
  have := hmem (σ c) (not_lt.mp hlt)
  simp [(d c).ne_zero] at this

theorem reflection_mem_stabilizer_of_ne {i j : ℕ} (hj : 1 ≤ j) (hjn : j < n) (hij : i ≠ j) :
    reflection n K j hj hjn ∈ stabilizer (flagSpace n K i) := by
  refine mem_stabilizer_of_map_le ?_
  rw [coe_reflection]
  refine map_flagSpace_le_of_isMonomial (isMonomial_reflection j hj hjn) fun c hc => ?_
  rw [adjSwap_of_lt hj hjn, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · have : (c : ℕ) = j - 1 := congrArg Fin.val h1
    show j < i
    omega
  · have : (c : ℕ) = j := congrArg Fin.val h2
    show j - 1 < i
    omega
  · exact hc

theorem upperTriangular_le_flagStabilizer (I : Set ℕ) :
    upperTriangular n K ≤ flagStabilizer n K I := fun b hb =>
  mem_flagStabilizer.mpr fun i _ => mem_stabilizer_of_map_le (by
    rintro _ ⟨v, hv, rfl⟩
    exact flagSpace_invariant i hb hv)

theorem exists_adjWord_of_preserves (I : Set ℕ) :
    ∀ σ : Equiv.Perm (Fin n), (∀ i ∈ I, ∀ c : Fin n, (c : ℕ) < i → (σ c : ℕ) < i) →
      ∃ l : List ℕ, (∀ j ∈ l, 1 ≤ j ∧ j < n ∧ j ∉ I) ∧ adjWordProd n l = σ := by
  classical
  intro σ
  induction h : inversionCount σ using Nat.strong_induction_on generalizing σ with
  | _ m ih =>
    intro hσ
    by_cases hσ1 : σ = 1
    · exact ⟨[], fun _ h => absurd h List.not_mem_nil, by rw [hσ1]; rfl⟩
    obtain ⟨i₀, hi, hin, hdesc⟩ := exists_descent hσ1
    set x : Fin n := ⟨i₀ - 1, by omega⟩ with hx
    set y : Fin n := ⟨i₀, hin⟩ with hy
    have hcut : i₀ ∉ I := by
      intro hI
      set S := Finset.univ.filter fun c : Fin n => (c : ℕ) < i₀
      have himage : S.image σ = S := by
        refine Finset.eq_of_subset_of_card_le (fun c hc => ?_) ?_
        · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hσ i₀ hI c' (Finset.mem_filter.mp hc').2⟩
        · rw [Finset.card_image_of_injective _ σ.injective]
      have hxS : x ∈ S.image σ := by
        rw [himage]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hx]; omega⟩
      obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp hxS
      have h1 : (σ⁻¹ x : ℕ) < i₀ := by
        rw [← hcx, perm_inv_apply]
        exact (Finset.mem_filter.mp hc).2
      have h2 : i₀ ≤ (σ⁻¹ y : ℕ) := by
        by_contra hlt
        have := hσ i₀ hI (σ⁻¹ y) (not_le.mp hlt)
        rw [perm_apply_inv] at this
        simp [hy] at this
      have h3 : (σ⁻¹ y : ℕ) < (σ⁻¹ x : ℕ) := hdesc
      omega
    have hσ' : ∀ i ∈ I, ∀ c : Fin n, (c : ℕ) < i → ((adjSwap n i₀ * σ) c : ℕ) < i := by
      intro i hiI c hc
      have hic : i ≠ i₀ := fun h => hcut (h ▸ hiI)
      have hσc := hσ i hiI c hc
      rw [Equiv.Perm.mul_apply, adjSwap_of_lt hi hin, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · have : ((σ c : Fin n) : ℕ) = i₀ - 1 := congrArg Fin.val h1
        show i₀ < i
        omega
      · have : ((σ c : Fin n) : ℕ) = i₀ := congrArg Fin.val h2
        show i₀ - 1 < i
        omega
      · exact hσc
    have hcount := (inversionCount_adjSwap_mul hi hin σ).1 hdesc
    obtain ⟨l, hl, hprod⟩ := ih _ (by omega) (adjSwap n i₀ * σ) rfl hσ'
    refine ⟨i₀ :: l, fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨hi, hin, hcut⟩
      · exact hl j hj
    · rw [adjWordProd_cons, hprod, ← mul_assoc, adjSwap_mul_self, one_mul]

@[expose] def subflagGenerators (n : ℕ) (K : Type*) [Field K] (I : Set ℕ) :
    Set (SpecialLinearGroup (Fin n) K) :=
  (upperTriangular n K : Set (SpecialLinearGroup (Fin n) K)) ∪
    {g | ∃ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n), j ∉ I ∧ reflection n K j hj hjn = g}

theorem subflag_stabilizer_generation (I : Set ℕ) :
    flagStabilizer n K I = Subgroup.closure (subflagGenerators n K I) ∧
    (∀ W : Submodule K (Fin n → K),
      (∀ g ∈ flagStabilizer n K I, ∀ v ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) ↔
        W = ⊥ ∨ W = ⊤ ∨ ∃ i ∈ I, W = flagSpace n K i) ∧
    (∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n),
      reflection n K j hj hjn ∈ flagStabilizer n K I ↔ j ∉ I) := by
  classical
  have hrefl : ∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n), j ∉ I →
      reflection n K j hj hjn ∈ flagStabilizer n K I := fun j hj hjn hjI =>
    mem_flagStabilizer.mpr fun i hi =>
      reflection_mem_stabilizer_of_ne hj hjn (fun h => hjI (h ▸ hi))
  have hmove : ∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n),
      reflection n K j hj hjn ∉ stabilizer (flagSpace n K j) := by
    intro j hj hjn hmem
    have hle : (flagSpace n K j).map (mulVecLin ((reflection n K j hj hjn :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≤ flagSpace n K j :=
      (mem_stabilizer.mp hmem).le
    rw [coe_reflection] at hle
    have := lt_of_isMonomial_of_map_le (isMonomial_reflection j hj hjn) hle
      ⟨j - 1, by omega⟩ (by simp; omega)
    rw [adjSwap_of_lt hj hjn, Equiv.swap_apply_left] at this
    simp at this
  have hgen : flagStabilizer n K I = Subgroup.closure (subflagGenerators n K I) := by
    refine le_antisymm (fun g hg => ?_) ?_
    · obtain ⟨w, hw⟩ := (triangular_bruhat (K := K) (n := n)).1 g
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
      have hBI := upperTriangular_le_flagStabilizer (K := K) (n := n) I
      have hwI : signedPermutation n K w ∈ flagStabilizer n K I := by
        have := mul_mem (mul_mem (inv_mem (hBI hb₁)) hg) (inv_mem (hBI hb₂))
        convert this using 1
        group
      have hσ : ∀ i ∈ I, ∀ c : Fin n, (c : ℕ) < i → (w c : ℕ) < i := by
        intro i hi c hc
        have h := (mem_stabilizer.mp (mem_flagStabilizer.mp hwI i hi)).le
        rw [coe_signedPermutation] at h
        exact lt_of_isMonomial_of_map_le (isMonomial_signedPermMatrix w) h c hc
      obtain ⟨l, hl, hprod⟩ := exists_adjWord_of_preserves I w hσ
      set ρ := (l.map (reflElt n K)).prod with hρ
      have hρmem : ρ ∈ Subgroup.closure (subflagGenerators n K I) := by
        rw [hρ]
        refine Subgroup.list_prod_mem _ fun x hx => ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hj1, hjn, hjI⟩ := hl j hj
        rw [reflElt_of_lt hj1 hjn]
        exact Subgroup.subset_closure (Or.inr ⟨j, hj1, hjn, hjI, rfl⟩)
      have hρmono := isMonomial_prod_reflElt (K := K) (n := n) l
      rw [hprod] at hρmono
      obtain ⟨D, hD, hwD⟩ := IsMonomial.exists_diagonal (M := signedPermutation n K w)
        (M' := ρ) (isMonomial_signedPermMatrix w) hρmono
      have hBcl : ∀ b ∈ upperTriangular n K, b ∈ Subgroup.closure (subflagGenerators n K I) :=
        fun b hb => Subgroup.subset_closure (Or.inl hb)
      rw [hwD]
      exact mul_mem (mul_mem (hBcl b₁ hb₁) (mul_mem hρmem (hBcl D hD))) (hBcl b₂ hb₂)
    · rw [Subgroup.closure_le]
      rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
      · exact upperTriangular_le_flagStabilizer I hg
      · exact hrefl j hj hjn hjI
  refine ⟨hgen, fun W => ⟨fun hW => ?_, ?_⟩, fun j hj hjn => ⟨fun hmem hjI => ?_,
    hrefl j hj hjn⟩⟩
  ·
    obtain ⟨d, hd, rfl⟩ := eq_flagSpace_of_invariant (K := K) (n := n) fun u hu v hv =>
      hW u (upperTriangular_le_flagStabilizer I (unitriangular_le_upperTriangular n K hu)) v hv
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact Or.inl (flagSpace_zero n K)
    rcases eq_or_lt_of_le hd with rfl | hdn
    · refine Or.inr (Or.inl ?_)
      rw [eq_top_iff]
      intro v _
      rw [mem_flagSpace]
      intro j hj
      exact absurd j.isLt (not_lt.mpr hj)
    · refine Or.inr (Or.inr ⟨d, ?_, rfl⟩)
      by_contra hdI
      apply hmove d hd0 hdn
      refine mem_stabilizer_of_map_le ?_
      rintro _ ⟨v, hv, rfl⟩
      exact hW _ (hrefl d hd0 hdn hdI) v hv
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩) g hg v hv
    · rw [Submodule.mem_bot] at hv ⊢
      rw [hv, mulVec_zero]
    · exact Submodule.mem_top
    · have h := mem_stabilizer.mp (mem_flagStabilizer.mp hg i hi)
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · exact hmove j hj hjn (mem_flagStabilizer.mp hmem j hjI)

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
