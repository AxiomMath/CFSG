module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4Compat

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3.D4

open CFSG.Blueprint.Chevalley Matrix

variable (K : Type) [Field K]

theorem ker_root_witness_fin : ∀ α ∈ d4Roots, ∃ p : Fin 8 × Fin 8,
    (phiRootZ α p.1 p.2 = 1 ∨ phiRootZ α p.1 p.2 = -1) ∧
      (∀ β ∈ d4Roots, β ≠ α → phiRootZ β p.1 p.2 = 0) ∧ ∀ j : Fin 4, HZ j p.1 p.2 = 0 := by
  decide +kernel

theorem ker_root_witness (α : Fin 4 → ℤ) (hα : α ∈ d4Roots) : ∃ r s : Fin 8,
    (phiRootZ α r s = 1 ∨ phiRootZ α r s = -1) ∧
      (∀ β ∈ d4Roots, β ≠ α → phiRootZ β r s = 0) ∧ ∀ j : Fin 4, HZ j r s = 0 := by
  obtain ⟨⟨r, s⟩, h⟩ := ker_root_witness_fin α hα
  exact ⟨r, s, h⟩

theorem ker_HZ_diagonal_entries : (HZ 0 0 4 = 1 ∧ HZ 1 0 4 = 0 ∧ HZ 2 0 4 = 0 ∧ HZ 3 0 4 = 0) ∧
    (HZ 0 1 5 = -1 ∧ HZ 1 1 5 = 0 ∧ HZ 2 1 5 = -1 ∧ HZ 3 1 5 = 0) ∧
    (HZ 0 2 6 = 0 ∧ HZ 1 2 6 = 1 ∧ HZ 2 2 6 = 1 ∧ HZ 3 2 6 = 1) ∧
    (HZ 0 3 7 = 0 ∧ HZ 1 3 7 = -1 ∧ HZ 2 3 7 = 0 ∧ HZ 3 3 7 = 1) := by
  decide +kernel

@[expose] def ker_labH (j : Fin 4) : Label Tag.D4 := Sum.inl (Fin.cast rfl j)

theorem ker_labH_injective : Function.Injective ker_labH := by
  intro a b h
  exact Fin.ext (congrArg Fin.val (Sum.inl.inj h))

theorem ker_labH_inj (a b : Fin 4) : ker_labH a = ker_labH b ↔ a = b :=
  ker_labH_injective.eq_iff

theorem ker_hVec_eq_labH (i : Fin 4) : hVec Tag.D4 K i = Finsupp.single (ker_labH i) 1 :=
  rfl

theorem ker_castM_apply (M : M8) (r s : Fin 8) : castM K M r s = ((M r s : ℤ) : K) := by
  simp [castM]

theorem ker_phiLabel_inl (j : Fin Tag.D4.rank) (r s : Fin 8) :
    phiLabel K (Sum.inl j) r s = ((HZ j r s : ℤ) : K) :=
  ker_castM_apply K (HZ j) r s

theorem ker_phiLabel_inr (β : Fin Tag.D4.rank → ℤ) (hβ : IsRoot Tag.D4 β) (r s : Fin 8) :
    phiLabel K (Sum.inr ⟨β, hβ⟩) r s = ((phiRootZ β r s : ℤ) : K) :=
  ker_castM_apply K (phiRootZ β) r s

theorem ker_phi_apply (v : RootModule Tag.D4 K) (r s : Fin 8) :
    phi K v r s = ∑ b ∈ v.support, v b * phiLabel K b r s := by
  simp only [phi, Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem ker_root_coord_zero {v : RootModule Tag.D4 K} (hv : phi K v = 0) {α : Fin Tag.D4.rank → ℤ}
    (hα : IsRoot Tag.D4 α) : v (Sum.inr ⟨α, hα⟩) = 0 := by
  obtain ⟨r, s, hunit, hother, hHZ⟩ := ker_root_witness α (isRoot_D4_iff.1 hα)
  have hsum : ∑ b ∈ v.support, v b * phiLabel K b r s = 0 := by
    rw [← ker_phi_apply, hv]
    rfl
  have h₀ : ∀ b ∈ v.support, b ≠ Sum.inr ⟨α, hα⟩ → v b * phiLabel K b r s = 0 := by
    rintro (j | ⟨β, hβ⟩) - hne
    · rw [ker_phiLabel_inl, hHZ j]
      simp
    · have hβα : β ≠ α := fun h => hne (by subst h; rfl)
      rw [ker_phiLabel_inr, hother β (isRoot_D4_iff.1 hβ) hβα]
      simp
  have h₁ : Sum.inr ⟨α, hα⟩ ∉ v.support →
      v (Sum.inr ⟨α, hα⟩) * phiLabel K (Sum.inr ⟨α, hα⟩) r s = 0 := by
    intro hnot
    rw [Finsupp.notMem_support_iff.1 hnot, zero_mul]
  rw [Finset.sum_eq_single (Sum.inr ⟨α, hα⟩) h₀ h₁, ker_phiLabel_inr] at hsum
  have hne : ((phiRootZ α r s : ℤ) : K) ≠ 0 := by
    rcases hunit with h1 | h1 <;> simp [h1]
  exact (mul_eq_zero.1 hsum).resolve_right hne

theorem ker_phi_eq_sum {v : RootModule Tag.D4 K}
    (hR : ∀ {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α), v (Sum.inr ⟨α, hα⟩) = 0) :
    phi K v = ∑ j : Fin 4, v (ker_labH j) • castM K (HZ j) := by
  have hsub : v.support ⊆ Finset.univ.map ⟨ker_labH, ker_labH_injective⟩ := by
    rintro (j | ⟨α, hα⟩) hb
    · exact Finset.mem_map.2 ⟨Fin.cast rfl.symm j, Finset.mem_univ _, rfl⟩
    · exact absurd (hR hα) (Finsupp.mem_support_iff.1 hb)
  rw [phi, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset v hsub _ (fun _ _ => by simp), Finset.sum_map]
  rfl

theorem ker_coords_eq {v : RootModule Tag.D4 K} (hv : phi K v = 0)
    (hR : ∀ {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α), v (Sum.inr ⟨α, hα⟩) = 0) :
    v (ker_labH 0) = 0 ∧ v (ker_labH 2) = 0 ∧ v (ker_labH 3) = v (ker_labH 1) := by
  have hsum := ker_phi_eq_sum K hR
  rw [hv] at hsum
  have e : ∀ r s : Fin 8, ∑ j : Fin 4, v (ker_labH j) * ((HZ j r s : ℤ) : K) = 0 := by
    intro r s
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) K => M r s) hsum
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ker_castM_apply,
      Matrix.zero_apply] at h
    exact h.symm
  obtain ⟨d0, d1, d2, d3⟩ := ker_HZ_diagonal_entries
  have e04 := e 0 4
  have e15 := e 1 5
  have e26 := e 2 6
  have e37 := e 3 7
  simp only [Fin.sum_univ_four, d0.1, d0.2.1, d0.2.2.1, d0.2.2.2, d1.1, d1.2.1, d1.2.2.1,
    d1.2.2.2, d2.1, d2.2.1, d2.2.2.1, d2.2.2.2, d3.1, d3.2.1, d3.2.2.1, d3.2.2.2,
    Int.cast_one, Int.cast_zero, Int.cast_neg] at e04 e15 e26 e37
  have f0 : v (ker_labH 0) = 0 := by linear_combination e04
  have f2 : v (ker_labH 2) = 0 := by linear_combination -e15 - e04
  have f3 : v (ker_labH 3) = v (ker_labH 1) := by linear_combination e37
  exact ⟨f0, f2, f3⟩

theorem phi_ker_le_span {v : RootModule Tag.D4 K} (hv : phi K v = 0) :
    v ∈ Submodule.span K {hVec Tag.D4 K (1 : Fin 4) + hVec Tag.D4 K (3 : Fin 4)} := by
  have hR : ∀ {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α), v (Sum.inr ⟨α, hα⟩) = 0 :=
    fun hα => ker_root_coord_zero K hv hα
  obtain ⟨h0, h2, h31⟩ := ker_coords_eq K hv hR
  have key4 : ∀ j : Fin 4, v (ker_labH j) =
      (v (ker_labH 1) • (hVec Tag.D4 K (1 : Fin 4) + hVec Tag.D4 K (3 : Fin 4))) (ker_labH j) := by
    intro j
    simp only [ker_hVec_eq_labH, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply,
      ker_labH_inj, smul_eq_mul]
    fin_cases j
    · simpa using h0
    · simp
    · simpa using h2
    · simpa using h31
  have key : v = v (ker_labH 1) • (hVec Tag.D4 K (1 : Fin 4) + hVec Tag.D4 K (3 : Fin 4)) := by
    ext a
    rcases a with j | ⟨α, hα⟩
    · exact key4 (Fin.cast rfl.symm j)
    · simp [hVec, Finsupp.single_apply, hR hα]
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end CFSG.ComponentClassification.CatFC.KGHS3.D4
