module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFamily
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def BlockNF (w : Fin d → K) (I : Finset (Fin d)) : Prop :=
  ∃ I₀ ⊆ I, 3 ≤ I₀.card ∧ (∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j) ∧
    ∀ x ∈ I, ∀ y ∈ I, x ∉ I₀ → y ∉ I₀ → x = y

omit [Field K] in
theorem BlockNF.blockOK {w : Fin d → K} {I : Finset (Fin d)} (h : BlockNF w I)
    (h3 : 3 ≤ I.card) (hexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4)) : BlockOK K w I :=
  ⟨h3, hexc, h⟩

omit [Field K] in
theorem BlockNF.exists_triple {w : Fin d → K} {I : Finset (Fin d)} (h : BlockNF w I) :
    ∃ x ∈ I, ∃ y ∈ I, ∃ z ∈ I, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ w x = w y ∧ w x = w z := by
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, -⟩ := h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 (by omega : 2 < I₀.card)
  exact ⟨x, hI₀ hx, y, hI₀ hy, z, hI₀ hz, hxy, hxz, hyz, hI₀w x hx y hy, hI₀w x hx z hz⟩

theorem blockNF_of_orthNF {m : ℕ} {e : Fin m → Fin d} (he : Function.Injective e)
    {w : Fin d → K} {I : Finset (Fin d)} (hI : ∀ x, x ∈ I ↔ ∃ i, e i = x)
    (hNF : OrthNF (w ∘ e)) : BlockNF w I := by
  obtain ⟨-, I', hI'3, hI'c, hI'w⟩ := hNF
  refine ⟨I'.map ⟨e, he⟩, ?_, by rw [Finset.card_map]; exact hI'3, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact (hI _).2 ⟨i, rfl⟩
  · intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hy
    exact hI'w i hi j hj
  · intro x hx y hy hx' hy'
    obtain ⟨i, rfl⟩ := (hI x).1 hx
    obtain ⟨j, rfl⟩ := (hI y).1 hy
    have hi : i ∉ I' := fun h => hx' (Finset.mem_map.2 ⟨i, h, rfl⟩)
    have hj : j ∉ I' := fun h => hy' (Finset.mem_map.2 ⟨j, h, rfl⟩)
    rw [hI'c i j hi hj]

theorem mem_famJ_iff {a b : ℕ} (hab : a + b = d) (x : Fin d) :
    x ∈ famJ hab ↔ ∃ i, sumFin hab (.inl i) = x := by
  obtain ⟨y, rfl⟩ := (sumFin hab).surjective x
  simp only [famJ, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rcases y with i | j <;> simp

theorem mem_famJ_compl_iff {a b : ℕ} (hab : a + b = d) (x : Fin d) :
    x ∈ (famJ hab)ᶜ ↔ ∃ j, sumFin hab (.inr j) = x := by
  obtain ⟨y, rfl⟩ := (sumFin hab).surjective x
  simp only [famJ, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases y with i | j <;> simp

variable [Finite K]

theorem exists_split_nf (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {A : Matrix (Fin d) (Fin d) K}
    (hAR : Aᵀ * (R : Matrix (Fin d) (Fin d) K) * A = R) (hA2 : A * A = 1) :
    ∃ (hab : Module.finrank K (eigM A) + Module.finrank K (eigP A) = d)
      (c : Fin (Module.finrank K (eigM A)) ⊕ Fin (Module.finrank K (eigP A)) → Fin d → K),
      (∀ x, A *ᵥ c x = (if x.isLeft then (-1 : K) else 1) • c x) ∧
      (∀ x y, x ≠ y → c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c y = 0) ∧
      (∀ x, c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x ≠ 0) ∧
      (3 ≤ Module.finrank K (eigM A) →
        BlockNF (famW (R : Matrix (Fin d) (Fin d) K) hab c) (famJ hab)) ∧
      (3 ≤ Module.finrank K (eigP A) →
        BlockNF (famW (R : Matrix (Fin d) (Fin d) K) hab c) (famJ hab)ᶜ) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set a := Module.finrank K (eigM A) with ha
  set b := Module.finrank K (eigP A) with hb
  have hab : a + b = d := finrank_eig_add h2 hA2
  set uM := Module.finBasisOfFinrankEq K (eigM A) ha.symm with huM
  set uP := Module.finBasisOfFinrankEq K (eigP A) hb.symm with huP
  obtain ⟨cM, hcM, horthM, hdiagM, hNFM⟩ := exists_family_of_basis hK hR
    (nondeg_eig h2 hR hAR hA2 (Or.inr rfl)) uM
  obtain ⟨cP, hcP, horthP, hdiagP, hNFP⟩ := exists_family_of_basis hK hR
    (nondeg_eig h2 hR hAR hA2 (Or.inl rfl)) uP
  set c : Fin a ⊕ Fin b → Fin d → K := Sum.elim cM cP with hc
  have hfam : ∀ x, famW (R : Matrix (Fin d) (Fin d) K) hab c (sumFin hab x) =
      c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x := famW_sumFin _ hab c
  refine ⟨hab, c, ?_, ?_, ?_, fun h3 => ?_, fun h3 => ?_⟩
  · rintro (i | j)
    · simp only [hc, Sum.elim_inl, Sum.isLeft_inl, ↓reduceIte, neg_smul, one_smul]
      exact mem_eigM.1 (hcM i)
    · simp only [hc, Sum.elim_inr, Sum.isLeft_inr, Bool.false_eq_true, ↓reduceIte, one_smul]
      exact mem_eigP.1 (hcP j)
  · rintro (i | j) (i' | j') hxy
    · exact horthM i i' fun h => hxy (by rw [h])
    · simp only [hc, Sum.elim_inl, Sum.elim_inr]
      rw [dot_symm hR]
      exact orth_eig h2 hAR (hcP j') (hcM i)
    · exact orth_eig h2 hAR (hcP j) (hcM i')
    · exact horthP j j' fun h => hxy (by rw [h])
  · rintro (i | j)
    · exact hdiagM i
    · exact hdiagP j
  · refine blockNF_of_orthNF (e := fun i => sumFin hab (.inl i))
      (fun i i' h => Sum.inl_injective ((sumFin hab).injective h)) (mem_famJ_iff hab) ?_
    have hf : (famW (R : Matrix (Fin d) (Fin d) K) hab c ∘ fun i => sumFin hab (.inl i)) =
        fun i => cM i ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ cM i := funext fun i => hfam _
    rw [hf]
    exact hNFM h3
  · refine blockNF_of_orthNF (e := fun j => sumFin hab (.inr j))
      (fun j j' h => Sum.inr_injective ((sumFin hab).injective h)) (mem_famJ_compl_iff hab) ?_
    have hf : (famW (R : Matrix (Fin d) (Fin d) K) hab c ∘ fun j => sumFin hab (.inr j)) =
        fun j => cP j ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ cP j := funext fun j => hfam _
    rw [hf]
    exact hNFP h3

end CFSG.ComponentClassification.Burgoyne.O
