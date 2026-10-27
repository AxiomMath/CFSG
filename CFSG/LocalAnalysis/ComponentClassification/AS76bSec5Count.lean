module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Sigma
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Arith

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

theorem sum_pair {H : Type} [AddGroup H] [Fintype H] (y : H) (g : Bool → Bool → ℕ)
    (hH : 2 ≤ Nat.card H) :
    ∑ x : H, g (nz x) (nz (x + y)) = E (nz y) (Nat.card H - 2) g := by
  classical
  have hsum : ∀ (s : Finset H) (c : ℕ), (∀ x ∈ s, g (nz x) (nz (x + y)) = c) →
      ∑ x ∈ s, g (nz x) (nz (x + y)) = s.card * c := fun s c hc => by
    rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
  rw [Nat.card_eq_fintype_card] at hH ⊢
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : H))]
  by_cases hy : y = 0
  · subst hy
    rw [hsum _ (g true true) fun x hx => by
        rw [add_zero, nz_of_ne (Finset.ne_of_mem_erase hx)],
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp only [add_zero, nz_zero, E, Bool.false_eq_true, ↓reduceIte]
    rw [show Fintype.card H - 2 + 1 = Fintype.card H - 1 by omega]
  · have hmem : -y ∈ Finset.univ.erase (0 : H) :=
      Finset.mem_erase.2 ⟨neg_ne_zero.2 hy, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hmem,
      hsum _ (g true true) fun x hx => by
        obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx
        have hx0 : x ≠ 0 := (Finset.mem_erase.1 hx2).1
        have hxy : x + y ≠ 0 := fun h0 => hx1 (eq_neg_of_add_eq_zero_left h0)
        rw [nz_of_ne hx0, nz_of_ne hxy],
      Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, zero_add, neg_add_cancel, nz_zero, nz_of_ne hy,
      nz_of_ne (neg_ne_zero.2 hy)]
    simp only [E, ↓reduceIte]
    rw [show Fintype.card H - 1 - 1 = Fintype.card H - 2 by omega, add_assoc]

theorem sum_triple {H₁ H₂ H₃ : Type} [AddGroup H₁] [AddGroup H₂] [AddGroup H₃] [Fintype H₁]
    [Fintype H₂] [Fintype H₃] (y₁ : H₁) (y₂ : H₂) (y₃ : H₃) (χ : Bool × Bool × Bool → ℕ)
    (c₁ : 2 ≤ Nat.card H₁) (c₂ : 2 ≤ Nat.card H₂) (c₃ : 2 ≤ Nat.card H₃) :
    ∑ x₁ : H₁, ∑ x₂ : H₂, ∑ x₃ : H₃,
      χ (nz x₁, nz x₂, nz x₃) * χ (nz (x₁ + y₁), nz (x₂ + y₂), nz (x₃ + y₃)) =
      E (nz y₁) (Nat.card H₁ - 2) fun σ₁ τ₁ => E (nz y₂) (Nat.card H₂ - 2) fun σ₂ τ₂ =>
        E (nz y₃) (Nat.card H₃ - 2) fun σ₃ τ₃ => χ (σ₁, σ₂, σ₃) * χ (τ₁, τ₂, τ₃) := by
  calc _ = ∑ x₁ : H₁, E (nz y₂) (Nat.card H₂ - 2) (fun σ₂ τ₂ =>
          E (nz y₃) (Nat.card H₃ - 2) fun σ₃ τ₃ =>
            χ (nz x₁, σ₂, σ₃) * χ (nz (x₁ + y₁), τ₂, τ₃)) := by
        refine Finset.sum_congr rfl fun x₁ _ => ?_
        calc _ = ∑ x₂ : H₂, E (nz y₃) (Nat.card H₃ - 2) (fun σ₃ τ₃ =>
                χ (nz x₁, nz x₂, σ₃) * χ (nz (x₁ + y₁), nz (x₂ + y₂), τ₃)) :=
              Finset.sum_congr rfl fun x₂ _ => sum_pair y₃ _ c₃
          _ = _ := sum_pair y₂ (fun σ₂ τ₂ => E (nz y₃) (Nat.card H₃ - 2) fun σ₃ τ₃ =>
              χ (nz x₁, σ₂, σ₃) * χ (nz (x₁ + y₁), τ₂, τ₃)) c₂
    _ = _ := sum_pair y₁ (fun σ₁ τ₁ => E (nz y₂) (Nat.card H₂ - 2) fun σ₂ τ₂ =>
          E (nz y₃) (Nat.card H₃ - 2) fun σ₃ τ₃ => χ (σ₁, σ₂, σ₃) * χ (τ₁, τ₂, τ₃)) c₁

variable {V : Type} [AddCommGroup V] {X : Type} [Group X] [DistribMulAction X V]

variable (X) in
@[expose] noncomputable def cnt (R : AddSubgroup V) (v : V) : ℕ :=
  Set.ncard {s : V | s ∈ fused X R ∧ s + v ∈ fused X R}

theorem cnt_smul {R : AddSubgroup V} (x : X) (v : V) : cnt X R (x • v) = cnt X R v := by
  rw [cnt, cnt, ← Set.ncard_image_of_injective {s : V | s ∈ fused X R ∧ s + v ∈ fused X R}
    (MulAction.injective x)]
  congr 1
  ext s
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨x⁻¹ • s, ⟨smul_mem_fused h1 x⁻¹, ?_⟩, by simp⟩
    rw [← smul_mem_fused_iff (x := x), smul_add, smul_inv_smul]
    exact h2
  · rintro ⟨s', ⟨h1, h2⟩, rfl⟩
    refine ⟨smul_mem_fused h1 x, ?_⟩
    rw [← smul_add]
    exact smul_mem_fused h2 x

namespace Hyp51

variable {A B : Subgroup X} {R U W : AddSubgroup V} (h : Hyp51 X A B R U W)

open scoped Classical in
@[expose] noncomputable def chi (p : Bool × Bool × Bool) : ℕ := if h.Occ p then 1 else 0

include h

variable [Finite V]

theorem cnt_eq (v : V) :
    cnt X R v = cform h.chi (h.decomp.pat v) (Nat.card R - 2) (Nat.card U - 2) := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype R := Fintype.ofFinite R
  have : Fintype U := Fintype.ofFinite U
  have : Fintype W := Fintype.ofFinite W
  have h1 : cnt X R v = ∑ s : V, h.chi (h.decomp.pat s) * h.chi (h.decomp.pat (s + v)) := by
    classical
    rw [cnt, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.univ.filter fun s => s ∈ fused X R ∧ s + v ∈ fused X R)
        (by simp), Finset.card_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [chi, ← h.mem_fused_iff_occ]
    by_cases h1 : s ∈ fused X R <;> by_cases h2 : s + v ∈ fused X R <;> simp [h1, h2]
  have h2 : cnt X R v = ∑ p : R × U × W, h.chi (h.decomp.pat (h.decomp.equiv p)) *
      h.chi (h.decomp.pat (h.decomp.equiv p + v)) := by
    rw [h1]
    symm
    refine Fintype.sum_equiv h.decomp.equiv.toEquiv _ _ fun p => ?_
    rfl
  rw [h2]
  simp only [h.decomp.pat_equiv, h.decomp.pat_equiv_add, Fintype.sum_prod_type]
  have c₁ : 2 ≤ Nat.card R := h.two_lt.le
  have c₂ : 2 ≤ Nat.card U := h.two_lt_card_U.le
  have c₃ : 2 ≤ Nat.card W := h.two_lt_card_W.le
  rw [sum_triple (h.decomp.cR v) (h.decomp.cU v) (h.decomp.cW v) h.chi c₁ c₂ c₃, ← h.card_eq]
  rfl

theorem cform_eq {p : Bool × Bool × Bool} (hp : h.Occ p) :
    cform h.chi p (Nat.card R - 2) (Nat.card U - 2) =
      cform h.chi (true, false, false) (Nat.card R - 2) (Nat.card U - 2) := by
  obtain ⟨v, hv, rfl⟩ := hp
  obtain ⟨x, r, hr, hr0, rfl⟩ := hv
  rw [← h.cnt_eq, cnt_smul, h.cnt_eq, h.pat_of_mem_R hr hr0]

end Hyp51

end CFSG.ComponentClassification.AS76b.Sec5
