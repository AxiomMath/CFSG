module

public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary
open scoped Matrix

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

private theorem toStd_two_eq {n : ℕ} (hn : ¬ Even n) (hn3 : 3 ≤ n) :
    toStd n (fun _ => (2 : ℤ)) = 2 • weight n ⟨0, by omega⟩ := by
  funext a
  have h0 : (0 : ℕ) < n / 2 := by omega
  simp only [toStd, hn, ite_false, weight, h0, dite_true, Pi.smul_apply]
  by_cases ha : a.val = 0
  · have : a = ⟨0, h0⟩ := Fin.ext ha
    subst this
    simp
  · have ha' : 0 < a.val := Nat.pos_of_ne_zero ha
    have hne : a ≠ ⟨0, h0⟩ := fun e => ha (by rw [e])
    simp [ha', Pi.single_eq_of_ne hne]

private theorem lv_weight_le {n : ℕ} (i : Fin n) : SUExtras.lv n (weight n i) ≤ (n : ℤ) - 1 := by
  rw [SUExtras.lv_weight]
  omega

private theorem neg_le_lv_weight {n : ℕ} (i : Fin n) :
    -((n : ℤ) - 1) ≤ SUExtras.lv n (weight n i) := by
  rw [SUExtras.lv_weight]
  have := i.isLt
  omega

theorem isHighestRoot_unitary_odd (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : ¬ Even n)
    (hn3 : 3 ≤ n) : IsHighestRoot (Unitary.rootDatum hF n) (fun _ => 2) := by
  set D := Unitary.rootDatum hF n with hD
  have hroots : D.roots = roots (isFiniteType_cartan n) (divisible n) := rfl
  have hmem : (fun _ => (2 : ℤ)) ∈ D.roots := by
    rw [hroots, roots_eq]
    refine Or.inr (Or.inl ⟨⟨0, by omega⟩, fun e => ?_, toStd_two_eq hn hn3⟩)
    have := congrArg Fin.val e
    simp only [Fin.val_rev] at this
    omega
  have hht : ht (fun _ : Fin D.rank => (2 : ℤ)) = (n : ℤ) - 1 := by
    have h1 := SUExtras.two_mul_ht (n := n) (fun _ => (2 : ℤ))
    rw [toStd_two_eq hn hn3, map_nsmul, SUExtras.lv_weight] at h1
    simp only [nsmul_eq_mul, Nat.cast_ofNat, CharP.cast_eq_zero, mul_zero, sub_zero] at h1
    change 2 * ht (fun _ : Fin (n / 2) => (2 : ℤ)) = _ at h1
    show ht (fun _ : Fin (n / 2) => (2 : ℤ)) = _
    omega
  have hle : ∀ δ ∈ D.roots, ht δ ≤ ht (fun _ : Fin D.rank => (2 : ℤ)) := by
    intro δ hδ
    rw [hht]
    rw [hroots, roots_eq] at hδ
    have h1 := SUExtras.two_mul_ht (n := n) δ
    rcases hδ with ⟨i, j, -, -, -, -, h⟩ | ⟨i, -, h⟩ | ⟨-, i, -, h⟩
    · rw [h, map_sub] at h1
      have := lv_weight_le i
      have := neg_le_lv_weight j
      change 2 * ht δ = _ at h1
      show ht δ ≤ _
      omega
    · rw [h, map_nsmul] at h1
      simp only [nsmul_eq_mul, Nat.cast_ofNat] at h1
      have := lv_weight_le i
      change 2 * ht δ = _ at h1
      show ht δ ≤ _
      omega
    · rw [h] at h1
      have := lv_weight_le i
      change 2 * ht δ = _ at h1
      show ht δ ≤ _
      omega
  refine ⟨hmem, ?_, hle, ?_⟩
  ·
    have hc : cartan n = (Symplectic.cartanC (n / 2))ᵀ := by simp [cartan, hn]
    have hd : divisible n = {k : Fin (n / 2) | k.val + 1 = n / 2} := by simp [divisible, hn]
    rcases hmem with ⟨w, l, h⟩ | ⟨w, l, hl, h⟩
    · exfalso
      have e := congrArg (weylAction D.isFiniteType w⁻¹) h
      rw [weylAction_inv_apply_apply,
        show (fun _ : Fin D.rank => (2 : ℤ)) = 2 • fun _ => (1 : ℤ) by funext; simp,
        map_nsmul] at e
      have := congrFun e l
      simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, Nat.cast_ofNat] at this
      omega
    · have hl' : l.val + 1 = n / 2 := by
        have : l ∈ divisible n := hl
        rw [hd] at this
        exact this
      have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongest_two_nsmul_single_BC
        (m := n / 2) (by omega) hc (isFiniteType_cartan n) hl'
      rw [← hd] at hlong
      have h2 := hlong.map_weylAction w
      intro δ hδ
      have h3 := h2.2 δ hδ
      rw [map_nsmul] at h3
      rw [h]
      exact h3
  ·
    exact isDominant_of_ht_le D.isFiniteType fun k =>
      hle _ (weylAction_mem_roots D.isFiniteType _ hmem)

end CFSG.LieType.HighestRoot
