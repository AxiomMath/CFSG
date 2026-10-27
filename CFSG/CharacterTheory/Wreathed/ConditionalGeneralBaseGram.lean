module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseDecomposition
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.Wreathed.ConditionalFourier

variable {m : ℕ} [NeZero m]

@[expose] def dualSixFun (J : ZMod m × ZMod m) : Fin 6 → ZMod m × ZMod m :=
  ![J, (J.2, J.1), (J.2, -J.1 - J.2), (-J.1 - J.2, J.1), (J.1, -J.1 - J.2), (-J.1 - J.2, J.2)]

section

omit [NeZero m]

@[simp] theorem dualSixFun_zero (J : ZMod m × ZMod m) : dualSixFun J 0 = J := rfl
@[simp] theorem dualSixFun_one (J : ZMod m × ZMod m) : dualSixFun J 1 = (J.2, J.1) := rfl
@[simp] theorem dualSixFun_two (J : ZMod m × ZMod m) :
    dualSixFun J 2 = (J.2, -J.1 - J.2) := rfl
@[simp] theorem dualSixFun_three (J : ZMod m × ZMod m) :
    dualSixFun J 3 = (-J.1 - J.2, J.1) := rfl
@[simp] theorem dualSixFun_four (J : ZMod m × ZMod m) :
    dualSixFun J 4 = (J.1, -J.1 - J.2) := rfl
@[simp] theorem dualSixFun_five (J : ZMod m × ZMod m) :
    dualSixFun J 5 = (-J.1 - J.2, J.2) := rfl

theorem dualSixFun_mem_dualSix (J : ZMod m × ZMod m) (k : Fin 6) :
    dualSixFun J k ∈ dualSix J := by
  rw [mem_dualSix_iff]
  fin_cases k <;> simp

theorem card_dualSixFun_eq_zero {I J : ZMod m × ZMod m}
    (h : I ∉ MulAction.orbit (dualGroup m) J) :
    ((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun J k = I)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  exact h ((mem_orbit_dualGroup_iff J I).mpr (hk ▸ dualSixFun_mem_dualSix J k))

theorem card_dualSixFun_self {I : ZMod m × ZMod m} (h : (dualSix I).Nodup) :
    ((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun I k = I)).card = 1 := by
  obtain ⟨h1, h2, h3⟩ := (nodup_dualSix_iff I).mp h
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  obtain ⟨i, j⟩ := I
  simp only at h1 h2 h3
  fin_cases k <;> simp [Prod.ext_iff] <;> first
    | exact fun h => h1 h.symm
    | exact fun h _ => h1 h.symm
    | exact fun h => h3 h.symm
    | exact fun h _ => h3 h.symm
    | exact fun _ h => h2 h.symm
    | exact fun h => h2 h.symm

theorem card_dualSixFun_diag {r : ZMod m} (h3 : 3 * r ≠ 0) :
    ((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun (r, r) k = (r, r))).card = 2 := by
  have hne : -r - r ≠ r := by
    intro h
    apply h3
    linear_combination -h
  rw [Finset.card_eq_two]
  refine ⟨0, 1, by decide, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  fin_cases k <;> simp [Prod.ext_iff, hne]

theorem dualSixFun_ne_zero {J : ZMod m × ZMod m} (hJ : J ≠ 0) (k : Fin 6) :
    dualSixFun J k ≠ 0 := by
  obtain ⟨j₁, j₂⟩ := J
  have hJ' : ¬ (j₁ = 0 ∧ j₂ = 0) := fun h => hJ (by rw [h.1, h.2]; rfl)
  intro h
  apply hJ'
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dualSixFun_zero, dualSixFun_one,
      dualSixFun_two, dualSixFun_three, dualSixFun_four, dualSixFun_five,
      Prod.mk_eq_zero] at h
  · exact h
  · exact ⟨h.2, h.1⟩
  · exact ⟨by linear_combination -h.2 - h.1, h.1⟩
  · exact ⟨h.2, by linear_combination -h.1 - h.2⟩
  · exact ⟨h.1, by linear_combination -h.2 - h.1⟩
  · exact ⟨by linear_combination -h.1 - h.2, h.2⟩

end

theorem sum_mul_conj_sum {ι κ μ : Type*} (B : Finset ι) (Q : Finset κ) (R : Finset μ)
    (c : κ → ℂ) (d : μ → ℂ) (X : κ → ι → ℂ) (Y : μ → ι → ℂ) :
    ∑ χ ∈ B, (∑ p ∈ Q, c p * X p χ) * conj (∑ q ∈ R, d q * Y q χ) =
      ∑ p ∈ Q, ∑ q ∈ R, c p * conj (d q) * ∑ χ ∈ B, X p χ * conj (Y q χ) := by
  calc ∑ χ ∈ B, (∑ p ∈ Q, c p * X p χ) * conj (∑ q ∈ R, d q * Y q χ)
      = ∑ χ ∈ B, ∑ p ∈ Q, ∑ q ∈ R, c p * conj (d q) * (X p χ * conj (Y q χ)) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [map_mul]
        ring
    _ = ∑ p ∈ Q, ∑ q ∈ R, ∑ χ ∈ B, c p * conj (d q) * (X p χ * conj (Y q χ)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]

section Characters

variable {A : Type*} [Group A] [Fintype A] {σ υ : A} {ζ : ℂ}
  (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
  (hσ : orderOf σ = m) (hυ : orderOf υ = m)
  (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
  (lam : ZMod m → ZMod m → A →* ℂ)
  (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val)

include hc hζ hlam in
theorem lam_mul_inv (i j : ZMod m) : lam i j (σ * υ)⁻¹ = ζ ^ (-i - j).val := by
  have h := conj_lam_mul_pow hc hζ lam hlam i j 1
  rw [pow_one, mul_one, conj_monoidHom_apply] at h
  exact h

omit [Fintype A] in
theorem inv_pow_mul_inv_pow (hζ : IsPrimitiveRoot ζ m) (i j : ZMod m) :
    (ζ ^ j.val)⁻¹ * (ζ ^ i.val)⁻¹ = ζ ^ (-i - j).val := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg,
    ← zpow_add₀ hζ0]
  apply zpow_eq_of_cast_eq hζ
  push_cast
  simp only [ZMod.natCast_zmod_val]
  ring

omit [Fintype A] in
include hc hgen hζ hlam in
theorem lam_comp_six (h6 : Fin 6 → MulAut A)
    (h6σ : ∀ k, h6 k σ = ![σ, υ, υ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹] k)
    (h6υ : ∀ k, h6 k υ = ![υ, σ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹, υ] k)
    (J : ZMod m × ZMod m) (k : Fin 6) (x : A) :
    lam J.1 J.2 (h6 k x) = lam (dualSixFun J k).1 (dualSixFun J k).2 x := by
  have hext := monoidHom_ext_pair hc hgen ((lam J.1 J.2).comp (h6 k).toMonoidHom)
    (lam (dualSixFun J k).1 (dualSixFun J k).2)
  have h1 : ((lam J.1 J.2).comp (h6 k).toMonoidHom) σ =
      lam (dualSixFun J k).1 (dualSixFun J k).2 σ := by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h6σ,
      (hlam _ _).1]
    fin_cases k <;> simp [(hlam _ _).1, (hlam _ _).2, inv_pow_mul_inv_pow hζ]
  have h2 : ((lam J.1 J.2).comp (h6 k).toMonoidHom) υ =
      lam (dualSixFun J k).1 (dualSixFun J k).2 υ := by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h6υ,
      (hlam _ _).2]
    fin_cases k <;> simp [(hlam _ _).1, (hlam _ _).2, inv_pow_mul_inv_pow hζ]
  exact DFunLike.congr_fun (hext h1 h2) x

omit [Fintype A] in
theorem conj_zpow_root (hζ : IsPrimitiveRoot ζ m) (e : ℤ) : conj (ζ ^ e) = ζ ^ (-e) := by
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (NeZero.ne m)
  have hconj : conj ζ = ζ⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  rw [map_zpow₀, hconj, inv_zpow']

omit [Fintype A] in
include hc hgen hζ hlam in
theorem conj_lam_mul_lam (i j i' j' : ZMod m) (x : A) :
    conj (lam i j x) * lam i' j' x = lam (i' - i) (j' - j) x := by
  obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow hc hgen x
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  rw [lam_zpow_mul_zpow hζ lam hlam, lam_zpow_mul_zpow hζ lam hlam,
    lam_zpow_mul_zpow hζ lam hlam, conj_zpow_root hζ, ← zpow_add₀ hζ0]
  apply zpow_eq_of_cast_eq hζ
  push_cast
  simp only [ZMod.natCast_zmod_val]
  ring

include hc hgen hζ hlam in
theorem sum_conj_lam_mul_lam (I P : ZMod m × ZMod m) :
    ∑ x : A, conj (lam I.1 I.2 x) * lam P.1 P.2 x =
      if P = I then (Fintype.card A : ℂ) else 0 := by
  rw [Finset.sum_congr rfl fun x _ => conj_lam_mul_lam hc hgen hζ lam hlam _ _ _ _ x,
    sum_linearCharacter hc hgen hζ (lam (P.1 - I.1) (P.2 - I.2)) (hlam _ _).1 (hlam _ _).2]
  have hiff : (P.1 - I.1 = 0 ∧ P.2 - I.2 = 0) ↔ P = I := by
    rw [sub_eq_zero, sub_eq_zero, Prod.ext_iff]
  by_cases h : P = I
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]

omit [Fintype A] in
include hc hζ hlam in
theorem lam_triple (i j : ZMod m) (k : ℕ) :
    lam i j ((σ * υ) ^ k) = ζ ^ (((i.val : ℤ) + j.val) * k) ∧
      lam i j (σ ^ k)⁻¹ = ζ ^ (-(i.val : ℤ) * k) ∧
      lam i j (υ ^ k)⁻¹ = ζ ^ (-(j.val : ℤ) * k) := by
  have h1 : (σ * υ) ^ k = σ ^ (k : ℤ) * υ ^ (k : ℤ) := by
    rw [hc.mul_pow, zpow_natCast, zpow_natCast]
  have h2 : (σ ^ k)⁻¹ = σ ^ (-(k : ℤ)) * υ ^ (0 : ℤ) := by
    rw [zpow_zero, mul_one, zpow_neg, zpow_natCast]
  have h3 : (υ ^ k)⁻¹ = σ ^ (0 : ℤ) * υ ^ (-(k : ℤ)) := by
    rw [zpow_zero, one_mul, zpow_neg, zpow_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, lam_zpow_mul_zpow hζ lam hlam]
    congr 1
    ring
  · rw [h2, lam_zpow_mul_zpow hζ lam hlam]
    congr 1
    ring
  · rw [h3, lam_zpow_mul_zpow hζ lam hlam]
    congr 1
    ring

omit [Fintype A] in
include hc hgen hζ hlam in
theorem sum_six_triple (h6 : Fin 6 → MulAut A)
    (h6σ : ∀ k, h6 k σ = ![σ, υ, υ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹] k)
    (h6υ : ∀ k, h6 k υ = ![υ, σ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹, υ] k)
    (J : ZMod m × ZMod m) (k : ℕ) :
    (∑ l : Fin 6, (1 - lam J.1 J.2 (h6 l ((σ * υ) ^ k))) =
        2 * ((1 - lam J.1 J.2 ((σ * υ) ^ k)) + (1 - lam J.1 J.2 (σ ^ k)⁻¹) +
          (1 - lam J.1 J.2 (υ ^ k)⁻¹))) ∧
    (∑ l : Fin 6, (1 - lam J.1 J.2 (h6 l (σ ^ k)⁻¹)) =
        2 * ((1 - lam J.1 J.2 ((σ * υ) ^ k)) + (1 - lam J.1 J.2 (σ ^ k)⁻¹) +
          (1 - lam J.1 J.2 (υ ^ k)⁻¹))) ∧
    (∑ l : Fin 6, (1 - lam J.1 J.2 (h6 l (υ ^ k)⁻¹)) =
        2 * ((1 - lam J.1 J.2 ((σ * υ) ^ k)) + (1 - lam J.1 J.2 (σ ^ k)⁻¹) +
          (1 - lam J.1 J.2 (υ ^ k)⁻¹))) := by
  have key : ∀ a b : ℤ, (a : ZMod m) = b → ζ ^ a = ζ ^ b := fun a b h => zpow_eq_of_cast_eq hζ h
  have hv := fun i j => lam_triple hc hζ lam hlam i j k
  simp only [lam_comp_six hc hgen hζ lam hlam h6 h6σ h6υ, Fin.sum_univ_six]
  simp only [dualSixFun_zero, dualSixFun_one, dualSixFun_two, dualSixFun_three,
    dualSixFun_four, dualSixFun_five, (hv _ _).1, (hv _ _).2.1, (hv _ _).2.2]
  have c : ∀ x : ZMod m, (((x.val : ℤ)) : ZMod m) = x := intCast_val_cast
  refine ⟨?_, ?_, ?_⟩
  · rw [key (((J.2.val : ℤ) + J.1.val) * k) (((J.1.val : ℤ) + J.2.val) * k)
        (by push_cast [c]; ring),
      key (((J.2.val : ℤ) + (-J.1 - J.2).val) * k) (-(J.1.val : ℤ) * k) (by push_cast [c]; ring),
      key ((((-J.1 - J.2).val : ℤ) + J.1.val) * k) (-(J.2.val : ℤ) * k)
        (by push_cast [c]; ring),
      key (((J.1.val : ℤ) + (-J.1 - J.2).val) * k) (-(J.2.val : ℤ) * k)
        (by push_cast [c]; ring),
      key ((((-J.1 - J.2).val : ℤ) + J.2.val) * k) (-(J.1.val : ℤ) * k)
        (by push_cast [c]; ring)]
    ring
  · rw [key (-((-J.1 - J.2).val : ℤ) * k) (((J.1.val : ℤ) + J.2.val) * k)
        (by push_cast [c]; ring)]
    ring
  · rw [key (-((-J.1 - J.2).val : ℤ) * k) (((J.1.val : ℤ) + J.2.val) * k)
        (by push_cast [c]; ring)]
    ring

omit [Fintype A] in
theorem sum_filter_six {B : Type*} [AddCommMonoid B] (h6 : Fin 6 → MulAut A) (P : Finset A)
    {u : A} (hP : ∀ k, h6 k u ∈ P) (hinj : Function.Injective (fun k => h6 k u))
    (f : A → B) :
    ∑ x ∈ P.filter (fun x => ∃ k, h6 k u = x), f x = ∑ k : Fin 6, f (h6 k u) := by
  have himage : P.filter (fun x => ∃ k, h6 k u = x) = Finset.univ.image (fun k => h6 k u) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hx⟩
      exact hx
    · rintro ⟨k, rfl⟩
      exact ⟨hP k, k, rfl⟩
  rw [himage, Finset.sum_image fun k _ l _ hkl => hinj hkl]

include hc hgen hσ hυ hint hζ hlam in
theorem gram_of_normalized_columns (h6 : Fin 6 → MulAut A)
    (h6σ : ∀ k, h6 k σ = ![σ, υ, υ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹] k)
    (h6υ : ∀ k, h6 k υ = ![υ, σ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹, υ] k)
    (P : Finset A)
    (hsplit : ∀ F : A → ℂ, ∑ x, F x = F 1 + ∑ k ∈ Finset.Ico 1 m,
      (F ((σ * υ) ^ k) + F (σ ^ k)⁻¹ + F (υ ^ k)⁻¹) + ∑ x ∈ P, F x)
    (hP : ∀ u ∈ P, ∀ k, h6 k u ∈ P) (hinj : ∀ u ∈ P, Function.Injective (fun k => h6 k u))
    {ι : Type*} (B : Finset ι) (Z : ι → ℕ → ℂ) (W : ι → A → ℂ)
    (hZZ : ∀ k ∈ Finset.Ico 1 m, ∀ l ∈ Finset.Ico 1 m,
      ∑ χ ∈ B, Z χ k * conj (Z χ l) = if k = l then 2 * (m : ℂ) ^ 2 else 0)
    (hZW : ∀ k ∈ Finset.Ico 1 m, ∀ u ∈ P, ∑ χ ∈ B, Z χ k * conj (W χ u) = 0)
    (hWW : ∀ u ∈ P, ∀ u' ∈ P, ∑ χ ∈ B, W χ u * conj (W χ u') =
      if ∃ k, h6 k u = u' then (m : ℂ) ^ 2 else 0)
    (col : ZMod m → ZMod m → ι → ℂ)
    (hcol : ∀ i j, ∀ χ ∈ B, (m : ℂ) ^ 2 * col i j χ =
      ∑ k ∈ Finset.Ico 1 m, ((1 - conj (lam i j ((σ * υ) ^ k))) +
        (1 - conj (lam i j (σ ^ k)⁻¹)) + (1 - conj (lam i j (υ ^ k)⁻¹))) * Z χ k +
      ∑ x ∈ P, (1 - conj (lam i j x)) * W χ x)
    (I J : ZMod m × ZMod m) (hI : I ≠ 0) (hJ : J ≠ 0) :
    ∑ χ ∈ B, col I.1 I.2 χ * conj (col J.1 J.2 χ) =
      6 + (((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun J k = I)).card : ℂ) := by
  classical
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hcard : (Fintype.card A : ℂ) = (m : ℂ) ^ 2 := by
    rw [card_eq_sq hc hgen hσ hυ hint hζ lam hlam]
    push_cast
    ring
  set α : ZMod m × ZMod m → A → ℂ := fun K x => 1 - conj (lam K.1 K.2 x) with hα
  set Bc : ZMod m × ZMod m → ℕ → ℂ := fun K k =>
    α K ((σ * υ) ^ k) + α K (σ ^ k)⁻¹ + α K (υ ^ k)⁻¹ with hBc
  set S : A → ℂ := fun z => ∑ l : Fin 6, conj (α J (h6 l z)) with hS
  have hconjα : ∀ x, conj (α J x) = 1 - lam J.1 J.2 x := by
    intro x
    simp only [hα, map_sub, map_one, Complex.conj_conj]
  have hStriple : ∀ k : ℕ, S ((σ * υ) ^ k) = 2 * conj (Bc J k) ∧
      S (σ ^ k)⁻¹ = 2 * conj (Bc J k) ∧ S (υ ^ k)⁻¹ = 2 * conj (Bc J k) := by
    intro k
    have h := sum_six_triple hc hgen hζ lam hlam h6 h6σ h6υ J k
    have hcB : conj (Bc J k) = (1 - lam J.1 J.2 ((σ * υ) ^ k)) +
        (1 - lam J.1 J.2 (σ ^ k)⁻¹) + (1 - lam J.1 J.2 (υ ^ k)⁻¹) := by
      simp only [hBc, map_add, hconjα]
    simp only [hS, hconjα]
    rw [hcB]
    exact h
  have hcol' : ∀ K : ZMod m × ZMod m, ∀ χ ∈ B, (m : ℂ) ^ 2 * col K.1 K.2 χ =
      ∑ k ∈ Finset.Ico 1 m, Bc K k * Z χ k + ∑ x ∈ P, α K x * W χ x :=
    fun K χ hχ => hcol K.1 K.2 χ hχ
  have hexpand : (m : ℂ) ^ 2 * (m : ℂ) ^ 2 * ∑ χ ∈ B, col I.1 I.2 χ * conj (col J.1 J.2 χ) =
      2 * (m : ℂ) ^ 2 * ∑ k ∈ Finset.Ico 1 m, Bc I k * conj (Bc J k) +
        (m : ℂ) ^ 2 * ∑ x ∈ P, α I x * S x := by
    have h1 : (m : ℂ) ^ 2 * (m : ℂ) ^ 2 * ∑ χ ∈ B, col I.1 I.2 χ * conj (col J.1 J.2 χ) =
        ∑ χ ∈ B, ((m : ℂ) ^ 2 * col I.1 I.2 χ) * conj ((m : ℂ) ^ 2 * col J.1 J.2 χ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [map_mul, map_pow, Complex.conj_natCast]
      ring
    rw [h1, Finset.sum_congr rfl fun χ hχ => by rw [hcol' I χ hχ, hcol' J χ hχ]]
    simp only [map_add, add_mul, mul_add, Finset.sum_add_distrib]
    rw [sum_mul_conj_sum, sum_mul_conj_sum, sum_mul_conj_sum, sum_mul_conj_sum]
    have hT1 : ∑ k ∈ Finset.Ico 1 m, ∑ l ∈ Finset.Ico 1 m, Bc I k * conj (Bc J l) *
        ∑ χ ∈ B, Z χ k * conj (Z χ l) =
        2 * (m : ℂ) ^ 2 * ∑ k ∈ Finset.Ico 1 m, Bc I k * conj (Bc J k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.sum_congr rfl fun l hl => by rw [hZZ k hk l hl], Finset.sum_eq_single k]
      · rw [ite_eq_left rfl]
        ring
      · intro l _ hlk
        rw [ite_eq_right (Ne.symm hlk), mul_zero]
      · intro hk'
        exact absurd hk hk'
    have hT2 : ∑ k ∈ Finset.Ico 1 m, ∑ x ∈ P, Bc I k * conj (α J x) *
        ∑ χ ∈ B, Z χ k * conj (W χ x) = 0 := by
      refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun x hx => ?_
      rw [hZW k hk x hx, mul_zero]
    have hT3 : ∑ x ∈ P, ∑ l ∈ Finset.Ico 1 m, α I x * conj (Bc J l) *
        ∑ χ ∈ B, W χ x * conj (Z χ l) = 0 := by
      refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun l hl => ?_
      have h0 : ∑ χ ∈ B, W χ x * conj (Z χ l) = conj (∑ χ ∈ B, Z χ l * conj (W χ x)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_mul, Complex.conj_conj, mul_comm]
      rw [h0, hZW l hl x hx, map_zero, mul_zero]
    have hT4 : ∑ x ∈ P, ∑ x' ∈ P, α I x * conj (α J x') *
        ∑ χ ∈ B, W χ x * conj (W χ x') = (m : ℂ) ^ 2 * ∑ x ∈ P, α I x * S x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.sum_congr rfl fun x' hx' => by rw [hWW x hx x' hx']]
      simp only [mul_ite, mul_zero, hS]
      rw [← Finset.sum_filter, sum_filter_six h6 P (hP x hx) (hinj x hx), Finset.mul_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [hT1, hT2, hT3, hT4]
    ring
  have hcentral : 2 * ∑ k ∈ Finset.Ico 1 m, Bc I k * conj (Bc J k) =
      ∑ k ∈ Finset.Ico 1 m, (α I ((σ * υ) ^ k) * S ((σ * υ) ^ k) +
        α I (σ ^ k)⁻¹ * S (σ ^ k)⁻¹ + α I (υ ^ k)⁻¹ * S (υ ^ k)⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h1, h2, h3⟩ := hStriple k
    rw [h1, h2, h3, hBc]
    ring
  have hα1 : α I 1 = 0 := by simp [hα]
  have htotal : 2 * ∑ k ∈ Finset.Ico 1 m, Bc I k * conj (Bc J k) + ∑ x ∈ P, α I x * S x =
      ∑ x : A, α I x * S x := by
    rw [hsplit (fun x => α I x * S x), hα1, zero_mul, zero_add, hcentral]
  have hD : ∑ x : A, α I x * S x = (m : ℂ) ^ 2 * (6 +
      (((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun J k = I)).card : ℂ)) := by
    have hrw : ∀ x, α I x * S x = ∑ l : Fin 6, (1 - conj (lam I.1 I.2 x)) *
        (1 - lam (dualSixFun J l).1 (dualSixFun J l).2 x) := by
      intro x
      simp only [hS, Finset.mul_sum, hα, map_sub, map_one, Complex.conj_conj]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [lam_comp_six hc hgen hζ lam hlam h6 h6σ h6υ J l x]
    rw [Finset.sum_congr rfl fun x _ => hrw x, Finset.sum_comm]
    have hterm : ∀ l : Fin 6, ∑ x : A, (1 - conj (lam I.1 I.2 x)) *
        (1 - lam (dualSixFun J l).1 (dualSixFun J l).2 x) =
        (m : ℂ) ^ 2 * (1 + if dualSixFun J l = I then 1 else 0) := by
      intro l
      have hPne := dualSixFun_ne_zero hJ l
      have hs1 := sum_linearCharacter hc hgen hζ (lam (dualSixFun J l).1 (dualSixFun J l).2)
        (hlam _ _).1 (hlam _ _).2
      have hs2 := sum_linearCharacter hc hgen hζ (lam I.1 I.2) (hlam _ _).1 (hlam _ _).2
      have hs3 := sum_conj_lam_mul_lam hc hgen hζ lam hlam I (dualSixFun J l)
      have hnz1 : ¬ ((dualSixFun J l).1 = 0 ∧ (dualSixFun J l).2 = 0) := fun h =>
        hPne (Prod.ext h.1 h.2)
      have hnz2 : ¬ (I.1 = 0 ∧ I.2 = 0) := fun h => hI (Prod.ext h.1 h.2)
      rw [ite_eq_right hnz1] at hs1
      rw [ite_eq_right hnz2] at hs2
      have hs2' : ∑ x : A, conj (lam I.1 I.2 x) = 0 := by rw [← map_sum, hs2, map_zero]
      have hexp : ∀ x : A, (1 - conj (lam I.1 I.2 x)) *
          (1 - lam (dualSixFun J l).1 (dualSixFun J l).2 x) =
          1 - lam (dualSixFun J l).1 (dualSixFun J l).2 x - conj (lam I.1 I.2 x) +
            conj (lam I.1 I.2 x) * lam (dualSixFun J l).1 (dualSixFun J l).2 x := by
        intro x
        ring
      rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, hs1, hs2', hs3, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, hcard]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_boole]
    ring
  have hfinal : (m : ℂ) ^ 2 * (m : ℂ) ^ 2 * ∑ χ ∈ B, col I.1 I.2 χ * conj (col J.1 J.2 χ) =
      (m : ℂ) ^ 2 * (m : ℂ) ^ 2 * (6 +
        (((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun J k = I)).card : ℂ)) := by
    rw [hexpand]
    calc 2 * (m : ℂ) ^ 2 * ∑ k ∈ Finset.Ico 1 m, Bc I k * conj (Bc J k) +
          (m : ℂ) ^ 2 * ∑ x ∈ P, α I x * S x
        = (m : ℂ) ^ 2 * (2 * ∑ k ∈ Finset.Ico 1 m, Bc I k * conj (Bc J k) +
          ∑ x ∈ P, α I x * S x) := by ring
      _ = (m : ℂ) ^ 2 * ∑ x : A, α I x * S x := by rw [htotal]
      _ = _ := by rw [hD]; ring
  have hm4 : (m : ℂ) ^ 2 * (m : ℂ) ^ 2 ≠ 0 := by positivity
  exact mul_left_cancel₀ hm4 hfinal

end Characters

end CFSG.Wreathed.ConditionalGeneralBase
