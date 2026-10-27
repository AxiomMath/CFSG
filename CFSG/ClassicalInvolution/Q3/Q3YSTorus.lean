module

public import CFSG.ClassicalInvolution.Q3.Q3YSComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

section Torus

variable {K : Type} [Group K] {k : Type*} [Field k] {D : UniversalRootDatum K}
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

def sl2W (t : kˣ) : Matrix.SpecialLinearGroup (Fin 2) k :=
  sl2Upper (t : k) * sl2Lower (-((t⁻¹ : kˣ) : k)) * sl2Upper (t : k)

theorem coe_sl2W (t : kˣ) :
    (sl2W t : Matrix (Fin 2) (Fin 2) k) = !![0, (t : k); -((t⁻¹ : kˣ) : k), 0] := by
  simp only [sl2W, Matrix.SpecialLinearGroup.coe_mul]
  change !![1, (t : k); 0, 1] * !![1, 0; -((t⁻¹ : kˣ) : k), 1] * !![1, (t : k); 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_neg_one : sl2W (-1 : kˣ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) k) * sl2W 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, coe_sl2W, coe_sl2W]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weylElement_eq (hX : ChevalleyExtras D k x C O) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, ∀ t : kˣ, weylElement x i t = φ (sl2W t) := by
  obtain ⟨φ, -, hup, hlo⟩ := hX.rankOne i
  refine ⟨φ, fun t => ?_⟩
  simp only [weylElement, sl2W, map_mul, hup, hlo]

theorem hElt_neg_one_eq (hX : ChevalleyExtras D k x C O) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, hElt x i (-1) = φ (-1) := by
  obtain ⟨φ, hφ⟩ := weylElement_eq hX i
  refine ⟨φ, ?_⟩
  unfold hElt
  rw [hφ, hφ, sl2W_neg_one, map_mul, mul_inv_cancel_right]

theorem hElt_neg_one_mul_self (hX : ChevalleyExtras D k x C O) (i : Fin D.rank) :
    hElt x i (-1) * hElt x i (-1) = 1 := by
  obtain ⟨φ, h⟩ := hElt_neg_one_eq hX i
  rw [h, ← map_mul]
  have : (-1 : Matrix.SpecialLinearGroup (Fin 2) k) * (-1) = 1 := by
    apply Subtype.ext
    simp
  rw [this, map_one]

theorem hElt_conj_weylElement (hX : ChevalleyExtras D k x C O) (a b : Fin D.rank) (s : kˣ) :
    hElt x a (-1) * weylElement x b s * (hElt x a (-1))⁻¹ =
      weylElement x b ((-1 : kˣ) ^ (D.cartan a b) * s) := by
  have hβ : (Pi.single b 1 : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots D b
  have hβ' : (-Pi.single b 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hβ
  have e1 : (∑ l, D.cartan a l * (Pi.single b (1 : ℤ) : Fin D.rank → ℤ) l) = D.cartan a b := by
    simp [Pi.single_apply]
  have e2 : (∑ l, D.cartan a l * (-Pi.single b (1 : ℤ) : Fin D.rank → ℤ) l) = -D.cartan a b := by
    simp [Pi.single_apply]
  have e : ∀ g y z w : K, g * (y * z * w) * g⁻¹ =
      (g * y * g⁻¹) * (g * z * g⁻¹) * (g * w * g⁻¹) := by
    intros
    group
  unfold weylElement
  rw [e, hElt_conj_x hX a (-1) hβ, hElt_conj_x hX a (-1) hβ', e1, e2]
  have h3 : (((-1 : kˣ) ^ (-D.cartan a b) : kˣ) : k) * (-((s⁻¹ : kˣ) : k)) =
      -((((-1 : kˣ) ^ D.cartan a b * s)⁻¹ : kˣ) : k) := by
    rw [zpow_neg, mul_inv, Units.val_mul]
    ring
  rw [h3]
  simp only [Units.val_mul]

theorem hElt_comm (hX : ChevalleyExtras D k x C O) (a b : Fin D.rank) :
    hElt x a (-1) * hElt x b (-1) = hElt x b (-1) * hElt x a (-1) := by
  have h2 := hElt_neg_one_mul_self hX b
  have e1 := hElt_conj_weylElement hX a b (-1)
  have e2 := hElt_conj_weylElement hX a b 1
  have hb : hElt x b (-1) = weylElement x b (-1) * (weylElement x b 1)⁻¹ := rfl
  have key : hElt x a (-1) * hElt x b (-1) * (hElt x a (-1))⁻¹ = hElt x b (-1) := by
    generalize hElt x a (-1) = ta at e1 e2 ⊢
    rw [hb] at h2 ⊢
    calc ta * (weylElement x b (-1) * (weylElement x b 1)⁻¹) * ta⁻¹
        = (ta * weylElement x b (-1) * ta⁻¹) * (ta * weylElement x b 1 * ta⁻¹)⁻¹ := by group
      _ = weylElement x b ((-1 : kˣ) ^ (D.cartan a b) * -1) *
            (weylElement x b ((-1 : kˣ) ^ (D.cartan a b) * 1))⁻¹ := by rw [e1, e2]
      _ = weylElement x b (-1) * (weylElement x b 1)⁻¹ := by
        rcases Int.even_or_odd (D.cartan a b) with hc | hc
        · rw [hc.neg_one_zpow]
          simp
        · rw [hc.neg_one_zpow]
          have h3 := inv_eq_of_mul_eq_one_right h2
          rw [mul_inv_rev, inv_inv] at h3
          simpa using h3
  exact mul_inv_eq_iff_eq_mul.mp key

theorem not_mem_center_of_conj (hX : ChevalleyExtras D k x C O) {g : K}
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) {u c : k} (h : g * x β u * g⁻¹ = x β c)
    (hne : c ≠ u) : g ∉ Subgroup.center K := by
  intro hg
  have h1 : g * x β u * g⁻¹ = x β u := by
    rw [← Subgroup.mem_center_iff.mp hg (x β u)]
    group
  rw [h1] at h
  exact hne ((hX.param β hβ).2.2 h).symm

theorem exists_fourGroup_torus [Finite K] (hX : ChevalleyExtras D k x C O) (hk : (-1 : k) ≠ 1)
    {a b : Fin D.rank} (hab : Odd (D.cartan a b)) (hba : Odd (D.cartan b a)) :
    ∃ F : Subgroup K, CFSG.Open.IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
      F ⊓ Subgroup.center K = ⊥ := by
  have haa : D.cartan a a = 2 := D.isFiniteType.apply_self a
  have hsa : (Pi.single a 1 : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots D a
  have hsb : (Pi.single b 1 : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots D b
  have ca : ∀ i j : Fin D.rank,
      (∑ l, D.cartan i l * (Pi.single j (1 : ℤ) : Fin D.rank → ℤ) l) = D.cartan i j := by
    intro i j
    simp [Pi.single_apply]
  have hp : hElt x a (-1) ∉ Subgroup.center K := by
    refine not_mem_center_of_conj hX hsb (u := 1) (c := -1) ?_ hk
    rw [hElt_conj_x hX a (-1) hsb 1, ca, hab.neg_one_zpow]
    simp
  have hq : hElt x b (-1) ∉ Subgroup.center K := by
    refine not_mem_center_of_conj hX hsa (u := 1) (c := -1) ?_ hk
    rw [hElt_conj_x hX b (-1) hsa 1, ca, hba.neg_one_zpow]
    simp
  have hpq : hElt x a (-1) * hElt x b (-1) ∉ Subgroup.center K := by
    refine not_mem_center_of_conj hX hsa (u := 1) (c := -1) ?_ hk
    have e : ∀ g₁ g₂ y : K, g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ := by
      intros
      group
    rw [e, hElt_conj_x hX b (-1) hsa 1, ca, hba.neg_one_zpow, hElt_conj_x hX a (-1) hsa, ca, haa]
    simp
  exact exists_fourGroup_of_noncentral (hElt_neg_one_mul_self hX a) (hElt_neg_one_mul_self hX b)
    (hElt_comm hX a b) hp hq hpq

end Torus

end CFSG.ClassicalInvolution.Q3.Q3YS
