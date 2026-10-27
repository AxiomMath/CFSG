module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Lin

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K]

theorem polar_vecT (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (i : Fin 3) :
    polar (quadOdd 3 K) v (oddVec 3 K i true) = v (.inr (.inl i)) := by
  rw [oddVec_true, polar_quadOdd_single_inl]

theorem polar_vecF (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (i : Fin 3) :
    polar (quadOdd 3 K) v (oddVec 3 K i false) = v (.inl i) := by
  rw [oddVec_false, polar_quadOdd_single_inr_inl]

theorem polar_vecZ (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    polar (quadOdd 3 K) v (oddZ 3 K) = 2 * v (.inr (.inr ())) := by
  rw [oddZ, polar_quadOdd_single_inr_inr]

noncomputable abbrev planeL (K : Type) [Field K] : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  Submodule.span K {oddVec 3 K 0 true, oddVec 3 K 1 true}

theorem mem_planeL {x : Fin 3 ⊕ Fin 3 ⊕ Unit → K} :
    x ∈ planeL K ↔ ∃ a b : K, a • oddVec 3 K 0 true + b • oddVec 3 K 1 true = x :=
  Submodule.mem_span_pair

theorem smul_add_mem_planeL (a b : K) :
    a • oddVec 3 K 0 true + b • oddVec 3 K 1 true ∈ planeL K :=
  mem_planeL.mpr ⟨a, b, rfl⟩

@[expose] noncomputable def radU (K : Type) [Field K] :
    Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) where
  carrier := {g | (∀ v, quadOdd 3 K (g v) = quadOdd 3 K v) ∧
    g (oddVec 3 K 0 true) = oddVec 3 K 0 true ∧ g (oddVec 3 K 1 true) = oddVec 3 K 1 true ∧
    ∀ x, polar (quadOdd 3 K) x (oddVec 3 K 0 true) = 0 →
      polar (quadOdd 3 K) x (oddVec 3 K 1 true) = 0 → g x - x ∈ planeL K}
  mul_mem' := by
    rintro g h ⟨hgO, hg0, hg1, hgL⟩ ⟨hhO, hh0, hh1, hhL⟩
    refine ⟨fun v => by rw [LinearEquiv.mul_apply, hgO, hhO],
      by rw [LinearEquiv.mul_apply, hh0, hg0], by rw [LinearEquiv.mul_apply, hh1, hg1],
      fun x hx0 hx1 => ?_⟩
    have h0 : polar (quadOdd 3 K) (h x) (oddVec 3 K 0 true) = 0 := by
      rw [← hh0, polar_apply_of_map hhO, hx0]
    have h1 : polar (quadOdd 3 K) (h x) (oddVec 3 K 1 true) = 0 := by
      rw [← hh1, polar_apply_of_map hhO, hx1]
    rw [LinearEquiv.mul_apply, show g (h x) - x = (g (h x) - h x) + (h x - x) by abel]
    exact add_mem (hgL _ h0 h1) (hhL x hx0 hx1)
  one_mem' := ⟨fun _ => rfl, rfl, rfl, fun x _ _ => by
    show x - x ∈ planeL K
    rw [sub_self]
    exact zero_mem _⟩
  inv_mem' := by
    rintro g ⟨hgO, hg0, hg1, hgL⟩
    have hinv : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
    refine ⟨fun v => ?_, (LinearEquiv.symm_apply_eq g).mpr hg0.symm,
      (LinearEquiv.symm_apply_eq g).mpr hg1.symm, fun x hx0 hx1 => ?_⟩
    · have := hgO (g⁻¹ v)
      rw [hinv] at this
      exact this.symm
    · have h0 : polar (quadOdd 3 K) (g⁻¹ x) (oddVec 3 K 0 true) = 0 := by
        rw [← polar_apply_of_map hgO, hinv, hg0, hx0]
      have h1 : polar (quadOdd 3 K) (g⁻¹ x) (oddVec 3 K 1 true) = 0 := by
        rw [← polar_apply_of_map hgO, hinv, hg1, hx1]
      have := neg_mem (hgL _ h0 h1)
      rwa [hinv, neg_sub] at this

theorem apply_planeL_of_mem_radU {g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hg : g ∈ radU K) (a b : K) :
    g (a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) =
      a • oddVec 3 K 0 true + b • oddVec 3 K 1 true := by
  rw [map_add, map_smul, map_smul, hg.2.1, hg.2.2.1]

theorem quadOdd_planeL (a b : K) :
    quadOdd 3 K (a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) = 0 := by
  rw [QuadraticMap.map_add (quadOdd 3 K), QuadraticMap.map_smul (quadOdd 3 K),
    QuadraticMap.map_smul (quadOdd 3 K), quadOdd_oddVec, quadOdd_oddVec, polar_smul_left,
    polar_smul_right, polar_vecT]
  simp

theorem polar_planeL {x : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (h0 : polar (quadOdd 3 K) x (oddVec 3 K 0 true) = 0)
    (h1 : polar (quadOdd 3 K) x (oddVec 3 K 1 true) = 0) (a b : K) :
    polar (quadOdd 3 K) x (a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) = 0 := by
  rw [polar_add_right, polar_smul_right, polar_smul_right, h0, h1, smul_zero, smul_zero, add_zero]

theorem eichler_mem_radU {u y : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hu : u ∈ planeL K)
    (hy0 : polar (quadOdd 3 K) y (oddVec 3 K 0 true) = 0)
    (hy1 : polar (quadOdd 3 K) y (oddVec 3 K 1 true) = 0) :
    eichler (quadOdd 3 K) u y ∈ radU K := by
  obtain ⟨a, b, rfl⟩ := mem_planeL.mp hu
  have hQu := quadOdd_planeL (K := K) a b
  have huy : polar (quadOdd 3 K) (a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) y = 0 := by
    rw [polar_comm]
    exact polar_planeL hy0 hy1 a b
  have hfix : ∀ v, polar (quadOdd 3 K) v (oddVec 3 K 0 true) = 0 →
      polar (quadOdd 3 K) v (oddVec 3 K 1 true) = 0 → polar (quadOdd 3 K) v y = 0 →
      eichler (quadOdd 3 K) (a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) y v = v :=
    fun v h0 h1 hy => eichler_apply_of_polar_eq_zero (polar_planeL h0 h1 a b) hy
  have hee : ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 →
      polar (quadOdd 3 K) (oddVec 3 K i true) (oddVec 3 K j true) = 0 := fun i j _ _ => by
    rw [polar_quadOdd_oddVec]
    simp
  refine ⟨map_of_mem (eichler_mem_orthogonalGroup _ _ _),
    hfix _ (hee 0 0 (by decide) (by decide)) (hee 0 1 (by decide) (by decide))
      (by rw [polar_comm]; exact hy0),
    hfix _ (hee 1 0 (by decide) (by decide)) (hee 1 1 (by decide) (by decide))
      (by rw [polar_comm]; exact hy1), fun x hx0 hx1 => ?_⟩
  rw [eichler_apply hQu huy, polar_planeL hx0 hx1 a b, zero_smul, add_zero, mul_zero, add_zero,
    show x - polar (quadOdd 3 K) x y • (a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) - x =
      (-(polar (quadOdd 3 K) x y * a)) • oddVec 3 K 0 true +
        (-(polar (quadOdd 3 K) x y * b)) • oddVec 3 K 1 true by module]
  exact smul_add_mem_planeL _ _

theorem eichlerPair_apply_fZero {y₀ y₁ : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (h00 : polar (quadOdd 3 K) y₀ (oddVec 3 K 0 true) = 0)
    (h0f : polar (quadOdd 3 K) y₀ (oddVec 3 K 0 false) = 0)
    (h1f : polar (quadOdd 3 K) y₁ (oddVec 3 K 0 false) = 0) :
    (eichler (quadOdd 3 K) (oddVec 3 K 0 true) y₀ * eichler (quadOdd 3 K) (oddVec 3 K 1 true) y₁)
        (oddVec 3 K 0 false) =
      oddVec 3 K 0 false + y₀ - quadOdd 3 K y₀ • oddVec 3 K 0 true := by
  have hf1 : polar (quadOdd 3 K) (oddVec 3 K 0 false) (oddVec 3 K 1 true) = 0 := by
    rw [polar_quadOdd_oddVec]
    simp
  have hf0 : polar (quadOdd 3 K) (oddVec 3 K 0 false) (oddVec 3 K 0 true) = 1 := by
    rw [polar_quadOdd_oddVec]
    simp
  rw [LinearEquiv.mul_apply, eichler_apply_of_polar_eq_zero hf1 (by rw [polar_comm]; exact h1f),
    eichler_apply (quadOdd_oddVec 3 K 0 true) (by rw [polar_comm]; exact h00), hf0,
    polar_comm (quadOdd 3 K) (oddVec 3 K 0 false), h0f, one_smul, zero_add, mul_one]

theorem eichlerPair_apply_fOne {y₀ y₁ : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (h00 : polar (quadOdd 3 K) y₀ (oddVec 3 K 0 true) = 0)
    (h01 : polar (quadOdd 3 K) y₀ (oddVec 3 K 1 true) = 0)
    (h10 : polar (quadOdd 3 K) y₁ (oddVec 3 K 0 true) = 0)
    (h11 : polar (quadOdd 3 K) y₁ (oddVec 3 K 1 true) = 0)
    (h1f : polar (quadOdd 3 K) y₁ (oddVec 3 K 1 false) = 0) :
    (eichler (quadOdd 3 K) (oddVec 3 K 0 true) y₀ * eichler (quadOdd 3 K) (oddVec 3 K 1 true) y₁)
        (oddVec 3 K 1 false) =
      oddVec 3 K 1 false + y₁ - (polar (quadOdd 3 K) (oddVec 3 K 1 false) y₀ +
        polar (quadOdd 3 K) y₁ y₀) • oddVec 3 K 0 true - quadOdd 3 K y₁ • oddVec 3 K 1 true := by
  have hp : ∀ (i j : Fin 3) (s t : Bool), polar (quadOdd 3 K) (oddVec 3 K i s) (oddVec 3 K j t) =
      if i = j ∧ s = !t then 1 else 0 := fun i j s t => polar_quadOdd_oddVec 3 K i j s t
  have hE1 : eichler (quadOdd 3 K) (oddVec 3 K 1 true) y₁ (oddVec 3 K 1 false) =
      oddVec 3 K 1 false + y₁ - quadOdd 3 K y₁ • oddVec 3 K 1 true := by
    rw [eichler_apply (quadOdd_oddVec 3 K 1 true) (by rw [polar_comm]; exact h11), hp,
      polar_comm (quadOdd 3 K) (oddVec 3 K 1 false), h1f]
    simp
  have hEf : eichler (quadOdd 3 K) (oddVec 3 K 0 true) y₀ (oddVec 3 K 1 false) =
      oddVec 3 K 1 false - polar (quadOdd 3 K) (oddVec 3 K 1 false) y₀ • oddVec 3 K 0 true := by
    rw [eichler_apply (quadOdd_oddVec 3 K 0 true) (by rw [polar_comm]; exact h00), hp]
    simp
  have hEy : eichler (quadOdd 3 K) (oddVec 3 K 0 true) y₀ y₁ =
      y₁ - polar (quadOdd 3 K) y₁ y₀ • oddVec 3 K 0 true := by
    rw [eichler_apply (quadOdd_oddVec 3 K 0 true) (by rw [polar_comm]; exact h00), h10]
    simp
  have hEe : eichler (quadOdd 3 K) (oddVec 3 K 0 true) y₀ (oddVec 3 K 1 true) =
      oddVec 3 K 1 true := by
    refine eichler_apply_of_polar_eq_zero ?_ (by rw [polar_comm]; exact h01)
    rw [hp]
    simp
  rw [LinearEquiv.mul_apply, hE1, map_sub, map_add, map_smul, hEf, hEy, hEe]
  module

end CFSG.ComponentClassification.HarrisLit.T1.S74
