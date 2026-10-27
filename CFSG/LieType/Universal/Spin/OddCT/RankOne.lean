module

public import CFSG.LieType.Universal.Spin.OddCT.Weyl

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

namespace OddCT

variable {n : ℕ} {K : Type} [Field K]

theorem sl2_bruhat (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (∃ (τ : Kˣ) (y : K), M = diagSL2 τ * upperSL2 y) ∨
      ∃ (x : K) (τ : Kˣ) (y : K), M = upperSL2 x * weylSL2 1 * diagSL2 τ * upperSL2 y := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact M.2
  by_cases hc : M 1 0 = 0
  · left
    have ha : M 0 0 ≠ 0 := by
      intro h0
      rw [h0, hc] at hdet
      simp at hdet
    have hd : M 1 1 = (M 0 0)⁻¹ := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    refine ⟨Units.mk0 (M 0 0) ha, M 0 1 / M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    field_simp
  · right
    refine ⟨M 0 0 / M 1 0, Units.mk0 (-M 1 0) (neg_ne_zero.mpr hc), M 1 1 / M 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
    linear_combination -hdet

theorem rankOne_le_range (k : Fin n) : rankOne (oddRootGroup n K) k ≤ (rankOneB K k).range := by
  refine sup_le ?_ ?_
  · rw [oddRootGroup_single]
    rintro _ ⟨c, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd c), rankOneB_upperSL2 K k _⟩
  · rw [oddRootGroup_neg_single]
    rintro _ ⟨c, rfl⟩
    exact ⟨lowerSL2 (Multiplicative.toAdd c), rankOneB_lowerSL2 K k _⟩

theorem inv_longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    ((oddFrame n K).longRoot hij s t (.ofAdd c))⁻¹ =
      (oddFrame n K).longRoot hij s t (.ofAdd (-c)) := by
  rw [← map_inv]
  rfl

theorem inv_shortRoot (i : Fin n) (s : Bool) (c : K) :
    ((oddFrame n K).shortRoot i s (.ofAdd c))⁻¹ = (oddFrame n K).shortRoot i s (.ofAdd (-c)) := by
  rw [← map_inv]
  rfl

theorem spinAction_longRoot_vec_true {i j : Fin n} (hij : i ≠ j) (c : K) :
    spinAction (quadOdd n K) ((oddFrame n K).longRoot hij true false (.ofAdd c))
        ((oddFrame n K).vec j true) =
      (oddFrame n K).vec j true + c • (oddFrame n K).vec i true :=
  (oddFrame n K).spinAction_longRoot_vec_not_right hij true false c

theorem spinAction_shortRoot_false_vec_true (i : Fin n) (c : K) :
    spinAction (quadOdd n K) ((oddFrame n K).shortRoot i false (.ofAdd c))
        ((oddFrame n K).vec i true) =
      (oddFrame n K).vec i true + c • (oddFrame n K).z - c ^ 2 • (oddFrame n K).vec i false :=
  (oddFrame n K).spinAction_shortRoot_vec_not i false c

theorem spinAction_shortRoot_true_vec_false (i : Fin n) (c : K) :
    spinAction (quadOdd n K) ((oddFrame n K).shortRoot i true (.ofAdd c))
        ((oddFrame n K).vec i false) =
      (oddFrame n K).vec i false + c • (oddFrame n K).z - c ^ 2 • (oddFrame n K).vec i true :=
  (oddFrame n K).spinAction_shortRoot_vec_not i true c

theorem eq_zero_of_mem_normalizer_long {k : Fin n} (hk : k.val + 1 < n) {c : K}
    (hN : rootB K k (.ofAdd c) ∈
      Subgroup.normalizer (oddRootGroup n K (-Pi.single k 1) : Set (spinGroup (quadOdd n K)))) :
    c = 0 := by
  have hkk' : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  have hz := (Subgroup.mem_normalizer_iff.mp hN _).mp (negRootB_mem (K := K) k (.ofAdd 1))
  rw [oddRootGroup_neg_single] at hz
  obtain ⟨d, hd⟩ := hz
  obtain ⟨d, rfl⟩ := Multiplicative.ofAdd.surjective d
  rw [negRootB_of_lt K hk rfl hkk'.symm, rootB_of_lt K hk rfl hkk', inv_longRoot] at hd
  have h1 := congrArg (fun g => spinAction (quadOdd n K) g ((oddFrame n K).vec k true)) hd
  simp only [map_mul, LinearEquiv.mul_apply, HypFrame.spinAction_longRoot_vec_left,
    spinAction_longRoot_vec_true, map_add, map_smul] at h1
  have h2 := congrFun h1 (Sum.inl k)
  simp [hkk'] at h2
  linear_combination h2

theorem sq_eq_one_of_mem_normalizer_short {k : Fin n} (hk : ¬k.val + 1 < n) {c : K}
    (hN : rootB K k (.ofAdd c) ∈
      Subgroup.normalizer (oddRootGroup n K (-Pi.single k 1) : Set (spinGroup (quadOdd n K))))
    (b : K) : (1 + b * c) ^ 2 = 1 := by
  have hz := (Subgroup.mem_normalizer_iff.mp hN _).mp (negRootB_mem (K := K) k (.ofAdd b))
  rw [oddRootGroup_neg_single] at hz
  obtain ⟨d, hd⟩ := hz
  obtain ⟨d, rfl⟩ := Multiplicative.ofAdd.surjective d
  rw [negRootB_of_not_lt K hk, negRootB_of_not_lt K hk, rootB_of_not_lt K hk, inv_shortRoot] at hd
  have h1 := congrArg (fun g => spinAction (quadOdd n K) g ((oddFrame n K).vec k true)) hd
  simp only [map_mul, LinearEquiv.mul_apply, OddFrame.spinAction_shortRoot_vec_self,
    spinAction_shortRoot_false_vec_true, map_add, map_sub, map_smul,
    OddFrame.spinAction_shortRoot_z, spinAction_shortRoot_true_vec_false] at h1
  have h2 := congrFun h1 (Sum.inl k)
  simp [oddZ] at h2
  linear_combination -h2

theorem eq_zero_of_mem_normalizer_short {k : Fin n} (hk : ¬k.val + 1 < n) {c : K}
    (hN : rootB K k (.ofAdd c) ∈
      Subgroup.normalizer (oddRootGroup n K (-Pi.single k 1) : Set (spinGroup (quadOdd n K)))) :
    c = 0 := by
  have h₁ := sq_eq_one_of_mem_normalizer_short hk hN 1
  have h₂ := sq_eq_one_of_mem_normalizer_short hk hN (-1)
  by_cases h2 : (2 : K) = 0
  · have : c * c = 0 := by linear_combination h₁ - c * h2
    exact mul_self_eq_zero.mp this
  · have : (2 : K) * (c * c) = 0 := by linear_combination h₁ + h₂
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)

end OddCT

open OddCT

variable (n : ℕ) (K : Type) [Field K]

theorem oddDatum_rankOne_bruhat : ∀ i : Fin n, ∀ g ∈ rankOne (oddDatum n K).rootGroup i,
    (∃ h ∈ (torusB K i).range, ∃ u ∈ (oddDatum n K).rootGroup (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ (oddDatum n K).rootGroup (Pi.single i 1), ∃ h ∈ (torusB K i).range,
        ∃ v ∈ (oddDatum n K).rootGroup (Pi.single i 1), g = u * weylB K i * h * v := by
  show ∀ i : Fin n, ∀ g ∈ rankOne (oddRootGroup n K) i,
    (∃ h ∈ (torusB K i).range, ∃ u ∈ oddRootGroup n K (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ oddRootGroup n K (Pi.single i 1), ∃ h ∈ (torusB K i).range,
        ∃ v ∈ oddRootGroup n K (Pi.single i 1), g = u * weylB K i * h * v
  intro k g hg
  obtain ⟨M, rfl⟩ := rankOne_le_range k hg
  rcases sl2_bruhat M with ⟨τ, y, rfl⟩ | ⟨x, τ, y, rfl⟩
  · refine Or.inl ⟨torusB K k τ, ⟨τ, rfl⟩, rootB K k (.ofAdd y), rootB_mem k _, ?_⟩
    rw [map_mul, rankOneB_upperSL2]
    rfl
  · refine Or.inr ⟨rootB K k (.ofAdd x), rootB_mem k _, torusB K k τ, ⟨τ, rfl⟩,
      rootB K k (.ofAdd y), rootB_mem k _, ?_⟩
    rw [map_mul, map_mul, map_mul, rankOneB_upperSL2, rankOneB_upperSL2]
    rfl

theorem oddDatum_eq_one_of_mem_normalizer : ∀ i : Fin n,
    ∀ u ∈ (oddDatum n K).rootGroup (Pi.single i 1),
      u ∈ Subgroup.normalizer
        ((oddDatum n K).rootGroup (-Pi.single i 1) : Set (spinGroup (quadOdd n K))) → u = 1 := by
  show ∀ i : Fin n, ∀ u ∈ oddRootGroup n K (Pi.single i 1),
    u ∈ Subgroup.normalizer (oddRootGroup n K (-Pi.single i 1) : Set (spinGroup (quadOdd n K))) →
      u = 1
  intro k u hu hN
  rw [oddRootGroup_single] at hu
  obtain ⟨c, rfl⟩ := hu
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective c
  have hc : c = 0 := by
    by_cases hk : k.val + 1 < n
    · exact eq_zero_of_mem_normalizer_long hk hN
    · exact eq_zero_of_mem_normalizer_short hk hN
  rw [hc, ofAdd_zero, map_one]

theorem oddDatum_torus_commute : ∀ i j : Fin n, ∀ h ∈ (torusB K i).range,
    ∀ h' ∈ (torusB K j).range, Commute h h' := by
  rintro i j _ ⟨τ, rfl⟩ _ ⟨σ, rfl⟩
  exact commute_torusB K i j τ σ

end CFSG.LieType.Universal.Spin
