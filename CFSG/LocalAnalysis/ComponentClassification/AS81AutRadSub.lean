module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AutRad

public noncomputable section

namespace CFSG.ComponentClassification.AS81

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ComponentClassification.RankTwoL3Even

variable {k : Type} [Field k]

theorem mul_unipU_zero_apply (M : Matrix (Fin 3) (Fin 3) k) (x z : k) (i j : Fin 3) :
    (M * (unipU k x 0 z : Matrix (Fin 3) (Fin 3) k)) i j =
      M i j + (if j = 1 then x * M i 0 else 0) + (if j = 2 then z * M i 0 else 0) := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem unipU_zero_mul_apply (M : Matrix (Fin 3) (Fin 3) k) (x z : k) (i j : Fin 3) :
    ((unipU k x 0 z : Matrix (Fin 3) (Fin 3) k) * M) i j =
      M i j + if i = 0 then x * M 1 j + z * M 2 j else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem mul_unipU_one_apply' (M : Matrix (Fin 3) (Fin 3) k) (y z : k) (i j : Fin 3) :
    (M * (unipU k 0 y z : Matrix (Fin 3) (Fin 3) k)) i j =
      M i j + if j = 2 then z * M i 0 + y * M i 1 else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem unipU_one_mul_apply' (M : Matrix (Fin 3) (Fin 3) k) (y z : k) (i j : Fin 3) :
    ((unipU k 0 y z : Matrix (Fin 3) (Fin 3) k) * M) i j =
      M i j + (if i = 0 then z * M 2 j else 0) + (if i = 1 then y * M 2 j else 0) := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem commute_unipU_zero_of_det {M : Matrix (Fin 3) (Fin 3) k} {a c a' c' : k}
    (hdet : a * c' - c * a' ≠ 0)
    (h₁ : M * (unipU k a 0 c : Matrix (Fin 3) (Fin 3) k) = (unipU k a 0 c : Matrix _ _ k) * M)
    (h₂ : M * (unipU k a' 0 c' : Matrix (Fin 3) (Fin 3) k) = (unipU k a' 0 c' : Matrix _ _ k) * M)
    (x z : k) :
    M * (unipU k x 0 z : Matrix (Fin 3) (Fin 3) k) = (unipU k x 0 z : Matrix _ _ k) * M := by
  have e : ∀ {a c : k}, M * (unipU k a 0 c : Matrix (Fin 3) (Fin 3) k) =
      (unipU k a 0 c : Matrix _ _ k) * M → ∀ i j : Fin 3,
      M i j + (if j = 1 then a * M i 0 else 0) + (if j = 2 then c * M i 0 else 0) =
        M i j + if i = 0 then a * M 1 j + c * M 2 j else 0 := by
    intro a c h i j
    have := congrFun (congrFun h i) j
    rwa [mul_unipU_zero_apply, unipU_zero_mul_apply] at this
  have e₁ := e h₁
  have e₂ := e h₂
  have a11 := e₁ 1 1
  have a12 := e₁ 1 2
  have a21 := e₁ 2 1
  have a22 := e₁ 2 2
  have a01 := e₁ 0 1
  have a02 := e₁ 0 2
  have b11 := e₂ 1 1
  have b12 := e₂ 1 2
  have b21 := e₂ 2 1
  have b22 := e₂ 2 2
  have b01 := e₂ 0 1
  have b02 := e₂ 0 2
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, add_zero] at a11 a12 a21 a22 a01 a02
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, add_zero] at b11 b12 b21 b22 b01 b02
  have h10 : M 1 0 = 0 := by
    have : (a * c' - c * a') * M 1 0 = 0 := by linear_combination c' * a11 - c * b11 + 0 * a12
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h20 : M 2 0 = 0 := by
    have : (a * c' - c * a') * M 2 0 = 0 := by linear_combination c' * a21 - c * b21
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h11 : M 1 1 = M 0 0 := by
    have : (a * c' - c * a') * (M 1 1 - M 0 0) = 0 := by linear_combination -c' * a01 + c * b01
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hdet))
  have h21 : M 2 1 = 0 := by
    have : (a * c' - c * a') * M 2 1 = 0 := by linear_combination a' * a01 - a * b01
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h12 : M 1 2 = 0 := by
    have : (a * c' - c * a') * M 1 2 = 0 := by linear_combination -c' * a02 + c * b02
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h22 : M 2 2 = M 0 0 := by
    have : (a * c' - c * a') * (M 2 2 - M 0 0) = 0 := by linear_combination a' * a02 - a * b02
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hdet))
  ext i j
  rw [mul_unipU_zero_apply, unipU_zero_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h11, h21, h12, h22]

theorem commute_unipU_one_of_det {M : Matrix (Fin 3) (Fin 3) k} {b c b' c' : k}
    (hdet : b * c' - c * b' ≠ 0)
    (h₁ : M * (unipU k 0 b c : Matrix (Fin 3) (Fin 3) k) = (unipU k 0 b c : Matrix _ _ k) * M)
    (h₂ : M * (unipU k 0 b' c' : Matrix (Fin 3) (Fin 3) k) = (unipU k 0 b' c' : Matrix _ _ k) * M)
    (y z : k) :
    M * (unipU k 0 y z : Matrix (Fin 3) (Fin 3) k) = (unipU k 0 y z : Matrix _ _ k) * M := by
  have e : ∀ {b c : k}, M * (unipU k 0 b c : Matrix (Fin 3) (Fin 3) k) =
      (unipU k 0 b c : Matrix _ _ k) * M → ∀ i j : Fin 3,
      M i j + (if j = 2 then c * M i 0 + b * M i 1 else 0) =
        M i j + (if i = 0 then c * M 2 j else 0) + (if i = 1 then b * M 2 j else 0) := by
    intro b c h i j
    have := congrFun (congrFun h i) j
    rwa [mul_unipU_one_apply', unipU_one_mul_apply'] at this
  have e₁ := e h₁
  have e₂ := e h₂
  have a00 := e₁ 0 0
  have a01 := e₁ 0 1
  have a02 := e₁ 0 2
  have a10 := e₁ 1 0
  have a11 := e₁ 1 1
  have a12 := e₁ 1 2
  have b00 := e₂ 0 0
  have b01 := e₂ 0 1
  have b02 := e₂ 0 2
  have b10 := e₂ 1 0
  have b11 := e₂ 1 1
  have b12 := e₂ 1 2
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, add_zero] at a00 a01 a02 a10 a11 a12
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, add_zero] at b00 b01 b02 b10 b11 b12
  have h20 : M 2 0 = 0 := by
    have : (b * c' - c * b') * M 2 0 = 0 := by linear_combination -b * b00 + b' * a00 + 0 * a10
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h21 : M 2 1 = 0 := by
    have : (b * c' - c * b') * M 2 1 = 0 := by linear_combination -b * b01 + b' * a01
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h01 : M 0 1 = 0 := by
    have : (b * c' - c * b') * M 0 1 = 0 := by linear_combination c' * a02 - c * b02
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h22 : M 2 2 = M 0 0 := by
    have : (b * c' - c * b') * (M 2 2 - M 0 0) = 0 := by linear_combination b' * a02 - b * b02
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hdet))
  have h10 : M 1 0 = 0 := by
    have : (b * c' - c * b') * M 1 0 = 0 := by linear_combination -b' * a12 + b * b12
    exact (mul_eq_zero.mp this).resolve_left hdet
  have h11 : M 1 1 = M 2 2 := by
    have : (b * c' - c * b') * (M 1 1 - M 2 2) = 0 := by linear_combination c' * a12 - c * b12
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hdet))
  ext i j
  rw [mul_unipU_one_apply', unipU_one_mul_apply']
  fin_cases i <;> fin_cases j <;> simp [h20, h21, h01, h22, h10, h11]

variable [Finite k]

theorem exists_det_ne_zero_zero {B : Subgroup (projectiveSL 3 k)} (hk : Nat.card k = 4)
    (hB : B ≤ projRad k 0) (hB5 : 5 ≤ Nat.card B) :
    ∃ a c a' c' : k, proj 3 k (unipU k a 0 c) ∈ B ∧ proj 3 k (unipU k a' 0 c') ∈ B ∧
      a * c' - c * a' ≠ 0 := by
  have hne : B ≠ ⊥ := fun h => by
    rw [h, card_bot] at hB5
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.mp (hB hbB)
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    push Not at h
    apply hb1
    apply Subtype.ext
    simp only [h.1, h.2, OneMemClass.coe_one]
    rw [unipU_zero, map_one]
  set f : k → projectiveSL 3 k := fun t => proj 3 k (unipU k (t * a) 0 (t * c)) with hf
  have hnot : ¬ ((B : Set (projectiveSL 3 k)) ⊆ Set.range f) := by
    intro hsub
    have h1 : Nat.card B ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hsub
    have h2 := Finite.card_range_le f
    omega
  rw [Set.not_subset] at hnot
  obtain ⟨b', hb'B, hb'f⟩ := hnot
  obtain ⟨a', c', rfl⟩ := mem_projRad_zero.mp (hB hb'B)
  refine ⟨a, c, a', c', hbB, hb'B, fun hdet => hb'f ?_⟩
  rcases hac with ha | hc
  · refine ⟨a' / a, ?_⟩
    simp only [hf]
    congr 2
    · field_simp
    · field_simp
      linear_combination -hdet
  · refine ⟨c' / c, ?_⟩
    simp only [hf]
    congr 2
    · field_simp
      linear_combination hdet
    · field_simp

theorem exists_det_ne_zero_one {B : Subgroup (projectiveSL 3 k)} (hk : Nat.card k = 4)
    (hB : B ≤ projRad k 1) (hB5 : 5 ≤ Nat.card B) :
    ∃ b c b' c' : k, proj 3 k (unipU k 0 b c) ∈ B ∧ proj 3 k (unipU k 0 b' c') ∈ B ∧
      b * c' - c * b' ≠ 0 := by
  have hne : B ≠ ⊥ := fun h => by
    rw [h, card_bot] at hB5
    omega
  obtain ⟨⟨x, hxB⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.mp (hB hxB)
  have hbc : b ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    push Not at h
    apply hx1
    apply Subtype.ext
    simp only [h.1, h.2, OneMemClass.coe_one]
    rw [unipU_zero, map_one]
  set f : k → projectiveSL 3 k := fun t => proj 3 k (unipU k 0 (t * b) (t * c)) with hf
  have hnot : ¬ ((B : Set (projectiveSL 3 k)) ⊆ Set.range f) := by
    intro hsub
    have h1 : Nat.card B ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hsub
    have h2 := Finite.card_range_le f
    omega
  rw [Set.not_subset] at hnot
  obtain ⟨x', hx'B, hx'f⟩ := hnot
  obtain ⟨b', c', rfl⟩ := mem_projRad_one.mp (hB hx'B)
  refine ⟨b, c, b', c', hxB, hx'B, fun hdet => hx'f ?_⟩
  rcases hbc with hb | hc
  · refine ⟨b' / b, ?_⟩
    simp only [hf]
    congr 2
    · field_simp
    · field_simp
      linear_combination -hdet
  · refine ⟨c' / c, ?_⟩
    simp only [hf]
    congr 2
    · field_simp
      linear_combination hdet
    · field_simp

variable [CharP k 2]

theorem mem_projRad_of_commute (hk : Nat.card k = 4) (i : Fin 2)
    {B : Subgroup (projectiveSL 3 k)} (hB : B ≤ projRad k i) (hB5 : 5 ≤ Nat.card B)
    {g : projectiveSL 3 k} (hg : ∀ b ∈ B, g * b = b * g) : g ∈ projRad k i := by
  obtain ⟨g', rfl⟩ := proj_surjective 3 k g
  have hconj : ∀ {a b c : k}, proj 3 k (unipU k a b c) ∈ B →
      (g' : Matrix (Fin 3) (Fin 3) k) * (unipU k a b c : Matrix (Fin 3) (Fin 3) k) =
        (unipU k a b c : Matrix (Fin 3) (Fin 3) k) * g' := by
    intro a b c hu
    have h := hg _ hu
    have h' : conjAut 3 k (SpecialLinearGroup.toGL g') (proj 3 k (unipU k a b c)) =
        proj 3 k (unipU k a b c) := by
      rw [conjAut_toGL, MulAut.conj_apply, h, mul_inv_cancel_right]
    have := mul_eq_mul_of_conjAut_proj_eq rfl (trace_unipU_ne_zero a b c) h'
    rwa [SpecialLinearGroup.coe_GL_coe_matrix] at this
  have hfix : ∀ x ∈ projRad k i, MulAut.conj (proj 3 k g') x = x := by
    intro x hx
    fin_cases i
    · obtain ⟨a, c, a', c', h₁, h₂, hdet⟩ := exists_det_ne_zero_zero hk hB hB5
      have hall := commute_unipU_zero_of_det hdet (hconj h₁) (hconj h₂)
      obtain ⟨x', z, rfl⟩ := mem_projRad_zero.mp hx
      have hc : g' * unipU k x' 0 z = unipU k x' 0 z * g' := by
        ext a b
        simp only [Matrix.SpecialLinearGroup.coe_mul]
        exact congrFun (congrFun (hall x' z) a) b
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right]
    · obtain ⟨b, c, b', c', h₁, h₂, hdet⟩ := exists_det_ne_zero_one hk hB hB5
      have hall := commute_unipU_one_of_det hdet (hconj h₁) (hconj h₂)
      obtain ⟨y, z, rfl⟩ := mem_projRad_one.mp hx
      have hc : g' * unipU k 0 y z = unipU k 0 y z * g' := by
        ext a b
        simp only [Matrix.SpecialLinearGroup.coe_mul]
        exact congrFun (congrFun (hall y z) a) b
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right]
  obtain ⟨r, hr, hgr⟩ := exists_eq_conj_of_fix_projRad i hfix
  rw [conj_injective_projectiveSL hgr]
  exact hr

theorem eq_one_of_fix_of_odd (hk : Nat.card k = 4) (i : Fin 2)
    {B : Subgroup (projectiveSL 3 k)} (hB : B ≤ projRad k i) (hB8 : 8 ≤ Nat.card B)
    {α : MulAut (projectiveSL 3 k)} (hα : Odd (orderOf α)) (hfix : ∀ b ∈ B, α b = b) :
    α = 1 := by
  set R := projRad k i with hRdef
  have hαR : ∀ x ∈ R, α x ∈ R := fun x hx => mem_projRad_of_commute hk i hB (by omega)
    fun b hb => by
      have hxb : x * b = b * x := commute_of_mem_projRad i hx (hB hb)
      calc α x * b = α x * α b := by rw [hfix b hb]
        _ = α (x * b) := (map_mul α x b).symm
        _ = α (b * x) := by rw [hxb]
        _ = α b * α x := map_mul α b x
        _ = b * α x := by rw [hfix b hb]
  have hfix' : ∀ b ∈ B, α⁻¹ b = b := fun b hb => by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact (hfix b hb).symm
  have hidx : (B.subgroupOf R).index * Nat.card B = 16 := by
    have h1 := (B.subgroupOf R).index_mul_card
    rw [show Nat.card (B.subgroupOf R) = Nat.card B from
      Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, card_projRad, hk] at h1
    exact h1
  have hφ : ∀ x ∈ R, α x * x⁻¹ ∈ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · rw [hfix x hxB, mul_inv_cancel]
      exact B.one_mem
    have hαxB : α x ∉ B := fun h => hxB (by
      have := hfix' _ h
      rw [MulAut.inv_apply_self] at this
      rw [this]
      exact h)
    have h2 : (B.subgroupOf R).index = 2 := by
      have hpos : 0 < (B.subgroupOf R).index := Nat.pos_of_ne_zero (index_ne_zero_of_finite)
      rcases Nat.lt_or_ge (B.subgroupOf R).index 2 with h | h
      · exfalso
        have h1 : (B.subgroupOf R).index = 1 := by omega
        rw [index_eq_one, subgroupOf_eq_top] at h1
        exact hxB (h1 hx)
      · have : (B.subgroupOf R).index * 8 ≤ 16 := hidx ▸ Nat.mul_le_mul_left _ hB8
        omega
    have := (mul_mem_iff_of_index_two h2 (a := ⟨α x, hαR x hx⟩) (b := ⟨x, hx⟩⁻¹)).mpr (by
      simp only [mem_subgroupOf, coe_inv]
      exact ⟨fun h => absurd h hαxB, fun h => absurd (by simpa using B.inv_mem h) hxB⟩)
    simpa [mem_subgroupOf] using this
  have h2 : ∀ x ∈ R, α (α x) = x := by
    intro x hx
    set b := α x * x⁻¹ with hbdef
    have hb := hφ x hx
    have hbx : α x = b * x := by rw [hbdef, inv_mul_cancel_right]
    have hbb : b * b = 1 := by rw [← sq]; exact sq_eq_one_of_mem_projRad hk i (hB hb)
    rw [hbx, map_mul, hfix b hb, hbx, ← mul_assoc, hbb, one_mul]
  obtain ⟨m, hm⟩ := hα
  have hαpow : α = (α ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf α + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hpowfix : ∀ n : ℕ, ∀ x ∈ R, ((α ^ 2) ^ n) x = x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have hα2x : (α ^ 2) x = x := by rw [sq, MulAut.mul_apply, h2 x hx]
      rw [pow_succ, MulAut.mul_apply, hα2x, ih x hx]
  have hfixR : ∀ x ∈ R, α x = x := fun x hx => by
    rw [hαpow]
    exact hpowfix _ x hx
  obtain ⟨r, hr, hαr⟩ := exists_eq_conj_of_fix_projRad i hfixR
  have hα2 : α ^ 2 = 1 := by
    rw [hαr, ← map_pow, sq_eq_one_of_mem_projRad hk i hr, map_one]
  rw [hαpow, hα2, one_pow]

end CFSG.ComponentClassification.AS81
