module

public import CFSG.Fischer.Classification.PartIII.U.Flag
public import CFSG.Fischer.Classification.PartIII.R3.Main
public import CFSG.Fischer.Classification.PartIII.Beta.Points

public section

namespace CFSG.Fischer.Classification.LocalU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification LocalR3 F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem eq_sum_of_dual (hf : IsF3Form f) {b b' : Fin m → Fin m → ZMod 3}
    (h : ∀ i j, f (b i) (b' j) = if i = j then 1 else 0) (x : Fin m → ZMod 3) :
    x = ∑ i, f x (b' i) • b i := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Subsingleton.elim _ _
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hli : LinearIndependent (ZMod 3) b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (f (b i)) hg
    simpa [map_sum, map_smul, h] using this
  set B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hB : ∀ i, B i = b' i := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  set x' := x - ∑ i, f x (b' i) • b i with hx'
  have h1 : ∀ j, f x' (b' j) = 0 := fun j => by
    simp only [hx', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left,
      LinearMap.BilinForm.smul_left, h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]
  have h2 : x' = 0 := hf.nondeg x' fun y => by
    rw [← B.sum_repr y, map_sum]
    simp only [map_smul, hB, h1, smul_zero, Finset.sum_const_zero]
  exact sub_eq_zero.1 h2

theorem exists_hyp_partner_perp (hf : IsF3Form f) {k : ℕ} {u : Fin k → Fin m → ZMod 3}
    (hu : ∀ i j, f (u i) (u j) = if i = j then 1 else 0) {z : Fin m → ZMod 3} (hz0 : z ≠ 0)
    (hzz : f z z = 0) (hzu : ∀ i, f z (u i) = 0) :
    ∃ y, f y y = 0 ∧ f z y = 1 ∧ ∀ i, f y (u i) = 0 := by
  obtain ⟨y', hy'U, hzy'⟩ := Beta.nondegOn_perpSub_orthonormal hf hu z (mem_perpSub.2 hzu) hz0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = (f z y')⁻¹ • y' := ⟨_, rfl⟩
  have hy₁u : ∀ i, f y₁ (u i) = 0 := fun i => by
    rw [hy₁, LinearMap.BilinForm.smul_left, mem_perpSub.1 hy'U i, mul_zero]
  have hzy₁ : f z y₁ = 1 := by rw [hy₁, LinearMap.BilinForm.smul_right, inv_mul_cancel₀ hzy']
  have hy₁z : f y₁ z = 1 := by rw [hf.symm]; exact hzy₁
  refine ⟨y₁ + f y₁ y₁ • z, ?_, ?_, fun i => ?_⟩
  · rw [norm_add_smul hf, hy₁z, hzz]
    linear_combination (f y₁ y₁) * three_eq_zero
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hzy₁, hzz, mul_zero,
      add_zero]
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hy₁u, hzu, mul_zero,
      add_zero]

theorem gram_diagF3 (δ : ZMod 3) (b : Fin m → Fin m → ZMod 3) :
    Matrix.of (fun i j => diagF3 m δ (b i) (b j)) =
      (Matrix.of fun i j => b j i).transpose * Matrix.diagonal (diagF3Entry m δ) *
        Matrix.of fun i j => b j i := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, diagF3_apply]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem det_gram_diagF3 (δ : ZMod 3) (b : Fin m → Fin m → ZMod 3) :
    (Matrix.of fun i j => diagF3 m δ (b i) (b j)).det =
      (Matrix.of fun i j => b j i).det ^ 2 * ∏ i, diagF3Entry m δ i := by
  rw [gram_diagF3, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem mulVec_of_eq_sum (b : Fin m → Fin m → ZMod 3) (g : Fin m → ZMod 3) :
    Matrix.mulVec (Matrix.of fun i j => b j i) g = ∑ c, g c • b c := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

@[expose] def NormOneCompl (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)) : Prop :=
  ∀ w w' z : Fin m → ZMod 3, f w w = 1 → f w' w' = 1 → f w w' = 0 → z ≠ 0 → f z z = 0 →
    f z w = 0 → f z w' = 0 → ∃ y, f y y = 1 ∧ f y w = 0 ∧ f y w' = 0 ∧ f y z = 0

set_option maxRecDepth 100000 in
theorem det_five_aux : ∀ c d : ZMod 3,
    (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, c] :
      Matrix (Fin 5) (Fin 5) (ZMod 3)).det = d ^ 2 * 2 → c = 1 ∨ d = 0 := by
  decide

theorem prod_diagF3Entry_five_two : ∏ i, diagF3Entry 5 2 i = 2 := by
  rw [Fin.prod_univ_five]
  decide

theorem normOneCompl_diagF3_five_two : NormOneCompl (diagF3 5 2) := by
  intro w w' z hw hw' hww' hz0 hzz hzw hzw'
  have hf : IsF3Form (diagF3 5 2) := isF3Form_diagF3 (by decide)
  have hw'w : diagF3 5 2 w' w = 0 := by rw [hf.symm]; exact hww'
  obtain ⟨z', hz'z', hzz', hz'u⟩ := exists_hyp_partner_perp hf (u := ![w, w'])
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [hw, hw', hww', hw'w]) hz0 hzz
    (fun i => by fin_cases i <;> simp [hzw, hzw'])
  have hz'w : diagF3 5 2 z' w = 0 := hz'u 0
  have hz'w' : diagF3 5 2 z' w' = 0 := hz'u 1
  obtain ⟨y, hy0, hyp⟩ := exists_ne_zero_perp (f := diagF3 5 2) (by norm_num : 4 < 5)
    ![w, w', z, z']
  have hyw : diagF3 5 2 y w = 0 := hyp 0
  have hyw' : diagF3 5 2 y w' = 0 := hyp 1
  have hyz : diagF3 5 2 y z = 0 := hyp 2
  have hyz' : diagF3 5 2 y z' = 0 := hyp 3
  have hwz : diagF3 5 2 w z = 0 := by rw [hf.symm]; exact hzw
  have hw'z : diagF3 5 2 w' z = 0 := by rw [hf.symm]; exact hzw'
  have hwz' : diagF3 5 2 w z' = 0 := by rw [hf.symm]; exact hz'w
  have hw'z' : diagF3 5 2 w' z' = 0 := by rw [hf.symm]; exact hz'w'
  have hwy : diagF3 5 2 w y = 0 := by rw [hf.symm]; exact hyw
  have hw'y : diagF3 5 2 w' y = 0 := by rw [hf.symm]; exact hyw'
  have hzy : diagF3 5 2 z y = 0 := by rw [hf.symm]; exact hyz
  have hz'y : diagF3 5 2 z' y = 0 := by rw [hf.symm]; exact hyz'
  have hz'z : diagF3 5 2 z' z = 1 := by rw [hf.symm]; exact hzz'
  set b : Fin 5 → Fin 5 → ZMod 3 := ![w, w', z, z', y] with hb
  have hG : (Matrix.of fun i j => diagF3 5 2 (b i) (b j)) =
      !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0;
        0, 0, 0, 0, diagF3 5 2 y y] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hw, hw', hww', hw'w, hzz, hzz', hz'z, hz'z', hwz, hw'z, hwz', hw'z', hwy, hw'y,
        hzy, hz'y, hzw, hzw', hz'w, hz'w', hyw, hyw', hyz, hyz']
  have hdet := det_gram_diagF3 2 b
  rw [hG, prod_diagF3Entry_five_two] at hdet
  rcases det_five_aux _ _ hdet with h1 | h0
  · exact ⟨y, h1, hyw, hyw', hyz⟩
  · exfalso
    obtain ⟨g, hg0, hg₀⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hg : g 0 • w + g 1 • w' + g 2 • z + g 3 • z' + g 4 • y = 0 := by
      rw [mulVec_of_eq_sum, Fin.sum_univ_five] at hg₀
      exact hg₀
    have e0 := congrArg (fun v => diagF3 5 2 v w) hg
    have e1 := congrArg (fun v => diagF3 5 2 v w') hg
    have e2 := congrArg (fun v => diagF3 5 2 v z') hg
    have e3 := congrArg (fun v => diagF3 5 2 v z) hg
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.zero_left, hw, hw'w, hzw, hz'w, hyw, hww', hw', hzw', hz'w', hyw',
      hwz', hw'z', hzz', hz'z', hyz', hwz, hw'z, hzz, hz'z, hyz, mul_zero, mul_one,
      add_zero, zero_add] at e0 e1 e2 e3
    rw [e0, e1, e2, e3, zero_smul, zero_smul, zero_smul, zero_smul, zero_add, zero_add,
      zero_add, zero_add] at hg
    have e4 : g 4 = 0 := (smul_eq_zero.1 hg).resolve_right hy0
    apply hg0
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4

variable (f) in
@[expose] def lineSet (u z : Fin m → ZMod 3) : Set (R3 f) :=
  {q | ∃ c : ZMod 3, reflBar f (u + c • z) = q}

theorem lineSet_smul {a : ZMod 3} (ha : a ≠ 0) (u z : Fin m → ZMod 3) :
    lineSet f u (a • z) = lineSet f u z := by
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c * a, by rw [smul_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c * a⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩

theorem zmod3_cases (c : ZMod 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  revert c; decide

theorem norm_line (hf : IsF3Form f) {u z : Fin m → ZMod 3} (hu : f u u = 1) (hzz : f z z = 0)
    (hzu : f z u = 0) (c : ZMod 3) : f (u + c • z) (u + c • z) = 1 := by
  rw [norm_add_smul hf, hf.symm u z, hzu, hzz, hu]
  ring

theorem lineSet_not_commute (hf : IsF3Form f) (hm : 4 ≤ m) {u z : Fin m → ZMod 3}
    (hu : f u u = 1) (hz0 : z ≠ 0) (hzz : f z z = 0) (hzu : f z u = 0) {c c' : ZMod 3}
    (hcc : c ≠ c') :
    reflBar f (u + c • z) * reflBar f (u + c' • z) ≠
      reflBar f (u + c' • z) * reflBar f (u + c • z) := by
  intro h
  rcases (reflBar_commute_iff hf hm (norm_line hf hu hzz hzu c)
    (norm_line hf hu hzz hzu c')).1 h with h1 | h1 | h1
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.smul_left, hu, hzz, hzu, hf.symm u z, hzu] at h1
    simp at h1
  · have : (c' - c) • z = 0 := by
      rw [sub_smul]
      linear_combination (norm := module) h1
    exact hcc (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hz0)).symm
  · have h2 := congrArg (fun v => f v u) h1
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.neg_left, hu, hzu, mul_zero, add_zero] at h2
    exact absurd h2 (by decide)

theorem exists_lineSet_eq (hf : IsF3Form f) (hm : 4 ≤ m) {a b : R3 f} (ha : a ∈ D3 f)
    (hb : b ∈ D3 f) (hab : b * a ≠ a * b) :
    ∃ u z, f u u = 1 ∧ z ≠ 0 ∧ f z z = 0 ∧ f z u = 0 ∧ a = reflBar f u ∧
      ({a, b, a * b * a} : Set (R3 f)) = lineSet f u z := by
  obtain ⟨u, hu, rfl⟩ := mem_D3_iff.1 ha
  obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 hb
  have huv : f u v ≠ 0 := fun h => hab ((reflBar_commute_iff hf hm hu hv).2 (Or.inl h)).symm
  obtain ⟨v', hv'⟩ : ∃ v', v' = f u v • v := ⟨_, rfl⟩
  have hv'v' : f v' v' = 1 := by rw [hv', norm_smul, mul_self_of_ne_zero huv, hv, mul_one]
  have huv' : f u v' = 1 := by
    rw [hv', LinearMap.BilinForm.smul_right, mul_self_of_ne_zero huv]
  have hv'u : f v' u = 1 := by rw [hf.symm]; exact huv'
  have hrv : reflBar f v' = reflBar f v := by rw [hv']; exact reflBar_smul huv v
  have hzz : f (v' - u) (v' - u) = 0 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hv'v', huv', hv'u,
      hu]
    ring
  have hzu : f (v' - u) u = 0 := by rw [LinearMap.BilinForm.sub_left, hv'u, hu, sub_self]
  have hz0 : v' - u ≠ 0 := fun h => hab (by
    rw [← hrv, sub_eq_zero.1 h])
  refine ⟨u, v' - u, hu, hz0, hzz, hzu, rfl, ?_⟩
  have e1 : reflBar f v = reflBar f (u + (1 : ZMod 3) • (v' - u)) := by
    rw [one_smul, add_sub_cancel, hrv]
  have e2 : reflBar f u * reflBar f v * reflBar f u =
      reflBar f (u + (2 : ZMod 3) • (v' - u)) := by
    rw [← hrv, reflBar_conj hf, act_refl hu, hv'u, one_smul, ← reflBar_neg]
    congr 1
    linear_combination (norm := module) -(three_eq_zero • v')
  ext q
  simp only [lineSet, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by rw [zero_smul, add_zero]⟩
    · exact ⟨1, e1.symm⟩
    · exact ⟨2, e2.symm⟩
  · rintro ⟨c, rfl⟩
    rcases zmod3_cases c with rfl | rfl | rfl
    · left; rw [zero_smul, add_zero]
    · right; left; exact e1.symm
    · right; right; exact e2.symm

theorem norm_comb (hf : IsF3Form f) (a b c : ZMod 3) (x y z : Fin m → ZMod 3) :
    f (a • x + b • y + c • z) (a • x + b • y + c • z) =
      a * a * f x x + b * b * f y y + c * c * f z z + 2 * a * b * f x y + 2 * a * c * f x z +
        2 * b * c * f y z := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hf.symm y x, hf.symm z x, hf.symm z y]
  ring

theorem reflBar_two_smul_add (u z : Fin m → ZMod 3) (c : ZMod 3) :
    reflBar f ((2 : ZMod 3) • u + c • z) = reflBar f (u + (-c) • z) := by
  rw [← reflBar_neg (u + (-c) • z)]
  congr 1
  linear_combination (norm := module) three_eq_zero • u

theorem line_eq_lineSet (hf : IsF3Form f) {u z : Fin m → ZMod 3} (hu : f u u = 1)
    (hzu : f z u = 0) :
    ({reflBar f u, reflBar f (u + z), reflBar f u * reflBar f (u + z) * reflBar f u} :
      Set (R3 f)) = lineSet f u z := by
  have e2 : reflBar f u * reflBar f (u + z) * reflBar f u = reflBar f (u + (2 : ZMod 3) • z) := by
    rw [reflBar_conj hf, act_refl hu, LinearMap.BilinForm.add_left, hu, hzu, add_zero, one_smul,
      ← reflBar_neg]
    congr 1
    linear_combination (norm := module) -(three_eq_zero • u) - three_eq_zero • z
  rw [e2]
  ext q
  simp only [lineSet, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by rw [zero_smul, add_zero]⟩
    · exact ⟨1, by rw [one_smul]⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨c, rfl⟩
    rcases zmod3_cases c with rfl | rfl | rfl
    · left; rw [zero_smul, add_zero]
    · right; left; rw [one_smul]
    · right; right; rfl

@[expose] def TwoLines {X : Type} [Group X] (S : Set X) : Prop :=
  ∃ a₁ b₁ a₂ b₂ : X, b₁ * a₁ ≠ a₁ * b₁ ∧ b₂ * a₂ ≠ a₂ * b₂ ∧
    S = {a₁, b₁, a₁ * b₁ * a₁} ∪ {a₂, b₂, a₂ * b₂ * a₂} ∧
    ∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set X), ∀ y ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set X),
      x * y = y * x

theorem twoLines_union_lineSet (hf : IsF3Form f) (hm : 4 ≤ m) {u₁ u₂ z : Fin m → ZMod 3}
    (hu₁ : f u₁ u₁ = 1) (hu₂ : f u₂ u₂ = 1) (hu₁u₂ : f u₁ u₂ = 0) (hz0 : z ≠ 0)
    (hzz : f z z = 0) (hzu₁ : f z u₁ = 0) (hzu₂ : f z u₂ = 0) :
    TwoLines (lineSet f u₁ z ∪ lineSet f u₂ z) := by
  have hnc : ∀ {u : Fin m → ZMod 3}, f u u = 1 → f z u = 0 →
      reflBar f (u + z) * reflBar f u ≠ reflBar f u * reflBar f (u + z) := fun hu hzu h =>
    lineSet_not_commute hf hm hu hz0 hzz hzu (c := 1) (c' := 0) (by decide)
      (by rwa [one_smul, zero_smul, add_zero])
  refine ⟨reflBar f u₁, reflBar f (u₁ + z), reflBar f u₂, reflBar f (u₂ + z), hnc hu₁ hzu₁,
    hnc hu₂ hzu₂, by rw [line_eq_lineSet hf hu₁ hzu₁, line_eq_lineSet hf hu₂ hzu₂], ?_⟩
  rw [line_eq_lineSet hf hu₁ hzu₁, line_eq_lineSet hf hu₂ hzu₂]
  rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
  refine (reflBar_commute_iff hf hm (norm_line hf hu₁ hzz hzu₁ c)
    (norm_line hf hu₂ hzz hzu₂ c')).2 (Or.inl ?_)
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hu₁u₂, hzz, hzu₂,
    hf.symm u₁ z, hzu₁]
  ring

theorem twoLines_of_tauChart {X Y Z : Type} [Group X] [Group Y] [Group Z] {A B : Set X}
    {c : X → Y} {ι : X → Z} (hBA : B ⊆ A) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b * a ∈ A)
    (hc : Set.InjOn c A) (hcc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a ↔ c a * c b = c b * c a)
    (hcτ : ∀ a ∈ A, ∀ b ∈ A, c (a * b * a) = c a * c b * c a)
    (hιc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a ↔ ι a * ι b = ι b * ι a)
    (hιτ : ∀ a ∈ A, ∀ b ∈ A, ι (a * b * a) = ι a * ι b * ι a) (h2 : TwoLines (c '' B)) :
    TwoLines (ι '' B) := by
  obtain ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, hS, hcomm⟩ := h2
  have hmem : ∀ y ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set Y) ∪ {a₂, b₂, a₂ * b₂ * a₂}, y ∈ c '' B :=
    fun y hy => by rw [hS]; exact hy
  obtain ⟨a₁', ha₁', rfl⟩ := hmem a₁ (Or.inl (Or.inl rfl))
  obtain ⟨b₁', hb₁', rfl⟩ := hmem b₁ (Or.inl (Or.inr (Or.inl rfl)))
  obtain ⟨a₂', ha₂', rfl⟩ := hmem a₂ (Or.inr (Or.inl rfl))
  obtain ⟨b₂', hb₂', rfl⟩ := hmem b₂ (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : ∀ {a b : X}, a ∈ B → b ∈ B → c a * c b * c a ∈ c '' B → a * b * a ∈ B := by
    intro a b ha hb h
    obtain ⟨t, ht, hct⟩ := h
    rw [← hcτ a (hBA ha) b (hBA hb)] at hct
    rwa [← hc (hBA ht) (hA a (hBA ha) b (hBA hb)) hct]
  have h₁ := h3 ha₁' hb₁' (hmem _ (Or.inl (Or.inr (Or.inr rfl))))
  have h₂ := h3 ha₂' hb₂' (hmem _ (Or.inr (Or.inr (Or.inr rfl))))
  have hB : B = {a₁', b₁', a₁' * b₁' * a₁'} ∪ {a₂', b₂', a₂' * b₂' * a₂'} := by
    ext s
    constructor
    · intro hs
      have hcs : c s ∈ c '' B := ⟨s, hs, rfl⟩
      rw [hS, ← hcτ a₁' (hBA ha₁') b₁' (hBA hb₁'), ← hcτ a₂' (hBA ha₂') b₂' (hBA hb₂')] at hcs
      have hinj : ∀ t ∈ B, c s = c t → s = t := fun t ht h => hc (hBA hs) (hBA ht) h
      rcases hcs with (h | h | h) | (h | h | h)
      · exact Or.inl (Or.inl (hinj _ ha₁' h))
      · exact Or.inl (Or.inr (Or.inl (hinj _ hb₁' h)))
      · exact Or.inl (Or.inr (Or.inr (hinj _ h₁ h)))
      · exact Or.inr (Or.inl (hinj _ ha₂' h))
      · exact Or.inr (Or.inr (Or.inl (hinj _ hb₂' h)))
      · exact Or.inr (Or.inr (Or.inr (hinj _ h₂ h)))
    · rintro ((rfl | rfl | rfl) | (rfl | rfl | rfl))
      exacts [ha₁', hb₁', h₁, ha₂', hb₂', h₂]
  have hL₁ : ι '' {a₁', b₁', a₁' * b₁' * a₁'} = {ι a₁', ι b₁', ι a₁' * ι b₁' * ι a₁'} := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      hιτ a₁' (hBA ha₁') b₁' (hBA hb₁')]
  have hL₂ : ι '' {a₂', b₂', a₂' * b₂' * a₂'} = {ι a₂', ι b₂', ι a₂' * ι b₂' * ι a₂'} := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      hιτ a₂' (hBA ha₂') b₂' (hBA hb₂')]
  have hcomm' : ∀ x ∈ ({a₁', b₁', a₁' * b₁' * a₁'} : Set X),
      ∀ y ∈ ({a₂', b₂', a₂' * b₂' * a₂'} : Set X), x * y = y * x := by
    intro x hx y hy
    have hxA : x ∈ A := hBA (hB ▸ Or.inl hx)
    have hyA : y ∈ A := hBA (hB ▸ Or.inr hy)
    refine (hcc x hxA y hyA).2 (hcomm _ ?_ _ ?_)
    · rcases hx with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hcτ _ (hBA ha₁') _ (hBA hb₁')))
    · rcases hy with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hcτ _ (hBA ha₂') _ (hBA hb₂')))
  refine ⟨ι a₁', ι b₁', ι a₂', ι b₂', fun h => hab₁ ?_, fun h => hab₂ ?_, ?_, ?_⟩
  · exact (hcc b₁' (hBA hb₁') a₁' (hBA ha₁')).1 ((hιc b₁' (hBA hb₁') a₁' (hBA ha₁')).2 h)
  · exact (hcc b₂' (hBA hb₂') a₂' (hBA ha₂')).1 ((hιc b₂' (hBA hb₂') a₂' (hBA ha₂')).2 h)
  · rw [hB, Set.image_union, hL₁, hL₂]
  · intro x hx y hy
    rw [← hL₁] at hx
    rw [← hL₂] at hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact (hιc x (hBA (hB ▸ Or.inl hx)) y (hBA (hB ▸ Or.inr hy))).1 (hcomm' x hx y hy)

section Five

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}

theorem eq_comb_five (hf : IsF3Form f) {w u₁ u₂ z z' : Fin 5 → ZMod 3} (hw : f w w = 1)
    (hu₁ : f u₁ u₁ = 1) (hu₂ : f u₂ u₂ = 1) (hwu₁ : f w u₁ = 0) (hwu₂ : f w u₂ = 0)
    (hu₁u₂ : f u₁ u₂ = 0) (hzz : f z z = 0) (hz'z' : f z' z' = 0) (hzz' : f z z' = 1)
    (hzw : f z w = 0) (hzu₁ : f z u₁ = 0) (hzu₂ : f z u₂ = 0) (hz'w : f z' w = 0)
    (hz'u₁ : f z' u₁ = 0) (hz'u₂ : f z' u₂ = 0) (x : Fin 5 → ZMod 3) :
    x = f x w • w + f x u₁ • u₁ + f x u₂ • u₂ + f x z' • z + f x z • z' := by
  have hu₁w : f u₁ w = 0 := by rw [hf.symm]; exact hwu₁
  have hu₂w : f u₂ w = 0 := by rw [hf.symm]; exact hwu₂
  have hu₂u₁ : f u₂ u₁ = 0 := by rw [hf.symm]; exact hu₁u₂
  have hwz : f w z = 0 := by rw [hf.symm]; exact hzw
  have hu₁z : f u₁ z = 0 := by rw [hf.symm]; exact hzu₁
  have hu₂z : f u₂ z = 0 := by rw [hf.symm]; exact hzu₂
  have hwz' : f w z' = 0 := by rw [hf.symm]; exact hz'w
  have hu₁z' : f u₁ z' = 0 := by rw [hf.symm]; exact hz'u₁
  have hu₂z' : f u₂ z' = 0 := by rw [hf.symm]; exact hz'u₂
  have hz'z : f z' z = 1 := by rw [hf.symm]; exact hzz'
  have key := eq_sum_of_dual hf (b := ![w, u₁, u₂, z, z']) (b' := ![w, u₁, u₂, z', z])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [hw, hu₁, hu₂, hwu₁, hwu₂, hu₁u₂, hzz, hz'z', hzz', hzw, hzu₁, hzu₂, hz'w, hz'u₁,
          hz'u₂, hu₁w, hu₂w, hu₂u₁, hwz, hu₁z, hu₂z, hwz', hu₁z', hu₂z', hz'z]) x
  rw [Fin.sum_univ_five] at key
  exact key

theorem eq_smul_of_perp_five (hf : IsF3Form f) {w u₁ u₂ z s : Fin 5 → ZMod 3} (hw : f w w = 1)
    (hu₁ : f u₁ u₁ = 1) (hu₂ : f u₂ u₂ = 1) (hwu₁ : f w u₁ = 0) (hwu₂ : f w u₂ = 0)
    (hu₁u₂ : f u₁ u₂ = 0) (hz0 : z ≠ 0) (hzz : f z z = 0) (hzw : f z w = 0)
    (hzu₁ : f z u₁ = 0) (hzu₂ : f z u₂ = 0) (hsw : f s w = 0) (hsu₁ : f s u₁ = 0)
    (hsu₂ : f s u₂ = 0) (hsz : f s z = 0) : ∃ c : ZMod 3, s = c • z := by
  have hu₁w : f u₁ w = 0 := by rw [hf.symm]; exact hwu₁
  have hu₂w : f u₂ w = 0 := by rw [hf.symm]; exact hwu₂
  have hu₂u₁ : f u₂ u₁ = 0 := by rw [hf.symm]; exact hu₁u₂
  obtain ⟨z', hz'z', hzz', hz'u⟩ := exists_hyp_partner_perp hf (u := ![w, u₁, u₂])
    (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hw, hu₁, hu₂, hwu₁, hwu₂, hu₁u₂, hu₁w, hu₂w, hu₂u₁])
    hz0 hzz (fun i => by fin_cases i <;> simp [hzw, hzu₁, hzu₂])
  have key := eq_comb_five hf hw hu₁ hu₂ hwu₁ hwu₂ hu₁u₂ hzz hz'z' hzz' hzw hzu₁ hzu₂ (hz'u 0)
    (hz'u 1) (hz'u 2) s
  simp only [hsw, hsu₁, hsu₂, hsz, zero_smul, zero_add, add_zero] at key
  exact ⟨_, key⟩

theorem sq_add_sq_eq_one : ∀ a b : ZMod 3, a * a + b * b = 1 →
    (a = 1 ∨ a = 2) ∧ b = 0 ∨ a = 0 ∧ (b = 1 ∨ b = 2) := by
  decide

theorem muPt_eq_union_lineSet (hf : IsF3Form f) {w u₁ u₂ z : Fin 5 → ZMod 3} (hw : f w w = 1)
    (hu₁ : f u₁ u₁ = 1) (hu₂ : f u₂ u₂ = 1) (hwu₁ : f w u₁ = 0) (hwu₂ : f w u₂ = 0)
    (hu₁u₂ : f u₁ u₂ = 0) (hz0 : z ≠ 0) (hzz : f z z = 0) (hzw : f z w = 0)
    (hzu₁ : f z u₁ = 0) (hzu₂ : f z u₂ = 0) :
    muPt f w z = lineSet f u₁ z ∪ lineSet f u₂ z := by
  have hu₁w : f u₁ w = 0 := by rw [hf.symm]; exact hwu₁
  have hu₂w : f u₂ w = 0 := by rw [hf.symm]; exact hwu₂
  have hu₂u₁ : f u₂ u₁ = 0 := by rw [hf.symm]; exact hu₁u₂
  have hu₁z : f u₁ z = 0 := by rw [hf.symm]; exact hzu₁
  have hu₂z : f u₂ z = 0 := by rw [hf.symm]; exact hzu₂
  obtain ⟨z', hz'z', hzz', hz'u⟩ := exists_hyp_partner_perp hf (u := ![w, u₁, u₂])
    (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hw, hu₁, hu₂, hwu₁, hwu₂, hu₁u₂, hu₁w, hu₂w, hu₂u₁])
    hz0 hzz (fun i => by fin_cases i <;> simp [hzw, hzu₁, hzu₂])
  ext q
  constructor
  · rintro ⟨v, hv, hvw, hvz, rfl⟩
    have key := eq_comb_five hf hw hu₁ hu₂ hwu₁ hwu₂ hu₁u₂ hzz hz'z' hzz' hzw hzu₁ hzu₂
      (hz'u 0) (hz'u 1) (hz'u 2) v
    simp only [hvw, hvz, zero_smul, zero_add, add_zero] at key
    generalize f v u₁ = a, f v u₂ = b, f v z' = c at key
    subst key
    rw [norm_comb hf, hu₁, hu₂, hzz, hu₁u₂, hu₁z, hu₂z] at hv
    rcases sq_add_sq_eq_one a b (by linear_combination hv) with ⟨ha | ha, rfl⟩ | ⟨rfl, hb | hb⟩
    · left
      exact ⟨c, by rw [ha, zero_smul, add_zero, one_smul]⟩
    · left
      exact ⟨-c, by rw [ha, zero_smul, add_zero, reflBar_two_smul_add]⟩
    · right
      exact ⟨c, by rw [hb, zero_smul, zero_add, one_smul]⟩
    · right
      exact ⟨-c, by rw [hb, zero_smul, zero_add, reflBar_two_smul_add]⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨_, norm_line hf hu₁ hzz hzu₁ c, ?_, ?_, rfl⟩
      · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu₁w, hzw, mul_zero,
          add_zero]
      · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu₁z, hzz, mul_zero,
          add_zero]
    · refine ⟨_, norm_line hf hu₂ hzz hzu₂ c, ?_, ?_, rfl⟩
      · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu₂w, hzw, mul_zero,
          add_zero]
      · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu₂z, hzz, mul_zero,
          add_zero]

theorem exists_muPt_eq_union_lineSet (hf : IsF3Form f) (hN : NormOneCompl f)
    {w z : Fin 5 → ZMod 3} (hw : f w w = 1) (hz : IsIsoPt f w z) :
    ∃ u₁ u₂, f u₁ u₁ = 1 ∧ f u₂ u₂ = 1 ∧ f w u₁ = 0 ∧ f w u₂ = 0 ∧ f u₁ u₂ = 0 ∧
      f z u₁ = 0 ∧ f z u₂ = 0 ∧ muPt f w z = lineSet f u₁ z ∪ lineSet f u₂ z := by
  obtain ⟨hz0, hzz, hzw⟩ := hz
  obtain ⟨u₁, hu₁, hu₁w, hu₁z⟩ := exists_norm_one_perp_isotropic hf (by norm_num) hw hz0 hzz hzw
  have hwu₁ : f w u₁ = 0 := by rw [hf.symm]; exact hu₁w
  have hzu₁ : f z u₁ = 0 := by rw [hf.symm]; exact hu₁z
  obtain ⟨u₂, hu₂, hu₂w, hu₂u₁, hu₂z⟩ := hN w u₁ z hw hu₁ hwu₁ hz0 hzz hzw hzu₁
  have hwu₂ : f w u₂ = 0 := by rw [hf.symm]; exact hu₂w
  have hu₁u₂ : f u₁ u₂ = 0 := by rw [hf.symm]; exact hu₂u₁
  have hzu₂ : f z u₂ = 0 := by rw [hf.symm]; exact hu₂z
  exact ⟨u₁, u₂, hu₁, hu₂, hwu₁, hwu₂, hu₁u₂, hzu₁, hzu₂,
    muPt_eq_union_lineSet hf hw hu₁ hu₂ hwu₁ hwu₂ hu₁u₂ hz0 hzz hzw hzu₁ hzu₂⟩

theorem add_one_ne_self (c : ZMod 3) : c + 1 ≠ c := by
  revert c; decide

theorem exists_eq_muPt_of_twoLines (hf : IsF3Form f) {w : Fin 5 → ZMod 3} (hw : f w w = 1)
    {S : Set (R3 f)} (hS : S ⊆ LocalClass (D3 f) (reflBar f w)) (h2 : TwoLines S) :
    ∃ z, IsIsoPt f w z ∧ S = muPt f w z := by
  have hm : 4 ≤ 5 := by norm_num
  obtain ⟨a₁, b₁, a₂, b₂, hab₁, hab₂, rfl, hcomm⟩ := h2
  have hD : ∀ q ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set (R3 f)) ∪ {a₂, b₂, a₂ * b₂ * a₂}, q ∈ D3 f :=
    fun q hq => (hS hq).1
  obtain ⟨u₁, z₁, hu₁, hz₁0, hz₁z₁, hz₁u₁, rfl, hL₁⟩ := exists_lineSet_eq hf hm
    (hD _ (Or.inl (Or.inl rfl))) (hD _ (Or.inl (Or.inr (Or.inl rfl)))) hab₁
  obtain ⟨u₂, z₂, hu₂, hz₂0, hz₂z₂, hz₂u₂, rfl, hL₂⟩ := exists_lineSet_eq hf hm
    (hD _ (Or.inr (Or.inl rfl))) (hD _ (Or.inr (Or.inr (Or.inl rfl)))) hab₂
  rw [hL₁, hL₂] at hS hcomm ⊢
  have hperp : ∀ {u z : Fin 5 → ZMod 3}, f u u = 1 → f z z = 0 → f z u = 0 →
      lineSet f u z ⊆ LocalClass (D3 f) (reflBar f w) → f u w = 0 ∧ f z w = 0 := by
    intro u z hu hzz hzu hsub
    have h0 := (reflBar_mem_localClass_iff hf hm hw (norm_line hf hu hzz hzu 0)).1
      (hsub ⟨0, rfl⟩)
    have h1 := (reflBar_mem_localClass_iff hf hm hw (norm_line hf hu hzz hzu 1)).1
      (hsub ⟨1, rfl⟩)
    rw [zero_smul, add_zero] at h0
    rw [one_smul, LinearMap.BilinForm.add_left, h0, zero_add] at h1
    exact ⟨h0, h1⟩
  obtain ⟨hu₁w, hz₁w⟩ := hperp hu₁ hz₁z₁ hz₁u₁ (Set.subset_union_left.trans hS)
  obtain ⟨hu₂w, hz₂w⟩ := hperp hu₂ hz₂z₂ hz₂u₂ (Set.subset_union_right.trans hS)
  have hpair : ∀ c c' : ZMod 3, f (u₁ + c • z₁) (u₂ + c' • z₂) = 0 := by
    intro c c'
    have hnc := lineSet_not_commute hf hm hu₁ hz₁0 hz₁z₁ hz₁u₁ (add_one_ne_self c)
    rcases (reflBar_commute_iff hf hm (norm_line hf hu₁ hz₁z₁ hz₁u₁ c)
      (norm_line hf hu₂ hz₂z₂ hz₂u₂ c')).1 (hcomm _ ⟨c, rfl⟩ _ ⟨c', rfl⟩) with h | h | h
    · exact h
    · have hc2 := hcomm _ ⟨c + 1, rfl⟩ _ ⟨c', rfl⟩
      rw [h] at hc2
      exact (hnc hc2).elim
    · have hc2 := hcomm _ ⟨c + 1, rfl⟩ _ ⟨c', rfl⟩
      rw [h, reflBar_neg] at hc2
      exact (hnc hc2).elim
  have h00 := hpair 0 0
  have h10 := hpair 1 0
  have h01 := hpair 0 1
  have h11 := hpair 1 1
  simp only [zero_smul, add_zero, one_smul, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right] at h00 h10 h01 h11
  rw [h00, zero_add] at h10 h01
  rw [h00, h10, h01] at h11
  simp only [zero_add] at h11
  have hwu₁ : f w u₁ = 0 := by rw [hf.symm]; exact hu₁w
  have hwu₂ : f w u₂ = 0 := by rw [hf.symm]; exact hu₂w
  have hz₂u₁ : f z₂ u₁ = 0 := by rw [hf.symm]; exact h01
  have hz₂z₁ : f z₂ z₁ = 0 := by rw [hf.symm]; exact h11
  obtain ⟨a, ha⟩ := eq_smul_of_perp_five hf hw hu₁ hu₂ hwu₁ hwu₂ h00 hz₁0 hz₁z₁ hz₁w hz₁u₁ h10
    hz₂w hz₂u₁ hz₂u₂ hz₂z₁
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hz₂0 ha
  rw [ha, lineSet_smul ha0]
  exact ⟨z₁, ⟨hz₁0, hz₁z₁, hz₁w⟩, (muPt_eq_union_lineSet hf hw hu₁ hu₂ hwu₁ hwu₂ h00 hz₁0
    hz₁z₁ hz₁w hz₁u₁ h10).symm⟩

theorem sq3_eq_one : ∀ a b c : ZMod 3, a * a + b * b + c * c = 1 →
    (a ≠ 0 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b ≠ 0 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c ≠ 0) := by
  decide

theorem reflBar_smul_add_mem_lineSet {a : ZMod 3} (ha : a ≠ 0) (u z : Fin 5 → ZMod 3)
    (c : ZMod 3) : reflBar f (a • u + c • z) ∈ lineSet f u z := by
  rcases zmod3_cases a with rfl | rfl | rfl
  · exact absurd rfl ha
  · exact ⟨c, by rw [one_smul]⟩
  · exact ⟨-c, (reflBar_two_smul_add u z c).symm⟩

theorem inter_localClass_eq_muPt_of_isAdm (hf : IsF3Form f) {M : Set (R3 f)}
    (hM : IsAdm (D3 f) M) {w₀ u u' z₀ : Fin 5 → ZMod 3} (hw₀ : f w₀ w₀ = 1) (hu : f u u = 1)
    (hu' : f u' u' = 1) (hw₀u : f w₀ u = 0) (hw₀u' : f w₀ u' = 0) (huu' : f u u' = 0)
    (hz₀0 : z₀ ≠ 0) (hz₀z₀ : f z₀ z₀ = 0) (hz₀w₀ : f z₀ w₀ = 0) (hz₀u : f z₀ u = 0)
    (hz₀u' : f z₀ u' = 0) (hg₀ : reflBar f w₀ ∈ M)
    (hS₀ : M ∩ LocalClass (D3 f) (reflBar f w₀) = muPt f w₀ z₀) (c : ZMod 3) :
    M ∩ LocalClass (D3 f) (reflBar f (u + c • z₀)) = muPt f (u + c • z₀) z₀ := by
  have hm : 4 ≤ 5 := by norm_num
  have huw₀ : f u w₀ = 0 := by rw [hf.symm]; exact hw₀u
  have hu'w₀ : f u' w₀ = 0 := by rw [hf.symm]; exact hw₀u'
  have hu'u : f u' u = 0 := by rw [hf.symm]; exact huu'
  have huz₀ : f u z₀ = 0 := by rw [hf.symm]; exact hz₀u
  have hu'z₀ : f u' z₀ = 0 := by rw [hf.symm]; exact hz₀u'
  have hmem : ∀ {v : Fin 5 → ZMod 3}, f v v = 1 → f v w₀ = 0 → f v z₀ = 0 → reflBar f v ∈ M :=
    fun hv hvw hvz => (hS₀.symm ▸ (⟨_, hv, hvw, hvz, rfl⟩ : reflBar f _ ∈ muPt f w₀ z₀) :
      reflBar f _ ∈ M ∩ LocalClass (D3 f) (reflBar f w₀)).1
  obtain ⟨k, hkdef⟩ : ∃ k, k = u + c • z₀ := ⟨_, rfl⟩
  rw [← hkdef]
  have hk : f k k = 1 := hkdef ▸ norm_line hf hu hz₀z₀ hz₀u c
  have hkw₀ : f k w₀ = 0 := by
    rw [hkdef, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, huw₀, hz₀w₀,
      mul_zero, add_zero]
  have hkz₀ : f k z₀ = 0 := by
    rw [hkdef, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, huz₀, hz₀z₀,
      mul_zero, add_zero]
  obtain ⟨z', hz', hSk⟩ := exists_isIsoPt_of_isAdm hf hm hM hk (hmem hk hkw₀ hkz₀)
  have h1 : reflBar f w₀ ∈ muPt f k z' := hSk ▸ ⟨hg₀, reflBar_mem_localClass hf hm hk hw₀
    (by rw [hf.symm]; exact hkw₀)⟩
  have hw₀z' : f w₀ z' = 0 := ((reflBar_mem_muPt_iff hf hm hw₀).1 h1).2
  have h2 : ∀ c' : ZMod 3, f (u' + c' • z₀) z' = 0 := fun c' => by
    have hv := norm_line hf hu' hz₀z₀ hz₀u' c'
    have hvw : f (u' + c' • z₀) w₀ = 0 := by
      rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu'w₀, hz₀w₀, mul_zero,
        add_zero]
    have hvz : f (u' + c' • z₀) z₀ = 0 := by
      rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu'z₀, hz₀z₀, mul_zero,
        add_zero]
    have hvk : f (u' + c' • z₀) k = 0 := by
      rw [hkdef]
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hu'u, hu'z₀, hz₀u,
        hz₀z₀]
      ring
    have h3 : reflBar f (u' + c' • z₀) ∈ muPt f k z' :=
      hSk ▸ ⟨hmem hv hvw hvz, reflBar_mem_localClass hf hm hk hv hvk⟩
    exact ((reflBar_mem_muPt_iff hf hm hv).1 h3).2
  have hu'z' : f u' z' = 0 := by simpa using h2 0
  have hz₀z' : f z₀ z' = 0 := by
    have h := h2 1
    rwa [one_smul, LinearMap.BilinForm.add_left, hu'z', zero_add] at h
  have huz' : f u z' = 0 := by
    have h : f z' k = 0 := hz'.2.2
    rw [hkdef, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hf.symm z' z₀,
      hz₀z', mul_zero, add_zero, hf.symm] at h
    exact h
  obtain ⟨a, ha⟩ := eq_smul_of_perp_five hf hw₀ hu hu' hw₀u hw₀u' huu' hz₀0 hz₀z₀ hz₀w₀ hz₀u
    hz₀u' (by rw [hf.symm]; exact hw₀z') (by rw [hf.symm]; exact huz')
    (by rw [hf.symm]; exact hu'z') (by rw [hf.symm]; exact hz₀z')
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hz'.1 ha
  rw [hSk, ha, muPt_smul ha0]

theorem eq_sPt_of_isAdm_five (hf : IsF3Form f) (hN : NormOneCompl f) {M : Set (R3 f)}
    (hM : IsAdm (D3 f) M) {w₀ : Fin 5 → ZMod 3} (hw₀ : f w₀ w₀ = 1) (hg₀ : reflBar f w₀ ∈ M) :
    ∃ z, z ≠ 0 ∧ f z z = 0 ∧ M = sPt f z := by
  have hm : 4 ≤ 5 := by norm_num
  obtain ⟨z₀, ⟨hz₀0, hz₀z₀, hz₀w₀⟩, hS₀⟩ := exists_isIsoPt_of_isAdm hf hm hM hw₀ hg₀
  obtain ⟨u₁, u₂, hu₁, hu₂, hw₀u₁, hw₀u₂, hu₁u₂, hz₀u₁, hz₀u₂, hμ⟩ :=
    exists_muPt_eq_union_lineSet hf hN hw₀ ⟨hz₀0, hz₀z₀, hz₀w₀⟩
  have hpt₁ := inter_localClass_eq_muPt_of_isAdm hf hM hw₀ hu₁ hu₂ hw₀u₁ hw₀u₂ hu₁u₂ hz₀0
    hz₀z₀ hz₀w₀ hz₀u₁ hz₀u₂ hg₀ hS₀
  have hu₁w₀ : f u₁ w₀ = 0 := by rw [hf.symm]; exact hw₀u₁
  have hu₂w₀ : f u₂ w₀ = 0 := by rw [hf.symm]; exact hw₀u₂
  have hu₂u₁ : f u₂ u₁ = 0 := by rw [hf.symm]; exact hu₁u₂
  have hw₀z₀ : f w₀ z₀ = 0 := by rw [hf.symm]; exact hz₀w₀
  have hu₁z₀ : f u₁ z₀ = 0 := by rw [hf.symm]; exact hz₀u₁
  have hu₂z₀ : f u₂ z₀ = 0 := by rw [hf.symm]; exact hz₀u₂
  refine ⟨z₀, hz₀0, hz₀z₀, Set.Subset.antisymm ?_ ?_⟩
  ·
    intro y hy
    obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 (hM.1 hy)
    refine ⟨v, hv, ?_, rfl⟩
    by_contra hvz
    set t := -(f v u₁) * (f v z₀)⁻¹ with ht
    have hvt : f v (u₁ + t • z₀) = 0 := by
      rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, ht, mul_assoc,
        inv_mul_cancel₀ hvz]
      ring
    have hmem : reflBar f v ∈ M ∩ LocalClass (D3 f) (reflBar f (u₁ + t • z₀)) :=
      ⟨hy, reflBar_mem_localClass hf hm (norm_line hf hu₁ hz₀z₀ hz₀u₁ t) hv hvt⟩
    rw [hpt₁ t] at hmem
    exact hvz ((reflBar_mem_muPt_iff hf hm hv).1 hmem).2
  ·
    rintro _ ⟨v, hv, hvz, rfl⟩
    obtain ⟨z', hz'z', hz₀z', hz'u⟩ := exists_hyp_partner_perp hf (u := ![w₀, u₁, u₂])
      (fun i j => by
        fin_cases i <;> fin_cases j <;>
          simp [hw₀, hu₁, hu₂, hw₀u₁, hw₀u₂, hu₁u₂, hu₁w₀, hu₂w₀, hu₂u₁])
      hz₀0 hz₀z₀ (fun i => by fin_cases i <;> simp [hz₀w₀, hz₀u₁, hz₀u₂])
    have key := eq_comb_five hf hw₀ hu₁ hu₂ hw₀u₁ hw₀u₂ hu₁u₂ hz₀z₀ hz'z' hz₀z' hz₀w₀ hz₀u₁
      hz₀u₂ (hz'u 0) (hz'u 1) (hz'u 2) v
    rw [hvz, zero_smul, add_zero] at key
    generalize f v w₀ = a₀, f v u₁ = a₁, f v u₂ = a₂, f v z' = c at key
    subst key
    have hn : a₀ * a₀ + a₁ * a₁ + a₂ * a₂ = 1 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hw₀,
        hu₁, hu₂, hw₀u₁, hw₀u₂, hu₁u₂, hu₁w₀, hu₂w₀, hu₂u₁, hw₀z₀, hu₁z₀, hu₂z₀, hz₀w₀, hz₀u₁,
        hz₀u₂, hz₀z₀] at hv
      linear_combination hv
    rcases sq3_eq_one a₀ a₁ a₂ hn with ⟨ha₀, rfl, rfl⟩ | ⟨rfl, ha₁, rfl⟩ | ⟨rfl, rfl, ha₂⟩
    ·
      simp only [zero_smul, add_zero] at hv ⊢
      have hv' : f (a₀ • w₀ + c • z₀) u₁ = 0 := by
        rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
          LinearMap.BilinForm.smul_left, hw₀u₁, hz₀u₁, mul_zero, mul_zero, add_zero]
      have hv'' : f (a₀ • w₀ + c • z₀) z₀ = 0 := by
        rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
          LinearMap.BilinForm.smul_left, hw₀z₀, hz₀z₀, mul_zero, mul_zero, add_zero]
      have h0 := hpt₁ 0
      rw [zero_smul, add_zero] at h0
      have hm' : reflBar f (a₀ • w₀ + c • z₀) ∈ muPt f u₁ z₀ := ⟨_, hv, hv', hv'', rfl⟩
      rw [← h0] at hm'
      exact hm'.1
    · simp only [zero_smul, zero_add, add_zero] at hv ⊢
      have hm' : reflBar f (a₁ • u₁ + c • z₀) ∈ muPt f w₀ z₀ :=
        hμ ▸ Or.inl (reflBar_smul_add_mem_lineSet ha₁ u₁ z₀ c)
      rw [← hS₀] at hm'
      exact hm'.1
    · simp only [zero_smul, zero_add] at hv ⊢
      have hm' : reflBar f (a₂ • u₂ + c • z₀) ∈ muPt f w₀ z₀ :=
        hμ ▸ Or.inr (reflBar_smul_add_mem_lineSet ha₂ u₂ z₀ c)
      rw [← hS₀] at hm'
      exact hm'.1

section Local

variable {G : Type} [Group G] {D : Set G}

theorem localClass_localClass_eq_inter (d f₀ : G) :
    LocalClass (LocalClass D d) f₀ = LocalClass D d ∩ LocalClass D f₀ := by
  ext s
  simp only [mem_localClass, Set.mem_inter_iff]
  tauto

theorem exists_inter_eq_muPt (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D) (hf : IsF3Form f)
    (hN : NormOneCompl f) (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f)
    {x f₀ : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) (hf₀ : f₀ ∈ muSet D d x)
    {w : Fin 5 → ZMod 3} (hw : f w w = 1) (hwg : reflBar f w = (φ ∘ lqMap D d) f₀) :
    ∃ ζ, IsIsoPt f w ζ ∧
      (φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass (D3 f) (reflBar f w) = muPt f w ζ := by
  have hm : 4 ≤ 5 := by norm_num
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  have hf₀d : f₀ ∈ LocalClass D d := hf₀.1
  have hf₀D : f₀ ∈ D := hf₀d.1
  have hdf₀ : d ∈ LocalClass D f₀ := mem_localClass_symm hd hf₀d
  have hxf₀ : x ∈ LocalClass D f₀ := mem_localClass_symm hx hf₀.2
  obtain ⟨φ₀, hφ₀⟩ := exists_localQuotientEquiv_of_mem hP hd hf₀D φ hφ
  have hι₀ := isChart_of_localQuotientEquiv hP
    (Pair.starImage_injective_of_simple hP hZ hS hf₀D) φ₀ hφ₀
  have hA := localClass_localClass_eq_inter (D := D) d f₀
  have hAd : LocalClass (LocalClass D d) f₀ ⊆ LocalClass D d := hA ▸ Set.inter_subset_left
  have hAf : LocalClass (LocalClass D d) f₀ ⊆ LocalClass D f₀ := hA ▸ Set.inter_subset_right
  have hBA : LocalClass (LocalClass D d) f₀ ∩ LocalClass D x ⊆ LocalClass (LocalClass D d) f₀ :=
    Set.inter_subset_left
  have hB : LocalClass (LocalClass D d) f₀ ∩ LocalClass D x = muSet (LocalClass D f₀) d x := by
    ext s
    simp only [muSet, mem_localClass, Set.mem_inter_iff]
    tauto
  obtain ⟨a, ha, hag⟩ := mem_D3_iff.1 (hι₀.mem hdf₀)
  obtain ⟨b, hb, hbg⟩ := mem_D3_iff.1 (hι₀.mem hxf₀)
  have hba : reflBar f b * reflBar f a ≠ reflBar f a * reflBar f b := by
    rw [hag, hbg]
    exact fun h => hxd ((hι₀.comm_iff x hxf₀ d hdf₀).2 h)
  obtain ⟨z', hz', hz'μ⟩ : ∃ z', IsIsoPt f a z' ∧
      muPt f a z' = muSet (D3 f) (reflBar f a) (reflBar f b) := by
    have hfam : muSet (D3 f) (reflBar f a) (reflBar f b) ∈ muFamily (D3 f) (reflBar f a) :=
      ⟨_, reflBar_mem_D3 hb, hba, rfl⟩
    rw [muFamily_D3 hf hm ha] at hfam
    exact hfam
  obtain ⟨u₁, u₂, hu₁, hu₂, -, -, hu₁u₂, hz'u₁, hz'u₂, hμ⟩ :=
    exists_muPt_eq_union_lineSet hf hN ha hz'
  have h2 : TwoLines ((φ₀ ∘ lqMap D f₀) '' (LocalClass (LocalClass D d) f₀ ∩ LocalClass D x)) := by
    rw [hB, hι₀.image_muSet hdf₀ hxf₀, ← hag, ← hbg, ← hz'μ, hμ]
    exact twoLines_union_lineSet hf hm hu₁ hu₂ hu₁u₂ hz'.1 hz'.2.1 hz'u₁ hz'u₂
  have h2' := twoLines_of_tauChart hBA
    (fun a ha b hb => hA ▸ ⟨Pair.mul_mul_mem_localClass_of_mem hP (hAd ha) (hAd hb),
      Pair.mul_mul_mem_localClass_of_mem hP (hAf ha) (hAf hb)⟩)
    (hι₀.injOn.mono hAf) (fun a ha b hb => hι₀.comm_iff a (hAf ha) b (hAf hb))
    (fun a ha b hb => by simp only [Function.comp_apply, lqMap_mul_mul (hAf ha) (hAf hb),
      map_mul])
    (fun a ha b hb => hι.comm_iff a (hAd ha) b (hAd hb))
    (fun a ha b hb => by simp only [Function.comp_apply, lqMap_mul_mul (hAd ha) (hAd hb),
      map_mul]) h2
  have hinter := image_muSet_inter hι hf₀
  rw [← hwg] at hinter
  rw [hinter]
  exact exists_eq_muPt_of_twoLines hf hw (hinter ▸ Set.inter_subset_right) h2'

theorem isAdm_image_muSet_five (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D) (hf : IsF3Form f)
    (hN : NormOneCompl f) (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f)
    {x : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) :
    IsAdm (D3 f) ((φ ∘ lqMap D d) '' muSet D d x) := by
  have hm : 4 ≤ 5 := by norm_num
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  refine ⟨hι.image_subset (muSet_subset_localClass d x), ?_⟩
  rintro _ ⟨f₀, hf₀, rfl⟩
  obtain ⟨w, hw, hwg⟩ := mem_D3_iff.1 (hι.mem hf₀.1)
  obtain ⟨ζ, hζ, hM⟩ := exists_inter_eq_muPt hP hZ hS hd hf hN φ hφ hx hxd hf₀ hw hwg
  have hwζ : f w ζ = 0 := by rw [hf.symm]; exact hζ.2.2
  have hu : f (w + ζ) (w + ζ) = 1 := by rw [norm_add hf, hw, hwζ, hζ.2.1]; ring
  refine ⟨reflBar f (w + ζ), reflBar_mem_D3 hu, ?_, ?_⟩
  · rw [← hwg]
    exact reflBar_add_not_commute hf hm hw hζ
  · rw [← hwg, hM, muSet_eq_muPt hf hm hw hu, add_sub_cancel_left]

end Local

end Five

end CFSG.Fischer.Classification.LocalU

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer LocalR3 F3 LocalU

theorem classicalConclusion_of_localR3_five_of_normOneCompl {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f) (hN : NormOneCompl f)
    (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f) :
    ClassicalConclusion G D := by
  have hH' := hH
  obtain ⟨hP, hZ, hS⟩ := hH'
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  obtain ⟨f₀, hf₀⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
  obtain ⟨w₀, hw₀, hwg⟩ := mem_D3_iff.1 (hι.mem hf₀.1)
  obtain ⟨z, hz0, hzz, hM⟩ := eq_sPt_of_isAdm_five hf hN
    (isAdm_image_muSet_five hP hZ hS hd hf hN φ hφ hx hxd) hw₀
    (by rw [hwg]; exact ⟨f₀, hf₀, rfl⟩)
  refine classicalConclusion_of_localR3_of_muSet hH hnab hd (by norm_num) hf φ hφ hx hxd hz0 hzz
    ?_
  rw [← hM, Set.image_comp, lqMap_image (muSet_subset_localClass d x)]

theorem classicalConclusion_of_localR3_diagF3_five_two {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (φ : LocalQuotient D d ≃* R3 (diagF3 5 2)) (hφ : φ '' LocalImages D d = D3 (diagF3 5 2)) :
    ClassicalConclusion G D :=
  classicalConclusion_of_localR3_five_of_normOneCompl hH hnab hd (isF3Form_diagF3 (by decide))
    normOneCompl_diagF3_five_two φ hφ

theorem classicalConclusion_of_localR3_five_of_ncard_36 {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f)
    (h36 : (D3 f).ncard = 36) (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f) :
    ClassicalConclusion G D := by
  rcases R3_five_cases hf with ⟨h45, -⟩ | ⟨-, ψ, hψ⟩
  · omega
  · refine classicalConclusion_of_localR3_diagF3_five_two hH hnab hd (φ.trans ψ) ?_
    rw [MulEquiv.coe_trans, Set.image_comp, hφ, hψ]

end CFSG.Fischer.Classification
