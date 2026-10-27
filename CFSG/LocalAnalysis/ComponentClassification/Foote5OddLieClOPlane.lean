module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.ite_ne {α : Type*} {x y : Fin d} (h : x ≠ y) (a b : α) :
    (if x = y then a else b) = b := by
  simp [h]

theorem ClO.ite_self {α : Type*} {x : Fin d} (a b : α) : (if x = x then a else b) = a := by
  simp

theorem ClO.plane_isometry {w₀ w₁ a b c e : K} (hw₀ : w₀ ≠ 0) (hw₁ : w₁ ≠ 0)
    (h1 : w₀ * a ^ 2 + w₁ * c ^ 2 = w₀) (h2 : w₀ * a * b + w₁ * c * e = 0)
    (h3 : w₀ * b ^ 2 + w₁ * e ^ 2 = w₁) :
    e = (a * e - b * c) * a ∧ w₀ * b = -((a * e - b * c) * (w₁ * c)) ∧
      (a * e - b * c) ^ 2 = 1 := by
  refine ⟨?_, by linear_combination a * h2 - b * h1, ?_⟩
  · have h : w₀ * ((a * e - b * c) * a - e) = 0 := by linear_combination e * h1 - c * h2
    linear_combination -((mul_eq_zero.1 h).resolve_left hw₀)
  · have h : w₀ * w₁ * ((a * e - b * c) ^ 2 - 1) = 0 := by
      linear_combination (w₀ * b ^ 2 + w₁ * e ^ 2) * h1 + w₀ * h3 -
        (w₀ * a * b + w₁ * c * e) * h2
    linear_combination (mul_eq_zero.1 h).resolve_left (mul_ne_zero hw₀ hw₁)

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {j₀ j₁ : Fin d}

include hw in
theorem ClO.oIsoBlock_pair_off {R : GL (Fin d) K} (hR : R ∈ oIsoBlock K hw {j₀, j₁}) {x y : Fin d}
    (hxy : x ∉ ({j₀, j₁} : Finset (Fin d)) ∨ y ∉ ({j₀, j₁} : Finset (Fin d))) :
    (R : Matrix (Fin d) (Fin d) K) x y = if x = y then 1 else 0 :=
  ((mem_oIsoBlock_iff hw).1 hR).2 x y hxy

include hw in
theorem ClO.mul_apply_pair {R R' : GL (Fin d) K} (hR : R ∈ oIsoBlock K hw {j₀, j₁})
    (hj : j₀ ≠ j₁) {x y : Fin d} (hx : x ∈ ({j₀, j₁} : Finset (Fin d))) :
    ((R : Matrix (Fin d) (Fin d) K) * R') x y =
      (R : Matrix (Fin d) (Fin d) K) x j₀ * (R' : Matrix (Fin d) (Fin d) K) j₀ y +
        (R : Matrix (Fin d) (Fin d) K) x j₁ * (R' : Matrix (Fin d) (Fin d) K) j₁ y := by
  rw [Matrix.mul_apply, Finset.sum_eq_add j₀ j₁ hj (fun z _ hz => by
    have hz' : z ∉ ({j₀, j₁} : Finset (Fin d)) := by simp [hz.1, hz.2]
    have hxz : x ≠ z := fun e => hz' (e ▸ hx)
    rw [ClO.oIsoBlock_pair_off hw hR (Or.inr hz'), ClO.ite_ne hxz, zero_mul]) (by simp)
    (by simp)]

include hw in
theorem ClO.oIsoBlock_pair_rel {R : GL (Fin d) K} (hR : R ∈ oIsoBlock K hw {j₀, j₁})
    (hj : j₀ ≠ j₁) :
    w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₀ ^ 2 +
        w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀ ^ 2 = w j₀ ∧
      w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₁ +
        w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀ * (R : Matrix (Fin d) (Fin d) K) j₁ j₁ = 0 ∧
      w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₁ ^ 2 +
        w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₁ ^ 2 = w j₁ := by
  have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 ((mem_oIsoBlock_iff hw).1 hR).1
  rw [coe_diagGL, Matrix.mul_assoc] at hiso
  have hent : ∀ x y, x ∈ ({j₀, j₁} : Finset (Fin d)) →
      (R : Matrix (Fin d) (Fin d) K) j₀ x * (w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ y) +
        (R : Matrix (Fin d) (Fin d) K) j₁ x * (w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ y) =
        diagonal w x y := by
    intro x y hx
    have e := congrFun (congrFun hiso x) y
    rw [Matrix.mul_apply] at e
    simp only [transpose_apply, diagonal_mul] at e
    rwa [Finset.sum_eq_add j₀ j₁ hj (fun z _ hz => by
      have hz' : z ∉ ({j₀, j₁} : Finset (Fin d)) := by simp [hz.1, hz.2]
      have hzx : z ≠ x := fun e => hz' (e ▸ hx)
      rw [ClO.oIsoBlock_pair_off hw hR (Or.inl hz'), ClO.ite_ne hzx, zero_mul]) (by simp)
      (by simp)] at e
  have hj0 : j₀ ∈ ({j₀, j₁} : Finset (Fin d)) := by simp
  have hj1 : j₁ ∈ ({j₀, j₁} : Finset (Fin d)) := by simp
  have e00 := hent j₀ j₀ hj0
  have e01 := hent j₀ j₁ hj0
  have e11 := hent j₁ j₁ hj1
  rw [diagonal_apply_eq] at e00 e11
  rw [diagonal_apply_ne _ hj] at e01
  refine ⟨by linear_combination e00, by linear_combination e01, by linear_combination e11⟩

include hw in
theorem ClO.mul_apply_off_left {A : GL (Fin d) K} (hA : A ∈ oIsoBlock K hw {j₀, j₁})
    (B : Matrix (Fin d) (Fin d) K) {x : Fin d} (hx : x ∉ ({j₀, j₁} : Finset (Fin d))) (y : Fin d) :
    ((A : Matrix (Fin d) (Fin d) K) * B) x y = B x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x (fun z _ hz => by
    rw [ClO.oIsoBlock_pair_off hw hA (Or.inl hx), ClO.ite_ne (Ne.symm hz), zero_mul]) (by simp),
    ClO.oIsoBlock_pair_off hw hA (Or.inl hx), ClO.ite_self, one_mul]

include hw in
theorem ClO.mul_apply_off_right {B : GL (Fin d) K} (hB : B ∈ oIsoBlock K hw {j₀, j₁})
    (A : Matrix (Fin d) (Fin d) K) (x : Fin d) {y : Fin d}
    (hy : y ∉ ({j₀, j₁} : Finset (Fin d))) :
    (A * (B : Matrix (Fin d) (Fin d) K)) x y = A x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single y (fun z _ hz => by
    rw [ClO.oIsoBlock_pair_off hw hB (Or.inr hy), ClO.ite_ne hz, mul_zero]) (by simp),
    ClO.oIsoBlock_pair_off hw hB (Or.inr hy), ClO.ite_self, mul_one]

include hw in
theorem ClO.proper_of_odd (h2 : (2 : K) ≠ 0) {R : GL (Fin d) K}
    (hR : R ∈ oIsoBlock K hw {j₀, j₁}) (hj : j₀ ≠ j₁) {m : ℕ} (hm : Odd m) (hRm : R ^ m = 1) :
    (R : Matrix (Fin d) (Fin d) K) j₁ j₁ = (R : Matrix (Fin d) (Fin d) K) j₀ j₀ ∧
      w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₁ =
        -(w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀) := by
  obtain ⟨h1, h2', h3⟩ := ClO.oIsoBlock_pair_rel hw hR hj
  obtain ⟨he, hb, hδ⟩ := ClO.plane_isometry (hw j₀) (hw j₁) h1 h2' h3
  rw [pow_two] at hδ
  rcases mul_self_eq_one_iff.1 hδ with hδ1 | hδ1
  · rw [hδ1, one_mul] at he
    rw [hδ1, one_mul] at hb
    exact ⟨he, hb⟩
  exfalso
  rw [hδ1, neg_one_mul] at he
  rw [hδ1, neg_one_mul, neg_neg] at hb
  have hj0 : j₀ ∈ ({j₀, j₁} : Finset (Fin d)) := by simp
  have hj1 : j₁ ∈ ({j₀, j₁} : Finset (Fin d)) := by simp
  have hbc : (R : Matrix (Fin d) (Fin d) K) j₀ j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀ =
      1 - (R : Matrix (Fin d) (Fin d) K) j₀ j₀ ^ 2 := by
    have : w j₀ * ((R : Matrix (Fin d) (Fin d) K) j₀ j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀ -
        (1 - (R : Matrix (Fin d) (Fin d) K) j₀ j₀ ^ 2)) = 0 := by
      linear_combination (R : Matrix (Fin d) (Fin d) K) j₁ j₀ * hb + h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hw j₀))
  have hR2 : R * R = 1 := by
    apply Units.ext
    ext x y
    rw [Units.val_mul, Units.val_one]
    by_cases hx : x ∈ ({j₀, j₁} : Finset (Fin d))
    · by_cases hy : y ∈ ({j₀, j₁} : Finset (Fin d))
      · rw [ClO.mul_apply_pair hw hR hj hx]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rw [one_apply_eq]; linear_combination hbc
        · rw [one_apply_ne hj, he]; ring
        · rw [one_apply_ne (Ne.symm hj), he]; ring
        · rw [one_apply_eq, he]; linear_combination hbc
      · rw [ClO.mul_apply_off_right hw hR _ x hy, ClO.oIsoBlock_pair_off hw hR (Or.inr hy),
          one_apply]
    · rw [ClO.mul_apply_off_left hw hR _ hx, ClO.oIsoBlock_pair_off hw hR (Or.inl hx), one_apply]
  obtain ⟨k, rfl⟩ := hm
  have hR1 : R = 1 := by
    rw [pow_succ, pow_mul, pow_two, hR2, one_pow, one_mul] at hRm
    exact hRm
  have e0 : (R : Matrix (Fin d) (Fin d) K) j₀ j₀ = 1 := by rw [hR1]; simp
  have e1 : (R : Matrix (Fin d) (Fin d) K) j₁ j₁ = 1 := by rw [hR1]; simp
  rw [e0, e1] at he
  exact h2 (by linear_combination he)

include hw in
theorem ClO.commute_of_proper {R R' : GL (Fin d) K} (hR : R ∈ oIsoBlock K hw {j₀, j₁})
    (hR' : R' ∈ oIsoBlock K hw {j₀, j₁}) (hj : j₀ ≠ j₁)
    (hp : (R : Matrix (Fin d) (Fin d) K) j₁ j₁ = (R : Matrix (Fin d) (Fin d) K) j₀ j₀ ∧
      w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₁ =
        -(w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀))
    (hp' : (R' : Matrix (Fin d) (Fin d) K) j₁ j₁ = (R' : Matrix (Fin d) (Fin d) K) j₀ j₀ ∧
      w j₀ * (R' : Matrix (Fin d) (Fin d) K) j₀ j₁ =
        -(w j₁ * (R' : Matrix (Fin d) (Fin d) K) j₁ j₀)) :
    R * R' = R' * R := by
  have hbc : (R : Matrix (Fin d) (Fin d) K) j₀ j₁ * (R' : Matrix (Fin d) (Fin d) K) j₁ j₀ =
      (R' : Matrix (Fin d) (Fin d) K) j₀ j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀ := by
    have : w j₀ * ((R : Matrix (Fin d) (Fin d) K) j₀ j₁ * (R' : Matrix (Fin d) (Fin d) K) j₁ j₀ -
        (R' : Matrix (Fin d) (Fin d) K) j₀ j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀) = 0 := by
      linear_combination (R' : Matrix (Fin d) (Fin d) K) j₁ j₀ * hp.2 -
        (R : Matrix (Fin d) (Fin d) K) j₁ j₀ * hp'.2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hw j₀))
  apply Units.ext
  ext x y
  rw [Units.val_mul, Units.val_mul]
  by_cases hx : x ∈ ({j₀, j₁} : Finset (Fin d))
  · by_cases hy : y ∈ ({j₀, j₁} : Finset (Fin d))
    · rw [ClO.mul_apply_pair hw hR hj hx, ClO.mul_apply_pair hw hR' hj hx]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · linear_combination hbc
      · rw [hp.1, hp'.1]; ring
      · rw [hp.1, hp'.1]; ring
      · rw [hp.1, hp'.1]; linear_combination -hbc
    · rw [ClO.mul_apply_off_right hw hR' _ x hy, ClO.mul_apply_off_right hw hR _ x hy,
        ClO.oIsoBlock_pair_off hw hR (Or.inr hy), ClO.oIsoBlock_pair_off hw hR' (Or.inr hy)]
  · rw [ClO.mul_apply_off_left hw hR _ hx, ClO.mul_apply_off_left hw hR' _ hx,
      ClO.oIsoBlock_pair_off hw hR (Or.inl hx), ClO.oIsoBlock_pair_off hw hR' (Or.inl hx)]

theorem ClO.commute_of_plane [Finite K] (h2 : (2 : K) ≠ 0) (hker : OKer (oQ (diagGL hw)))
    (hj : j₀ ≠ j₁) (hd : ∃ x : Fin d, x ∉ ({j₀, j₁} : Finset (Fin d)))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRo : ∀ y ∈ Ro, ∃ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
      R ∈ oIsoBlock K hw {j₀, j₁} ∧ y = oκ _ (linPair R hR)) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  obtain ⟨x₀, hx₀⟩ := hd
  have hprop : ∀ y ∈ Ro, ∀ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
      R ∈ oIsoBlock K hw {j₀, j₁} → y = oκ _ (linPair R hR) →
      (R : Matrix (Fin d) (Fin d) K) j₁ j₁ = (R : Matrix (Fin d) (Fin d) K) j₀ j₀ ∧
        w j₀ * (R : Matrix (Fin d) (Fin d) K) j₀ j₁ =
          -(w j₁ * (R : Matrix (Fin d) (Fin d) K) j₁ j₀) := by
    intro y hy R hR hRJ hyR
    have hodd := ClSp.odd_orderOf_of_mem hRodd hy
    obtain ⟨-, c, hc⟩ := hker _ (by
      rw [map_pow, ← hyR]
      exact pow_orderOf_eq_one y : oκ _ (linPair R hR ^ orderOf y) = 1)
    obtain ⟨hl, -⟩ := pow_left_of_right_eq_one (g := linPair R hR) rfl (orderOf y)
    rw [hl, linPair_left] at hc
    have hRm : R ^ orderOf y = 1 := by
      have hmem : R ^ orderOf y ∈ oIsoBlock K hw {j₀, j₁} := pow_mem hRJ _
      have e := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) x₀ x₀) hc
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e
      rw [ClO.oIsoBlock_pair_off hw hmem (Or.inl hx₀), ClO.ite_self] at e
      have hc1 : c = 1 := Units.ext e
      rw [← hc, hc1, map_one]
    exact ClO.proper_of_odd hw h2 hRJ hj hodd hRm
  intro r₁ h₁ r₂ h₂
  obtain ⟨R, hR, hRJ, hR₁⟩ := hRo r₁ h₁
  obtain ⟨R', hR', hRJ', hR₂⟩ := hRo r₂ h₂
  have hc := ClO.commute_of_proper hw hRJ hRJ' hj (hprop r₁ h₁ R hR hRJ hR₁)
    (hprop r₂ h₂ R' hR' hRJ' hR₂)
  rw [hR₁, hR₂, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (linPair R hR).val.left * glFieldAut (Fin d) K (linPair R hR).val.right
        (linPair R' hR').val.left = (linPair R' hR').val.left *
      glFieldAut (Fin d) K (linPair R' hR').val.right (linPair R hR).val.left
    rw [linPair_right, linPair_right, map_one, MulAut.one_apply, MulAut.one_apply, linPair_left,
      linPair_left, hc]
  · change (linPair R hR).val.right * (linPair R' hR').val.right =
      (linPair R' hR').val.right * (linPair R hR).val.right
    rw [linPair_right, linPair_right]

end CFSG.ComponentClassification.Foote5.OddLieCore
