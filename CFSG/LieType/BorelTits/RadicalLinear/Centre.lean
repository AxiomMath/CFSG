module

public import CFSG.LieType.BorelTits.RadicalLinear.Supported
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalGen

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix CFSG.StandardType.GGOppRad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem apply_eq_zero_of_commute_transvection {g : SpecialLinearGroup ι K} {i j : ι} (hij : i ≠ j)
    (h : (g : Matrix ι ι K) * (SpecialLinearGroup.transvection hij (1 : K) : Matrix ι ι K) =
      (SpecialLinearGroup.transvection hij (1 : K) : Matrix ι ι K) * (g : Matrix ι ι K)) :
    (∀ c, c ≠ i → (g : Matrix ι ι K) c i = 0) ∧
      (∀ a, a ≠ j → (g : Matrix ι ι K) j a = 0) := by
  rw [SpecialLinearGroup.transvection_coe] at h
  have h1 : (g : Matrix ι ι K) * Matrix.single i j (1 : K) =
      Matrix.single i j (1 : K) * (g : Matrix ι ι K) := add_left_cancel (by
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] using h)
  constructor <;> intro x hx
  · have := congrFun (congrFun h1 x) j
    rwa [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hx,
      mul_one] at this
  · have := congrFun (congrFun h1 i) x
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, Matrix.single_mul_apply_same, one_mul] at this
    exact this.symm

theorem mem_center_stdU_iff [Finite K] {ℓ : ι → ℕ} {lo hi : ℕ} (hlo : ∀ a, lo ≤ ℓ a)
    (hhi : ∀ a, ℓ a ≤ hi) (hlo' : ∃ a, ℓ a = lo) (hhi' : ∃ a, ℓ a = hi) (hlohi : lo < hi)
    (g : stdU (K := K) ℓ) :
    g ∈ Subgroup.center (stdU (K := K) ℓ) ↔
      ∀ c a, ¬ (ℓ c = lo ∧ ℓ a = hi) →
        ((g : SpecialLinearGroup ι K) : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a := by
  classical
  constructor
  · intro hg c a hnot
    have comm : ∀ {i j : ι} (hij : i ≠ j) (hlt : ℓ i < ℓ j),
        (g : Matrix ι ι K) * (SpecialLinearGroup.transvection hij (1 : K) : Matrix ι ι K) =
        (SpecialLinearGroup.transvection hij (1 : K) : Matrix ι ι K) * (g : Matrix ι ι K) := by
      intro i j hij hlt
      have ht := transvection_mem_stdU hij hlt (1 : K)
      exact congrArg (fun z : stdU (K := K) ℓ => ((z : SpecialLinearGroup ι K) : Matrix ι ι K))
        (Subgroup.mem_center_iff.mp hg ⟨_, ht⟩).symm
    by_cases hlt : ℓ c < ℓ a
    · have hca : c ≠ a := fun h => (ne_of_lt hlt) (congrArg ℓ h)
      by_cases ha : ℓ a = hi
      · obtain ⟨b, hb⟩ := hlo'
        have hlt' : ℓ b < ℓ c := by
          rw [hb]; exact lt_of_le_of_ne (hlo c) (fun h => hnot ⟨h.symm, ha⟩)
        have hbc : b ≠ c := fun h => (ne_of_lt hlt') (congrArg ℓ h)
        rw [((apply_eq_zero_of_commute_transvection hbc (comm hbc hlt')).2 a (Ne.symm hca)),
          Matrix.one_apply_ne hca]
      · obtain ⟨b, hb⟩ := hhi'
        have hlt' : ℓ a < ℓ b := by
          rw [hb]; exact lt_of_le_of_ne (hhi a) ha
        have hab : a ≠ b := fun h => (ne_of_lt hlt') (congrArg ℓ h)
        rw [((apply_eq_zero_of_commute_transvection hab (comm hab hlt')).1 c hca),
          Matrix.one_apply_ne hca]
    · exact mem_stdU_iff.mp g.2 c a hlt
  · intro hg
    refine Subgroup.mem_center_iff.mpr fun h0 => ?_
    let X : Matrix ι ι K := ((g : SpecialLinearGroup ι K) : Matrix ι ι K) - 1
    let Y : Matrix ι ι K := ((h0 : SpecialLinearGroup ι K) : Matrix ι ι K) - 1
    have hX : ∀ c a, X c a ≠ 0 → ℓ c = lo ∧ ℓ a = hi := by
      intro c a hne; by_contra hbad
      exact hne (by simp only [X, Matrix.sub_apply, hg c a hbad, sub_self])
    have hY : ∀ c a, Y c a ≠ 0 → ℓ c < ℓ a := by
      intro c a hne; by_contra hbad
      exact hne (by simp only [Y, Matrix.sub_apply, mem_stdU_iff.mp h0.2 c a hbad, sub_self])
    have hXY : X * Y = 0 := by
      ext c a
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hx : X c b = 0 <;> by_cases hy : Y b a = 0 <;> simp [hx, hy]
      obtain ⟨-, hb⟩ := hX c b hx; have h1 := hY b a hy; have h2 := hhi a; omega
    have hYX : Y * X = 0 := by
      ext c a
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hx : Y c b = 0 <;> by_cases hy : X b a = 0 <;> simp [hx, hy]
      have h1 := hY c b hx; obtain ⟨h2, -⟩ := hX b a hy; have h3 := hlo c; omega
    have hcomm : ((h0 : SpecialLinearGroup ι K) : Matrix ι ι K) *
        ((g : SpecialLinearGroup ι K) : Matrix ι ι K) =
        ((g : SpecialLinearGroup ι K) : Matrix ι ι K) *
          ((h0 : SpecialLinearGroup ι K) : Matrix ι ι K) := by
      have hg' : ((g : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 + X := by simp only [X]; abel
      have hh' : ((h0 : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 + Y := by simp only [Y]; abel
      rw [hg', hh']
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hYX, hXY]
      abel
    refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun c a => ?_)
    simpa [X, Y, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] using
      congrFun (congrFun hcomm c) a

theorem card_center_stdU [Finite K] {ℓ : ι → ℕ} {lo hi : ℕ} (hlo : ∀ a, lo ≤ ℓ a)
    (hhi : ∀ a, ℓ a ≤ hi) (hlo' : ∃ a, ℓ a = lo) (hhi' : ∃ a, ℓ a = hi) (hlohi : lo < hi) :
    Nat.card (Subgroup.center (stdU (K := K) ℓ)) =
      Nat.card K ^ ((Finset.univ.filter fun a => ℓ a = lo).card *
        (Finset.univ.filter fun a => ℓ a = hi).card) := by
  classical
  let T : Finset (ι × ι) := (Finset.univ.filter fun a => ℓ a = lo) ×ˢ
    (Finset.univ.filter fun a => ℓ a = hi)
  have hT : ∀ p ∈ T, ℓ p.1 < ℓ p.2 := by
    rintro ⟨c, a⟩ hp
    simp only [T, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [hp.1, hp.2]; exact hlohi
  let e : Subgroup.center (stdU (K := K) ℓ) ≃
      {g : SpecialLinearGroup ι K // ∀ c a, (c, a) ∉ T →
        ((g : SpecialLinearGroup ι K) : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a} :=
    { toFun := fun g => ⟨g.1.1, fun c a h =>
        (mem_center_stdU_iff hlo hhi hlo' hhi' hlohi g.1).mp g.2 c a (by simpa [T] using h)⟩
      invFun := fun s => ⟨⟨s.1, by
          rw [mem_stdU_iff]
          exact fun c a hlt => s.2 c a (by
            intro hmem
            obtain ⟨hc, ha⟩ : ℓ c = lo ∧ ℓ a = hi := by simpa [T] using hmem
            exact hlt (by rw [hc, ha]; exact hlohi))⟩,
        by
          rw [mem_center_stdU_iff hlo hhi hlo' hhi' hlohi]
          exact fun c a h => s.2 c a (by simpa [T] using h)⟩
      left_inv := fun g => rfl
      right_inv := fun s => rfl }
  rw [Nat.card_congr e, card_supported ℓ T hT]; simp only [T, Finset.card_product]

end CFSG.LieType.BorelTits.RadicalLinear
