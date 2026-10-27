module

public import CFSG.LieType.SeitzGeneration.OrthLow

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

section Torus

variable {K : Type} [Field K]

@[expose] def rotMat (b c α β : K) : Matrix (Fin 2) (Fin 2) K := !![α, -(c * β); β, α + b * β]

theorem det_rotMat (b c α β : K) : (rotMat b c α β).det = α ^ 2 + b * α * β + c * β ^ 2 := by
  rw [rotMat, Matrix.det_fin_two_of]
  ring

theorem rotMat_mul (b c α β α' β' : K) : rotMat b c α β * rotMat b c α' β' =
    rotMat b c (α * α' - c * β * β') (α * β' + β * α' + b * β * β') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rotMat_one (b c : K) : rotMat b c 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat]

theorem rotMat_det_ne_zero {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {α β : K}
    (h : (α, β) ≠ 0) : α ^ 2 + b * α * β + c * β ^ 2 ≠ 0 := by
  by_cases hβ : β = 0
  · subst hβ
    have hα : α ≠ 0 := fun hα => h (by rw [hα]; rfl)
    simpa using hα
  · intro h0
    apply hirr (α / β)
    field_simp
    linear_combination h0

@[expose] def anisoTorus (b c : K) : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∃ α β : K, (g : Matrix (Fin 2) (Fin 2) K) = rotMat b c α β}
  mul_mem' := by
    rintro g h ⟨α, β, hg⟩ ⟨α', β', hh⟩
    exact ⟨_, _, by rw [Units.val_mul, hg, hh, rotMat_mul]⟩
  one_mem' := ⟨1, 0, by rw [Units.val_one, rotMat_one]⟩
  inv_mem' := by
    rintro g ⟨α, β, hg⟩
    have hN : α ^ 2 + b * α * β + c * β ^ 2 ≠ 0 := by
      rw [← det_rotMat, ← hg]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    refine ⟨(α + b * β) / (α ^ 2 + b * α * β + c * β ^ 2),
      -β / (α ^ 2 + b * α * β + c * β ^ 2), Units.inv_eq_of_mul_eq_one_right ?_⟩
    have hinv := mul_inv_cancel₀ hN
    rw [hg, rotMat_mul, ← rotMat_one b c]
    congr 1
    · linear_combination hinv
    · ring

theorem card_anisoTorus [Finite K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (anisoTorus b c) = Nat.card K ^ 2 - 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hunit : ∀ v : K × K, v ≠ 0 → IsUnit (rotMat b c v.1 v.2).det := fun v hv => by
    rw [det_rotMat]
    exact isUnit_iff_ne_zero.mpr (rotMat_det_ne_zero hirr hv)
  let f : ↥{v : K × K | v ≠ 0} → anisoTorus b c := fun v =>
    ⟨Matrix.nonsingInvUnit (rotMat b c v.1.1 v.1.2) (hunit v.1 v.2), v.1.1, v.1.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun g => ?_⟩
    · have h := congrArg (fun g : anisoTorus b c =>
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hvw
      have h0 := congrFun (congrFun h 0) 0
      have h1 := congrFun (congrFun h 1) 0
      exact Subtype.ext (Prod.ext h0 h1)
    · obtain ⟨α, β, hg⟩ := g.2
      have hne : (α, β) ≠ 0 := by
        intro h0
        have hα : α = 0 := congrArg Prod.fst h0
        have hβ : β = 0 := congrArg Prod.snd h0
        have h00 : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 0 := by
          rw [hg, hα, hβ]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [rotMat]
        exact not_isUnit_zero (h00 ▸ (g : GL (Fin 2) K).isUnit)
      exact ⟨⟨(α, β), hne⟩, Subtype.ext (Units.ext hg.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Set.card_ne_eq,
    Fintype.card_prod, ← Nat.card_eq_fintype_card, sq]

theorem exists_rotMat_order [Finite K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ∃ α β : K, α ^ 2 + b * α * β + c * β ^ 2 = 1 ∧ rotMat b c α β ^ p = 1 ∧
      rotMat b c α β ≠ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (GL (Fin 2) K) := inferInstance
  have hdvd : p ∣ Nat.card (anisoTorus b c) := by
    rw [card_anisoTorus hirr]
    obtain ⟨t, ht⟩ : ∃ t, Nat.card K = t + 1 :=
      ⟨Nat.card K - 1, by have := Finite.card_pos (α := K); omega⟩
    rw [ht] at hpq ⊢
    have h : (t + 1) ^ 2 - 1 = (t + 1 + 1) * t := by
      have : (t + 1) ^ 2 = (t + 1 + 1) * t + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    rw [h]
    exact hpq.mul_right t
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := anisoTorus b c) p hdvd
  obtain ⟨α, β, hαβ⟩ := g.2
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := fun h => by
    rw [h, orderOf_one] at hg
    exact hp.one_lt.ne' hg.symm
  have hmat : rotMat b c α β ^ p = 1 := by
    have := congrArg (fun g : anisoTorus b c =>
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hgp
    simpa [hαβ] using this
  refine ⟨α, β, ?_, hmat, fun h1 => hg1 (Subtype.ext (Units.ext (by rw [hαβ, h1]; rfl)))⟩
  have hdet : (α ^ 2 + b * α * β + c * β ^ 2) ^ p = 1 := by
    rw [← det_rotMat, ← Matrix.det_pow, hmat, Matrix.det_one]
  by_contra hne
  have h1 := dvd_card_sub_one_of_pow_eq_one hp hdet hne
  have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h1
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  have : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
  rw [this] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem rotMat_isom (b c α β : K) (hN : α ^ 2 + b * α * β + c * β ^ 2 = 1) (y : Fin 2 → K) :
    ((rotMat b c α β).mulVec y 0) ^ 2 + b * (rotMat b c α β).mulVec y 0 *
        (rotMat b c α β).mulVec y 1 + c * ((rotMat b c α β).mulVec y 1) ^ 2 =
      y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2 := by
  simp only [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  linear_combination (y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2) * hN

end Torus

end CFSG.LieType.SeitzGeneration
