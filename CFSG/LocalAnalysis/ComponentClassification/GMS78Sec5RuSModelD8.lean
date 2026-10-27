module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCoset
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuJ
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModelSec

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

namespace RuSModel

variable {G : Type} [Group G]

@[expose] def dElt (X U : G) (d : Fin 8) : G := U ^ (d.val / 2) * X ^ (d.val % 2)

theorem dElt_mul {X U z : G} (hX : X * X = 1) (hXU : X * U = U * (U * (U * (z * X))))
    (hU4 : U * (U * (U * U)) = z) (hzX : z * X = X * z) (hzU : z * U = U * z) (hzz : z * z = 1)
    (d e : Fin 8) :
    dElt X U d * dElt X U e = dElt X U (dMul d e) * (if dOvf d e then z else 1) := by
  have r1 : ∀ w, X * (X * w) = w := fun w => by rw [← mul_assoc, hX, one_mul]
  have r2 : ∀ w, X * (U * w) = U * (U * (U * (z * (X * w)))) := fun w => by
    rw [← mul_assoc, hXU]; simp only [mul_assoc]
  have r6 : ∀ w, U * (U * (U * (U * w))) = z * w := fun w => by
    rw [← hU4]; simp only [mul_assoc]
  have r7 : ∀ w, z * (X * w) = X * (z * w) := fun w => by rw [← mul_assoc, hzX, mul_assoc]
  have r8 : ∀ w, z * (U * w) = U * (z * w) := fun w => by rw [← mul_assoc, hzU, mul_assoc]
  have r9 : ∀ w, z * (z * w) = w := fun w => by rw [← mul_assoc, hzz, one_mul]
  fin_cases d <;> fin_cases e <;>
    simp (config := { decide := true }) only [dElt, dMul, pow_succ, pow_zero, one_mul, mul_one,
      mul_assoc, hX, hXU, hU4, hzX, hzz, r2, r6, r7, r8, ↓reduceIte, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.zero_div, Nat.zero_mod]

theorem fin8Of_val (d : Fin 8) : fin8Of d.val = d := by
  ext
  simp [fin8Of, Nat.mod_eq_of_lt d.isLt]

theorem dCode_eq : ∀ d : Fin 8, dCode d =
    linComp ((linComp (dCode 2))^[d.val / 2] linId) (if d.val % 2 = 1 then dCode 1 else linId) := by
  intro d
  fin_cases d <;> rfl

theorem adMat_dCode : ∀ d : Fin 8, adMat (dCode d) =
    [[1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 69, 10, 48, 32, 64, 129],
      [3, 2, 69, 10, 117, 171, 74, 129], [3, 2, 12, 8, 222, 171, 74, 130],
      [1, 2, 12, 8, 210, 33, 66, 130], [1, 2, 79, 10, 243, 33, 66, 131],
      [3, 2, 79, 10, 188, 168, 72, 131], [3, 2, 4, 8, 20, 168, 72, 128]].getD d.val [] := by
  decide +kernel

theorem fix_xu : ∀ m < 256, maskApply (adMat (dCode 1)) m = m →
    maskApply (adMat (dCode 2)) m = m → m = 0 ∨ m = 2 := by
  rw [adMat_dCode 1, adMat_dCode 2]
  decide +kernel

theorem norm_sixteen :
    let A := maskApply (adMat (dCode 2))
    let w := 16 ^^^ maskApply (adMat (dCode 1)) 16
    w ^^^ A w ^^^ A (A w) ^^^ A (A (A w)) = 2 := by
  simp only [adMat_dCode]
  decide

theorem fix_code_xy : ∀ t : Fin 8, linApply (dCode 1) t = t → linApply (dCode 7) t = t →
    t = 0 ∨ t = 1 := by
  decide

theorem dCode_one_mem : dCode 1 ∈ invList := by decide +kernel

theorem dCode_seven_mem : dCode 7 ∈ invList := by decide +kernel

theorem dCode_two : dCode 2 = linComp (dCode 1) (dCode 7) := by decide

theorem dCode_two_pow : (linComp (dCode 2))^[4] linId = linId := by decide

end RuSModel

open RuSModel

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem code_mul {g h : G} {r s : Lin8} (hhN : h ∈ normalizer (R : Set G))
    (hg : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b))
    (hh : ∀ b ∈ gmsA L T, ν (h * b * h⁻¹) = linApply s (ν b)) :
    ∀ b ∈ gmsA L T, ν (g * h * b * (g * h)⁻¹) = linApply (linComp r s) (ν b) := by
  intro b hb
  rw [show g * h * b * (g * h)⁻¹ = g * (h * b * h⁻¹) * g⁻¹ by group, hg _ (hM.normA h hhN b hb),
    hh b hb, RuSimCode.linApply_linComp]

omit hM in
theorem code_one : ∀ b ∈ gmsA L T, ν ((1 : G) * b * 1⁻¹) = linApply linId (ν b) := by
  intro b _
  rw [one_mul, inv_one, mul_one, RuSimCode.linApply_linId]

theorem code_pow {g : G} {r : Lin8} (hgN : g ∈ normalizer (R : Set G))
    (hg : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b)) (k : ℕ) :
    ∀ b ∈ gmsA L T, ν (g ^ k * b * (g ^ k)⁻¹) = linApply ((linComp r)^[k] linId) (ν b) := by
  induction k with
  | zero => simpa using code_one (G := G) (L := L) (T := T) (ν := ν)
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact hM.code_mul (pow_mem hgN k) hg ih

theorem act_of_code {g : G} {r : Lin8} (hgN : g ∈ normalizer (R : Set G))
    (hg : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b)) :
    ∀ x ∈ R, μ (g * x * g⁻¹) = maskApply (adMat r) (μ x) := by
  obtain ⟨r', -, hr'A, hr'R⟩ := hM.act g hgN
  rw [hM.code_unique hg hr'A]
  exact hr'R

theorem code_dElt {X U : G} (hXN : X ∈ normalizer (R : Set G)) (hUN : U ∈ normalizer (R : Set G))
    (hX : ∀ b ∈ gmsA L T, ν (X * b * X⁻¹) = linApply (dCode 1) (ν b))
    (hU : ∀ b ∈ gmsA L T, ν (U * b * U⁻¹) = linApply (dCode 2) (ν b)) (d : Fin 8) :
    ∀ b ∈ gmsA L T, ν (dElt X U d * b * (dElt X U d)⁻¹) = linApply (dCode d) (ν b) := by
  rw [dCode_eq d]
  refine hM.code_mul (pow_mem hXN _) (hM.code_pow hUN hU _) ?_
  rcases Nat.mod_two_eq_zero_or_one d.val with h0 | h1
  · simp only [h0, pow_zero, zero_ne_one, ↓reduceIte]
    exact code_one (G := G) (L := L) (T := T) (ν := ν)
  · simp only [h1, pow_one, ↓reduceIte]
    exact hX

omit hM in
theorem dElt_mem {X U : G} (hXN : X ∈ normalizer (R : Set G)) (hUN : U ∈ normalizer (R : Set G))
    (d : Fin 8) : dElt X U d ∈ normalizer (R : Set G) :=
  mul_mem (pow_mem hUN _) (pow_mem hXN _)

variable (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
  (hidx : R.relIndex (normalizer (R : Set G)) = 168)
include hNC hidx

omit hidx in
theorem mem_of_code_linId {g : G} (hgN : g ∈ normalizer (R : Set G))
    (hg : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply linId (ν b)) : g ∈ R :=
  hM.mem_of_code_eq_linId hNC hgN hg

theorem exists_xu [Finite G] :
    ∃ X U z : G, X ∈ normalizer (R : Set G) ∧ U ∈ normalizer (R : Set G) ∧
      (∀ b ∈ gmsA L T, ν (X * b * X⁻¹) = linApply (dCode 1) (ν b)) ∧
      (∀ b ∈ gmsA L T, ν (U * b * U⁻¹) = linApply (dCode 2) (ν b)) ∧
      X * X = 1 ∧ X * U = U * (U * (U * (z * X))) ∧ U * (U * (U * U)) = z ∧
      z ∈ gmsA L T ∧ (ν z = 0 ∨ ν z = 1) ∧ z * X = X * z ∧ z * U = U * z ∧ z * z = 1 := by
  obtain ⟨X₀, hX₀N, hX₀2, hX₀A⟩ := hM.exists_sq_eq_one_code hNC hidx dCode_one_mem
  obtain ⟨Y, hYN, hY2, hYA⟩ := hM.exists_sq_eq_one_code hNC hidx dCode_seven_mem
  have hX₀X₀ : X₀ * X₀ = 1 := by rw [← pow_two, hX₀2]
  have hYY : Y * Y = 1 := by rw [← pow_two, hY2]
  have hU₀N : X₀ * Y ∈ normalizer (R : Set G) := mul_mem hX₀N hYN
  have hU₀A : ∀ b ∈ gmsA L T, ν (X₀ * Y * b * (X₀ * Y)⁻¹) = linApply (dCode 2) (ν b) := by
    rw [dCode_two]
    exact hM.code_mul hYN hX₀A hYA
  have hX₀R := hM.act_of_code hX₀N hX₀A
  have hU₀R := hM.act_of_code hU₀N hU₀A
  set W := (X₀ * Y) ^ 4 with hW
  have hWN : W ∈ normalizer (R : Set G) := pow_mem hU₀N 4
  have hWR : W ∈ R := hM.mem_of_code_linId hNC hWN (by
    rw [← dCode_two_pow]
    exact hM.code_pow hU₀N hU₀A 4)
  have hinv : X₀ * (X₀ * Y) * X₀⁻¹ = (X₀ * Y)⁻¹ := by
    have h1 : X₀⁻¹ = X₀ := inv_eq_of_mul_eq_one_right hX₀X₀
    have h2 : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hYY
    rw [mul_inv_rev, h1, h2, ← mul_assoc, hX₀X₀, one_mul]
  have hXW : X₀ * W * X₀⁻¹ = W⁻¹ := by
    rw [hW, ← conj_pow, hinv, inv_pow]
  have hUW : (X₀ * Y) * W * (X₀ * Y)⁻¹ = W := by
    rw [hW, ← pow_succ', pow_succ, mul_inv_cancel_right]
  have hμW : μ W = 0 ∨ μ W = 2 := by
    refine RuSModel.fix_xu _ (hM.lt _ hWR) ?_ ?_
    · rw [← hX₀R W hWR, hXW, hM.μ_inv hWR]
    · rw [← hU₀R W hWR, hUW]
  obtain ⟨X, hXN, hXA, hXX, hXYA⟩ : ∃ X : G, X ∈ normalizer (R : Set G) ∧
      (∀ b ∈ gmsA L T, ν (X * b * X⁻¹) = linApply (dCode 1) (ν b)) ∧ X * X = 1 ∧
      μ ((X * Y) ^ 4) = 0 ∧ (X * Y) ^ 4 ∈ R := by
    rcases hμW with h0 | h2
    · exact ⟨X₀, hX₀N, hX₀A, hX₀X₀, h0, hWR⟩
    · obtain ⟨ℓ₀, hℓ₀, hμℓ₀⟩ := hM.surj 16 (by norm_num)
      refine ⟨ℓ₀ * X₀ * ℓ₀⁻¹, mul_mem (mul_mem (le_normalizer hℓ₀) hX₀N) (inv_mem
        (le_normalizer hℓ₀)), fun b hb => ?_, by
          rw [show ℓ₀ * X₀ * ℓ₀⁻¹ * (ℓ₀ * X₀ * ℓ₀⁻¹) = ℓ₀ * (X₀ * X₀) * ℓ₀⁻¹ by group, hX₀X₀]
          group, ?_⟩
      · have hc : ℓ₀⁻¹ * b * ℓ₀ = b := by
          have := hM.central _ (inv_mem hℓ₀) b hb
          rw [this]; group
        rw [show ℓ₀ * X₀ * ℓ₀⁻¹ * b * (ℓ₀ * X₀ * ℓ₀⁻¹)⁻¹ =
            ℓ₀ * (X₀ * (ℓ₀⁻¹ * b * ℓ₀) * X₀⁻¹) * ℓ₀⁻¹ by group, hc]
        have hb' := hM.normA X₀ hX₀N b hb
        rw [show ℓ₀ * (X₀ * b * X₀⁻¹) * ℓ₀⁻¹ = X₀ * b * X₀⁻¹ by
          rw [hM.central _ hℓ₀ _ hb']; group]
        exact hX₀A b hb
      ·
        set U₀ := X₀ * Y with hU₀
        set w := ℓ₀ * (X₀ * ℓ₀⁻¹ * X₀⁻¹) with hw
        have hX₀ℓ : X₀ * ℓ₀⁻¹ * X₀⁻¹ ∈ R := (mem_normalizer_iff.mp hX₀N _).mp (inv_mem hℓ₀)
        have hwR : w ∈ R := mul_mem hℓ₀ hX₀ℓ
        have hμw : μ w = 16 ^^^ maskApply (adMat (dCode 1)) 16 := by
          rw [hw, hM.mul _ hℓ₀ _ hX₀ℓ, hX₀R _ (inv_mem hℓ₀), hM.μ_inv hℓ₀, hμℓ₀]
        have hconj : ∀ k : ℕ, U₀ ^ k * w * (U₀ ^ k)⁻¹ ∈ R ∧
            μ (U₀ ^ k * w * (U₀ ^ k)⁻¹) = (maskApply (adMat (dCode 2)))^[k] (μ w) := by
          intro k
          induction k with
          | zero => simpa using hwR
          | succ k ih =>
            rw [Function.iterate_succ_apply', pow_succ',
              show U₀ * U₀ ^ k * w * (U₀ * U₀ ^ k)⁻¹ = U₀ * (U₀ ^ k * w * (U₀ ^ k)⁻¹) * U₀⁻¹ by
                group]
            exact ⟨(mem_normalizer_iff.mp hU₀N _).mp ih.1, by rw [hU₀R _ ih.1, ih.2]⟩
        have hXY : ℓ₀ * X₀ * ℓ₀⁻¹ * Y = w * U₀ := by rw [hw, hU₀]; group
        have hexp : (w * U₀) ^ 4 = w * (U₀ * w * U₀⁻¹) * (U₀ ^ 2 * w * (U₀ ^ 2)⁻¹) *
            (U₀ ^ 3 * w * (U₀ ^ 3)⁻¹) * W := by
          rw [hW]
          simp only [pow_succ, pow_zero, one_mul]
          group
        obtain ⟨h1R, h1⟩ := hconj 1
        obtain ⟨h2R, h2'⟩ := hconj 2
        obtain ⟨h3R, h3⟩ := hconj 3
        rw [pow_one] at h1R h1
        refine ⟨?_, ?_⟩
        · rw [hXY, hexp, hM.mul _ (mul_mem (mul_mem (mul_mem hwR h1R) h2R) h3R) _ hWR,
            hM.mul _ (mul_mem (mul_mem hwR h1R) h2R) _ h3R, hM.mul _ (mul_mem hwR h1R) _ h2R,
            hM.mul _ hwR _ h1R, h1, h2', h3, h2, hμw]
          have := RuSModel.norm_sixteen
          simp only at this
          simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
          rw [this]
          rfl
        · rw [hXY, hexp]
          exact mul_mem (mul_mem (mul_mem (mul_mem hwR h1R) h2R) h3R) hWR
  have hzA : (X * Y) ^ 4 ∈ gmsA L T := (hM.ker _ hXYA.2).mp hXYA.1
  set z := (X * Y) ^ 4 with hz
  have hzz : z * z = 1 := by
    have := (hM.sq_eq_one_iff (hM.le hzA)).mpr (by rw [(hM.ker _ (hM.le hzA)).mpr hzA]; rfl)
    rwa [pow_two] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hXinv : X⁻¹ = X := inv_eq_of_mul_eq_one_right hXX
  have hYinv : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hYY
  have hUN : X * Y ∈ normalizer (R : Set G) := mul_mem hXN hYN
  have hXz : X * z * X⁻¹ = z := by
    have h1 : X * (X * Y) * X⁻¹ = (X * Y)⁻¹ := by
      rw [mul_inv_rev, hXinv, hYinv, ← mul_assoc, hXX, one_mul]
    rw [hz, ← conj_pow, h1, inv_pow, ← hz, hzinv]
  have hYz : Y * z * Y⁻¹ = z := by
    have h1 : Y * (X * Y) * Y⁻¹ = (X * Y)⁻¹ := by
      rw [mul_inv_rev, hXinv, hYinv]
      simp only [mul_assoc, hYY, mul_one]
    rw [hz, ← conj_pow, h1, inv_pow, ← hz, hzinv]
  have hzX : z * X = X * z := by
    calc z * X = (X * z * X⁻¹) * X := by rw [hXz]
      _ = X * z := by group
  have hzY : z * Y = Y * z := by
    calc z * Y = (Y * z * Y⁻¹) * Y := by rw [hYz]
      _ = Y * z := by group
  have hνz : ν z = 0 ∨ ν z = 1 := by
    refine RuSModel.fix_code_xy _ ?_ ?_
    · rw [← hXA z hzA, hXz]
    · rw [← hYA z hzA, hYz]
  refine ⟨X, X * Y, z, hXN, hUN, hXA, ?_, hXX, ?_, ?_, hzA, hνz, hzX, ?_, hzz⟩
  · rw [dCode_two]
    exact hM.code_mul hYN hXA hYA
  ·
    have hU8 : (X * Y) ^ 8 = 1 := by
      rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, ← hz, pow_two, hzz]
    have h7 : (X * Y) ^ 7 = (X * Y)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hU8]
    calc X * (X * Y) = Y := by rw [← mul_assoc, hXX, one_mul]
      _ = (X * Y)⁻¹ * X := by rw [mul_inv_rev, hXinv, hYinv, mul_assoc, hXX, mul_one]
      _ = (X * Y) ^ 7 * X := by rw [h7]
      _ = X * Y * (X * Y * (X * Y * (z * X))) := by
        rw [hz]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · rw [hz]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · rw [mul_assoc, ← hzY, ← mul_assoc, hzX, mul_assoc]

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
