module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOPc
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O

variable {K : Type} [Field K] {n : ℕ}

theorem rot_cases (h2 : (2 : K) ≠ 0) {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : Yᵀ * diagonal ![1, 1] * Y = diagonal ![1, 1]) (hd : Y.det = 1) {μ : K}
    (hμ : μ ^ 2 = 1) (hY2 : Y * Y = μ • 1) :
    Y = 1 ∨ Y = -1 ∨ Y = jMat (-1) ∨ Y = -jMat (-1) := by
  rcases mul_self_eq_one_iff.1 (show μ * μ = 1 by rw [← sq]; exact hμ) with rfl | rfl
  · rw [one_smul] at hY2
    rcases eq_one_or_eq_neg_one_of_det_eq_one rfl h2 hd hY2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [neg_one_smul] at hY2
    rcases eq_jMat_of_mul_self_eq_neg_one h2 hY hd hY2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem refl_cases (h2 : (2 : K) ≠ 0) {Y s₀ : Matrix (Fin 2) (Fin 2) K}
    (hY : Yᵀ * diagonal ![1, 1] * Y = diagonal ![1, 1])
    (hs₀ : s₀ᵀ * diagonal ![1, 1] * s₀ = diagonal ![1, 1]) (hd : Y.det = -1)
    (hd₀ : s₀.det = -1) {μ : K} (hμ : μ ^ 2 = 1) (hc : Y * s₀ = μ • (s₀ * Y)) :
    Y = s₀ ∨ Y = -s₀ ∨ Y = jMat (-1) * s₀ ∨ Y = -(jMat (-1) * s₀) := by
  have hw : ∀ i, (![1, 1] : Fin 2 → K) i ≠ 0 := by
    intro i
    fin_cases i <;> simp
  have hY2 := mul_self_eq_one_of_det_eq_neg_one rfl hw hY hd
  have hs2 := mul_self_eq_one_of_det_eq_neg_one rfl hw hs₀ hd₀
  have hZ : (Y * s₀)ᵀ * diagonal ![1, 1] * (Y * s₀) = diagonal ![1, 1] := by
    rw [transpose_mul]
    calc s₀ᵀ * Yᵀ * diagonal ![1, 1] * (Y * s₀) = s₀ᵀ * (Yᵀ * diagonal ![1, 1] * Y) * s₀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hY, hs₀]
  have hZd : (Y * s₀).det = 1 := by rw [det_mul, hd, hd₀]; ring
  have hsY : s₀ * Y = μ • (Y * s₀) := by
    rw [hc, smul_smul, ← sq, hμ, one_smul]
  have hZ2 : Y * s₀ * (Y * s₀) = μ • 1 := by
    calc Y * s₀ * (Y * s₀) = Y * (s₀ * Y) * s₀ := by simp only [Matrix.mul_assoc]
      _ = μ • (Y * Y * (s₀ * s₀)) := by
          rw [hsY, Matrix.mul_smul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = μ • 1 := by rw [hY2, hs2, Matrix.one_mul]
  have hYe : Y = Y * s₀ * s₀ := by rw [Matrix.mul_assoc, hs2, Matrix.mul_one]
  rcases rot_cases h2 hZ hZd hμ hZ2 with h | h | h | h
  · left
    rw [hYe, h, Matrix.one_mul]
  · right; left
    rw [hYe, h, Matrix.neg_mul, Matrix.one_mul]
  · right; right; left
    rw [hYe, h]
  · right; right; right
    rw [hYe, h, Matrix.neg_mul]

variable [Finite K]

theorem famF_concl_pc (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)))
    {X : Type} [Group X] [Finite X] (π : matrixDerived (oQ R) →* X)
    (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 →
      ∃ μ : K, ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = μ • 1)
    (hz2 : π A * π A = 1) {P : Subgroup X} (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({π A} : Set X)), IsComponent L →
      Even (Nat.card L) → ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = π A) ∧
      ¬ ∀ q ∈ P, q * q = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hne1 : (-1 : K) ≠ 1 := fun e => h2 (by linear_combination -e)
  have hn0 : 0 < n := by omega
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat, diagonal_transpose]
  have hker' : ∀ s, π s = 1 → s ∈ center (matrixDerived (oQ R)) := fun s hs => by
    obtain ⟨μ, hμ⟩ := hker s hs
    exact mem_center_of_coe_eq_smul hμ
  set ℓ := Function.surjInv hπ with hℓdef
  have hℓ : ∀ g, π (ℓ g) = g := Function.surjInv_eq hπ
  have hinj : Function.Injective (fun s : matrixDerived (oQ R) =>
      ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) :=
    fun s t h => Subtype.ext (Units.ext h)
  have hw : ∀ i, (![1, 1] : Fin 2 → K) i ≠ 0 := by
    intro i
    fin_cases i <;> simp
  have hlift : ∀ g ∈ P, ∃ D₀ : Matrix (Fin 2) (Fin 2) K,
      ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ ∧
        D₀ᵀ * diagonal ![1, 1] * D₀ = diagonal ![1, 1] := fun g hg =>
    lift_eq_blkDiag_pc hK hp hKc hn hR hA π hπ hker' (fun L hL he k hk => hP L hL he k hk g hg)
      (hℓ g)
  have hsc : ∀ s, π s = 1 → ∃ μ : K, μ ^ 2 = 1 ∧
      ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = μ • 1 := by
    intro s hs
    obtain ⟨μ, hμ⟩ := hker s hs
    refine ⟨μ, ?_, hμ⟩
    have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
      ((mem_matrixIsometries_oQ h2 R hRs _).1 (matrixDerived_le_isometries _ s.2))
    change ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ *
      (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
        ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = R at hiso
    rw [hμ] at hiso
    exact sq_eq_one_of_smul_isometry (by omega) R hiso
  have hblk_smul : ∀ μ : K, (μ • 1 : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (μ • 1) := fun μ => by rw [blkDiag_smul, blkDiag_one']
  have hcard4 : ∀ T : Finset (Matrix (Fin 2) (Fin 2) K), T.card ≤ 4 →
      (∀ g ∈ P, ∃ s, π s = g ∧
        ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) ∈ T.image (blkDiag n)) →
          False := by
    intro T hT hmem
    have := card_le_of_forall_lift_mem π hinj (T.image (blkDiag n)) hmem
    have := Finset.card_image_le (s := T) (f := blkDiag n)
    omega
  have hAA : (((A * A : matrixDerived (oQ R)) : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) = -1 := by
    rw [Subgroup.coe_mul, Units.val_mul, hA, blkDiag_mul, jMat_mul_self, blkDiag_smul,
      blkDiag_one', neg_one_smul]
  have hrep : ∀ g, ∀ D₀ : Matrix (Fin 2) (Fin 2) K,
      ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ →
        (((A * A * ℓ g : matrixDerived (oQ R)) : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (-D₀) ∧ π (A * A * ℓ g) = g := by
    intro g D₀ hD₀
    refine ⟨?_, by rw [map_mul, map_mul, hz2, one_mul, hℓ]⟩
    rw [Subgroup.coe_mul _ (A * A), Units.val_mul, hAA, hD₀, neg_one_mul, ← neg_one_smul K D₀,
      blkDiag_smul, neg_one_smul]
  have hdet1 : ∀ {Y : Matrix (Fin 2) (Fin 2) K},
      Yᵀ * diagonal ![1, 1] * Y = diagonal ![1, 1] → Y.det = 1 ∨ Y.det = -1 := fun hY =>
    mul_self_eq_one_iff.1 (by rw [← sq]; exact det_sq_eq_one_of_isometry hw hY)
  refine ⟨fun ⟨⟨u, hu, v, hv, huv⟩, huniq⟩ => ?_, fun hall => ?_⟩
  ·
    obtain ⟨Du, hDu, hYu⟩ := hlift u hu
    obtain ⟨Dv, hDv, hYv⟩ := hlift v hv
    have hrefl : ∀ t ∈ P, ∀ D₀ : Matrix (Fin 2) (Fin 2) K,
        ((ℓ t : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ →
          D₀ᵀ * diagonal ![1, 1] * D₀ = diagonal ![1, 1] → D₀.det = -1 → False := by
      intro t ht D₀ hD₀ hY hd
      have hY2 := mul_self_eq_one_of_det_eq_neg_one rfl hw hY hd
      have htt : ℓ t * ℓ t = 1 := by
        refine Subtype.ext (Units.ext ?_)
        rw [Subgroup.coe_mul, Units.val_mul, hD₀, blkDiag_mul, hY2, blkDiag_one',
          OneMemClass.coe_one, Units.val_one]
      have ht2 : t * t = 1 := by rw [← hℓ t, ← map_mul, htt, map_one]
      have hrot : D₀.det = 1 := by
        rcases huniq t ht ht2 with rfl | rfl
        · obtain ⟨μ, hμ2, hμ⟩ := hsc _ (hℓ 1)
          rw [hμ, hblk_smul] at hD₀
          rw [← eq_of_blkDiag_eq hn0 hD₀, det_smul, det_one, Fintype.card_fin, mul_one, hμ2]
        · have h1 : π (ℓ (π A) * A⁻¹) = 1 := by rw [map_mul, map_inv, hℓ, mul_inv_cancel]
          obtain ⟨μ, hμ2, hμ⟩ := hsc _ h1
          have e2 : ℓ (π A) = (ℓ (π A) * A⁻¹) * A := by group
          have e : ((ℓ (π A) : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
              blkDiag n (μ • jMat (-1)) := by
            rw [e2, Subgroup.coe_mul _ (ℓ (π A) * A⁻¹), Units.val_mul, hμ, hA, Matrix.smul_mul,
              Matrix.one_mul, blkDiag_smul]
          rw [e] at hD₀
          rw [← eq_of_blkDiag_eq hn0 hD₀, det_smul, Fintype.card_fin, det_jMat_neg_one,
            mul_one, hμ2]
      rw [hd] at hrot
      exact hne1 hrot
    have hcomm : Du * Dv ≠ Dv * Du := by
      intro h
      apply huv
      rw [← hℓ u, ← hℓ v, ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext (Units.ext ?_)
      rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hDu, hDv,
        blkDiag_mul, blkDiag_mul, h]
    rcases hdet1 hYu with hdu | hdu
    · rcases hdet1 hYv with hdv | hdv
      · exact hcomm (commute_of_det_eq_one rfl hw hYu hYv hdu hdv)
      · exact hrefl v hv Dv hDv hYv hdv
    · exact hrefl u hu Du hDu hYu hdu
  ·
    have hsq : ∀ g ∈ P, ∀ D₀ : Matrix (Fin 2) (Fin 2) K,
        ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ →
          ∃ μ : K, μ ^ 2 = 1 ∧ D₀ * D₀ = μ • 1 := by
      intro g hg D₀ hD₀
      obtain ⟨μ, hμ2, hμ⟩ := hsc _ (by rw [map_mul, hℓ, hall g hg] : π (ℓ g * ℓ g) = 1)
      refine ⟨μ, hμ2, eq_of_blkDiag_eq hn0 ?_⟩
      rw [← blkDiag_mul, ← hD₀, ← hblk_smul, ← hμ, Subgroup.coe_mul, Units.val_mul]
    have hcm : ∀ g ∈ P, ∀ h ∈ P, ∀ D₀ E₀ : Matrix (Fin 2) (Fin 2) K,
        ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ →
          ((ℓ h : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n E₀ →
            ∃ μ : K, μ ^ 2 = 1 ∧ D₀ * E₀ = μ • (E₀ * D₀) := by
      intro g hg h hh D₀ E₀ hD₀ hE₀
      have hgh : g * h = h * g := by
        have hg1 : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hall g hg)
        have hh1 : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hall h hh)
        have hgh1 : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right (hall _ (mul_mem hg hh))
        rw [← hgh1, _root_.mul_inv_rev, hg1, hh1]
      have h1 : π (ℓ g * ℓ h * (ℓ h * ℓ g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hℓ, hℓ, hgh, mul_inv_cancel]
      obtain ⟨μ, hμ2, hμ⟩ := hsc _ h1
      have e2 : ℓ g * ℓ h = (ℓ g * ℓ h * (ℓ h * ℓ g)⁻¹) * (ℓ h * ℓ g) := by group
      have e3 : ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((ℓ h : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
            μ • (((ℓ h : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
              ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, e2,
          Subgroup.coe_mul _ (ℓ g * ℓ h * (ℓ h * ℓ g)⁻¹), Units.val_mul, hμ, Matrix.smul_mul,
          Matrix.one_mul, Subgroup.coe_mul, Units.val_mul]
      rw [hD₀, hE₀, blkDiag_mul, blkDiag_mul, ← blkDiag_smul] at e3
      exact ⟨μ, hμ2, eq_of_blkDiag_eq hn0 e3⟩
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix (Fin 2) (Fin 2) K, ∀ g ∈ P, ∀ D₀ : Matrix (Fin 2) (Fin 2) K,
        ((ℓ g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ →
          D₀ᵀ * diagonal ![1, 1] * D₀ = diagonal ![1, 1] → D₀.det = -1 →
            D₀ = s₀ ∨ D₀ = -s₀ ∨ D₀ = jMat (-1) * s₀ ∨ D₀ = -(jMat (-1) * s₀) := by
      by_cases hB : ∃ g₀ ∈ P, ∃ s₀ : Matrix (Fin 2) (Fin 2) K,
          ((ℓ g₀ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n s₀ ∧
            s₀ᵀ * diagonal ![1, 1] * s₀ = diagonal ![1, 1] ∧ s₀.det = -1
      · obtain ⟨g₀, hg₀, s₀, hD₀, hiso₀, hd₀⟩ := hB
        refine ⟨s₀, fun g hg D₀ hD hY hd => ?_⟩
        obtain ⟨μ, hμ2, hc⟩ := hcm g hg g₀ hg₀ D₀ s₀ hD hD₀
        exact refl_cases h2 hY hiso₀ hd hd₀ hμ2 hc
      · exact ⟨1, fun g hg D₀ hD hY hd => absurd ⟨g, hg, D₀, hD, hY, hd⟩ hB⟩
    apply hcard4 {1, jMat (-1), s₀, jMat (-1) * s₀} (card_insert_four_le _ _ _ _)
    intro g hg
    obtain ⟨D₀, hD₀, hY⟩ := hlift g hg
    have key : ∃ Y ∈ ({1, jMat (-1), s₀, jMat (-1) * s₀} : Finset (Matrix (Fin 2) (Fin 2) K)),
        D₀ = Y ∨ D₀ = -Y := by
      rcases hdet1 hY with hd | hd
      · obtain ⟨μ, hμ2, hD2⟩ := hsq g hg D₀ hD₀
        rcases rot_cases h2 hY hd hμ2 hD2 with h | h | h | h
        · exact ⟨1, by simp, Or.inl h⟩
        · exact ⟨1, by simp, Or.inr h⟩
        · exact ⟨jMat (-1), by simp, Or.inl h⟩
        · exact ⟨jMat (-1), by simp, Or.inr h⟩
      · rcases hs₀ g hg D₀ hD₀ hY hd with h | h | h | h
        · exact ⟨s₀, by simp, Or.inl h⟩
        · exact ⟨s₀, by simp, Or.inr h⟩
        · exact ⟨jMat (-1) * s₀, by simp, Or.inl h⟩
        · exact ⟨jMat (-1) * s₀, by simp, Or.inr h⟩
    obtain ⟨Y, hYT, hY'⟩ := key
    rcases hY' with h | h
    · exact ⟨ℓ g, hℓ g, Finset.mem_image.2 ⟨Y, hYT, by rw [hD₀, h]⟩⟩
    · obtain ⟨hrD, hrπ⟩ := hrep g D₀ hD₀
      exact ⟨A * A * ℓ g, hrπ, Finset.mem_image.2 ⟨Y, hYT, by rw [hrD, h, neg_neg]⟩⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
