module

public import CFSG.LargeExtraspecial.AS35WL5U5
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLa

public section

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace AS35W

variable {K : Type} [Field K]

theorem sq_dvd_card_centralizer_of_family {g : SpecialLinearGroup (Fin 4) K}
    {Y : Matrix (Fin 4) (Fin 4) K} {t : K} (ht : t ≠ 0) (P : GL (Fin 4) K)
    (hP : (t • (g : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * Y)
    (U : K × K → Matrix (Fin 4) (Fin 4) K) (h0 : U 0 = 1)
    (hadd : ∀ a b, U (a + b) = U a * U b) (hdet : ∀ a, (U a).det = 1)
    (hcomm : ∀ a, U a * Y = Y * U a) (hinj : ∀ a (r : K), U a = r • 1 → a = 0) :
    Nat.card K ^ 2 ∣ Nat.card (centralizer ({proj 4 K g} : Set (projectiveSL 4 K))) := by
  set Pm : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K)
  set Pi : Matrix (Fin 4) (Fin 4) K := ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hPPi : Pm * Pi = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdetV : ∀ a, (Pm * U a * Pi).det = 1 := by
    intro a
    rw [det_mul, det_mul, hdet, mul_one, ← det_mul, hPPi, det_one]
  have h1 : (g : Matrix (Fin 4) (Fin 4) K) * Pm = t⁻¹ • (Pm * Y) := by
    rw [← hP, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hg : (g : Matrix (Fin 4) (Fin 4) K) = t⁻¹ • (Pm * Y * Pi) := by
    calc (g : Matrix (Fin 4) (Fin 4) K) = (g : Matrix (Fin 4) (Fin 4) K) * (Pm * Pi) := by
          rw [hPPi, Matrix.mul_one]
      _ = (g : Matrix (Fin 4) (Fin 4) K) * Pm * Pi := by rw [Matrix.mul_assoc]
      _ = t⁻¹ • (Pm * Y * Pi) := by rw [h1, Matrix.smul_mul]
  have hVg : ∀ a, Pm * U a * Pi * (g : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) * (Pm * U a * Pi) := by
    intro a
    rw [hg, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc Pm * U a * Pi * (Pm * Y * Pi) = Pm * U a * (Pi * Pm) * Y * Pi := by
          simp only [Matrix.mul_assoc]
      _ = Pm * (U a * Y) * Pi := by rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Pm * (Y * U a) * Pi := by rw [hcomm]
      _ = Pm * Y * (Pi * Pm) * U a * Pi := by
          rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Pm * Y * Pi * (Pm * U a * Pi) := by simp only [Matrix.mul_assoc]
  let φ : Multiplicative (K × K) →* SpecialLinearGroup (Fin 4) K :=
    { toFun := fun a => ⟨Pm * U (Multiplicative.toAdd a) * Pi, hdetV _⟩
      map_one' := by
        apply Subtype.ext
        change Pm * U 0 * Pi = 1
        rw [h0, Matrix.mul_one, hPPi]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change Pm * U (Multiplicative.toAdd a + Multiplicative.toAdd b) * Pi =
          Pm * U (Multiplicative.toAdd a) * Pi * (Pm * U (Multiplicative.toAdd b) * Pi)
        rw [hadd]
        calc Pm * (U (Multiplicative.toAdd a) * U (Multiplicative.toAdd b)) * Pi =
            Pm * U (Multiplicative.toAdd a) * (Pi * Pm) * U (Multiplicative.toAdd b) * Pi := by
              rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  set ψ := (proj 4 K).comp φ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 ha)
    change Pm * U (Multiplicative.toAdd a) * Pi = scalar (Fin 4) (c : K) at hc
    have hU : U (Multiplicative.toAdd a) = (c : K) • 1 := by
      calc U (Multiplicative.toAdd a) = Pi * (Pm * U (Multiplicative.toAdd a) * Pi) * Pm := by
            simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
            rw [Matrix.mul_assoc, hPiP, Matrix.mul_one]
        _ = (c : K) • 1 := by
            rw [hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, hPiP]
    exact hinj _ _ hU
  have hle : ψ.range ≤ centralizer ({proj 4 K g} : Set (projectiveSL 4 K)) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change proj 4 K (φ a) * proj 4 K g = proj 4 K g * proj 4 K (φ a)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hVg _)
  have hcard : Nat.card ψ.range = Nat.card K ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    change Nat.card (K × K) = _
    rw [Nat.card_prod, sq]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

@[expose] def uX1 (a : K × K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a.1, 0, 0; 0, 1, 0, 0; 0, 0, 1, a.2; 0, 0, 0, 1]

@[expose] def uD1 (a : K × K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a.1, a.2, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def uN (c : K) (a : K × K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, a.1, c * a.2; 0, 1, a.2, a.1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem uX1_zero : uX1 (0 : K × K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uX1]

theorem uD1_zero : uD1 (0 : K × K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uD1]

theorem uN_zero (c : K) : uN c (0 : K × K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uN]

theorem uX1_add (a b : K × K) : uX1 (a + b) = uX1 a * uX1 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uX1, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uD1_add (a b : K × K) : uD1 (a + b) = uD1 a * uD1 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uD1, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uN_add (c : K) (a b : K × K) : uN c (a + b) = uN c a * uN c b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uN, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uX1_det (a : K × K) : (uX1 a).det = 1 := by
  rw [uX1, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem uD1_det (a : K × K) : (uD1 a).det = 1 := by
  rw [uD1, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem uN_det (c : K) (a : K × K) : (uN c a).det = 1 := by
  rw [uN, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

open CFSG.ComponentClassification.CatFactsL4U4 in
theorem uX1_comm (a : K × K) : uX1 a * HBlocks.X1 1 = HBlocks.X1 1 * uX1 a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uX1, HBlocks.X1, Matrix.mul_apply, Fin.sum_univ_four]

open CFSG.ComponentClassification.CatFactsL4U4 in
theorem uD1_comm (a : K × K) : uD1 a * InvClassL.dOne = InvClassL.dOne * uD1 a := by
  ext i j
  rw [InvClassL.dOne, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [uD1]

open CFSG.ComponentClassification.CatFactsL4U4 in
theorem uN_comm (c : K) (a : K × K) : uN c a * InvClassL.stdN c = InvClassL.stdN c * uN c a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uN, InvClassL.stdN, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uX1_inj (a : K × K) (r : K) (h : uX1 a = r • 1) : a = 0 := by
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 2) 3
  simp [uX1] at h1 h2
  exact Prod.ext h1 h2

theorem uD1_inj (a : K × K) (r : K) (h : uD1 a = r • 1) : a = 0 := by
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 0) 2
  simp [uD1] at h1 h2
  exact Prod.ext h1 h2

theorem uN_inj (c : K) (a : K × K) (r : K) (h : uN c a = r • 1) : a = 0 := by
  have h1 := congrFun (congrFun h 1) 3
  have h2 := congrFun (congrFun h 1) 2
  simp [uN] at h1 h2
  exact Prod.ext h1 h2

open CFSG.ComponentClassification.CatFactsL4U4 in
theorem sq_dvd_card_centralizer_L4 [Finite K] (hodd : Odd (Nat.card K)) {z : projectiveSL 4 K}
    (hz : orderOf z = 2) :
    Nat.card K ^ 2 ∣ Nat.card (centralizer ({z} : Set (projectiveSL 4 K))) := by
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨g, rfl⟩ := proj_surjective 4 K z
  have hg2 : proj 4 K (g * g) = 1 := by
    rw [map_mul, ← sq, ← hz, pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg2)
  have hX : (g : Matrix (Fin 4) (Fin 4) K) * g = (c : K) • 1 := by
    have hc' : (g : Matrix (Fin 4) (Fin 4) K) * g = scalar (Fin 4) (c : K) := hc
    rw [hc', scalar_apply, smul_one_eq_diagonal]
  have hns : ∀ a : K, (g : Matrix (Fin 4) (Fin 4) K) ≠ a • 1 := by
    intro a ha
    have hdet : a ^ 4 = 1 := by
      have h1 := g.2
      rw [ha, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hdet
    have h1 : proj 4 K g = 1 := proj_eq_one_iff.2 ⟨Units.mk0 a ha0,
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]), by
        rw [ha, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]⟩
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  rcases InvClassL.classify_inv hchar hX c.ne_zero hns with
    ⟨l, hl0, -, -, P, hP⟩ | ⟨l, hl0, -, -, P, s, hs, hP⟩ | ⟨-, P, hP⟩
  · exact sq_dvd_card_centralizer_of_family (inv_ne_zero hl0) P hP uX1 uX1_zero uX1_add uX1_det
      uX1_comm uX1_inj
  · have hs0 : s * l⁻¹ ≠ 0 :=
      mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) (inv_ne_zero hl0)
    exact sq_dvd_card_centralizer_of_family hs0 P hP uD1 uD1_zero uD1_add uD1_det uD1_comm
      uD1_inj
  · exact sq_dvd_card_centralizer_of_family one_ne_zero P (by rw [one_smul]; exact hP)
      (uN (c : K)) (uN_zero _) (uN_add _) (uN_det _) (uN_comm _) (uN_inj _)

@[expose] def L43W2Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 → W2Good (projectiveSL 4 K)

theorem l4W2Input_of (h3 : L43W2Input) : L4W2Input := by
  intro X _ _ p f hp hp2 hf _ h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  by_cases hq3 : p ^ f = 3
  · exact W2Good.of_mulEquiv e (h3 K (hK.trans hq3))
  intro z hz
  exfalso
  have hz' := hz.map e
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hdvd := (sq_dvd_card_centralizer_L4 hodd hz'.orderOf_eq).trans hz'.card_dvd
  rw [hK] at hdvd
  exact hq3 (eq_three_of_sq_dvd hp hp2 hf hdvd)

end AS35W

end CFSG.LargeExtraspecial
