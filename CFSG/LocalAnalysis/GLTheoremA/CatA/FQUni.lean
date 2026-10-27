module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly CFSG.Open
open scoped Matrix

section SU

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem mem_LargeEvenSU_iff [CharP K 2] {g : ℕ} (A : GL (Fin d) K) :
    A ∈ LargeEvenSUGroup (Fin d) K (2 ^ g) ↔
      (A : Matrix (Fin d) (Fin d) K).det = 1 ∧
        ((A : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ g))ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1 := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let φ : K →+* K := iterateFrobenius K 2 g
  have hφ : ∀ x, φ x = x ^ 2 ^ g := fun x => rfl
  have h : LargeEvenSUGroup (Fin d) K (2 ^ g) = Subgroup.closure {A : GL (Fin d) K |
      (A : Matrix (Fin d) (Fin d) K).det = 1 ∧
        ((A : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ g))ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1} :=
    rfl
  rw [h, mem_closure_iff_of_mul_closed]
  · rfl
  · simp
  · rintro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩
    have hmap : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ 2 ^ g) = M.map φ := fun M => rfl
    rw [hmap] at ha2 hb2
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul, Matrix.det_mul, ha1, hb1, mul_one]
    · rw [hmap, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
      calc _ = ((b : Matrix (Fin d) (Fin d) K).map φ)ᵀ *
            (((a : Matrix (Fin d) (Fin d) K).map φ)ᵀ * (a : Matrix (Fin d) (Fin d) K)) *
            (b : Matrix (Fin d) (Fin d) K) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [ha2, Matrix.mul_one]; exact hb2

theorem pow_two_pow_mul_of_odd {k : Type} [Field k] [Finite k] {j' r : ℕ}
    (hk : Nat.card k = (2 ^ j') ^ 2) (hr : Odd r) (a : k) :
    a ^ 2 ^ (j' * r) = a ^ 2 ^ j' := by
  haveI := Fintype.ofFinite k
  have h1 : a ^ ((2 ^ j') ^ 2) = a := by
    have := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hk] at this
  obtain ⟨s, rfl⟩ := hr
  have h2 : ∀ s : ℕ, a ^ (((2 ^ j') ^ 2) ^ s) = a := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [pow_succ, pow_mul, ih, h1]
  have h3 : (2 : ℕ) ^ (j' * (2 * s + 1)) = 2 ^ j' * (((2 ^ j') ^ 2) ^ s) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [h3, pow_mul', h2]

theorem su_map_subtype_iff [CharP K 2] {j j' r : ℕ} (hjr : j = j' * r) (hr : Odd r)
    (σ : K ≃+* K) [CharP (fixF σ) 2] (hk : Nat.card (fixF σ) = (2 ^ j') ^ 2)
    (A : GL (Fin d) (fixF σ)) :
    Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ LargeEvenSUGroup (Fin d) K (2 ^ j) ↔
      A ∈ LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ j') := by
  rw [mem_LargeEvenSU_iff, mem_LargeEvenSU_iff]
  set f : fixF σ →+* K := (fixF σ).subtype with hf
  have hA : ((Matrix.GeneralLinearGroup.map f A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) (fixF σ)).map f := rfl
  have hdet : ((A : Matrix (Fin d) (Fin d) (fixF σ)).map f).det =
      f (A : Matrix (Fin d) (Fin d) (fixF σ)).det := by
    rw [RingHom.map_det]; rfl
  have hpow : ((A : Matrix (Fin d) (Fin d) (fixF σ)).map f).map (· ^ 2 ^ j) =
      ((A : Matrix (Fin d) (Fin d) (fixF σ)).map (· ^ 2 ^ j')).map f := by
    ext i k
    simp only [Matrix.map_apply]
    rw [← map_pow]
    congr 1
    rw [hjr]
    exact pow_two_pow_mul_of_odd hk hr _
  rw [hA, hdet, hpow, ← Matrix.transpose_map, ← Matrix.map_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨f.injective (by rw [h1, map_one]), ?_⟩
    have h2' : (((A : Matrix (Fin d) (Fin d) (fixF σ)).map (· ^ 2 ^ j'))ᵀ *
        (A : Matrix (Fin d) (Fin d) (fixF σ))).map f =
        (1 : Matrix (Fin d) (Fin d) (fixF σ)).map f := by
      rw [h2, Matrix.map_one _ (map_zero f) (map_one f)]
    exact Matrix.map_injective f.injective h2'
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1, map_one], ?_⟩
    rw [h2, Matrix.map_one _ (map_zero f) (map_one f)]

theorem twoPart_card_SU {L : Type} [Field L] [Finite L] {n g : ℕ} (hn : 3 ≤ n) (hg : 1 ≤ g)
    (hL : Nat.card L = (2 ^ g) ^ 2) :
    twoPart (Nat.card (LargeEvenSUGroup (Fin n) L (2 ^ g))) = 2 ^ (g * (n * (n - 1) / 2)) := by
  have hL' : Nat.card L = 2 ^ (2 * g) := by rw [hL, ← pow_mul, mul_comm]
  rw [twoPart_card_matrix_group (by omega) hL' (LargeEvenSUGroup (Fin n) L (2 ^ g))]
  exact twoPart_card_statedProj_statedSU hn hg hL

theorem stOrderBody_unitary [CharP K 2] (hd : 3 ≤ d) {j : ℕ} (hj : 1 ≤ j)
    (hK : Nat.card K = (2 ^ j) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))))) :
    StOrderBody p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))) := by
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  have hu : 0 < d * (d - 1) / 2 := by
    have : 2 ≤ d * (d - 1) := calc 2 = 2 * 1 := rfl
      _ ≤ d * (d - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos this (by norm_num)
  refine stOrderBody_of_matrix (m := 2 * j) (by omega) hK' (LargeEvenSUGroup (Fin d) K (2 ^ j))
    (fun σ h hh => su_map_mem σ h hh) (fun σ => Odd (orderOf σ)) ?_ hu two_pos ?_ ?_ hp ?_ I
  · intro σ hσ n
    exact Odd.of_dvd_nat hσ (orderOf_pow_dvd n)
  · rw [twoPart_card_SU hd hj hK, ← pow_mul]
    exact congrArg (2 ^ ·) (by ring)
  · intro σ hσ e he
    obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
    have hee : e = 2 * j / orderOf σ := Nat.pow_right_injective (le_refl 2) (he.symm.trans hcard)
    have hcop : (orderOf σ).Coprime 2 := (Nat.coprime_two_left.2 hσ).symm
    obtain ⟨j', hjj'⟩ := (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd : orderOf σ ∣ j)
    have hr0 : 0 < orderOf σ := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hee' : e = 2 * j' := by
      rw [hee, hjj', ← mul_assoc, mul_comm 2 (orderOf σ), mul_assoc, Nat.mul_div_cancel_left _ hr0]
    have hj' : 1 ≤ j' := by
      rcases Nat.eq_zero_or_pos j' with h0 | h0
      · rw [h0, mul_zero] at hjj'; omega
      · exact h0
    have hk : Nat.card (fixF σ) = (2 ^ j') ^ 2 := by
      rw [card_fixF.trans he, hee', pow_mul']
    haveI : CharP (fixF σ) 2 :=
      CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * j')
        (by rw [hk, ← pow_mul, mul_comm])
    rw [card_fixed_eq_of_iff σ _ (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ j'))
      (su_map_subtype_iff (j := j) (j' := j') (r := orderOf σ) (by rw [hjj', mul_comm]) hσ σ hk),
      twoPart_card_SU hd hj' hk, ← pow_mul, hee']
    congr 1
    ring
  · intro σ
    obtain ⟨hdvd, -⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
    have hr0 : orderOf σ ≠ 0 := (Nat.pos_of_dvd_of_pos hdvd (by omega)).ne'
    obtain ⟨a, c, hc, hac⟩ := Nat.exists_eq_two_pow_mul_odd hr0
    refine ⟨2 ^ a, fun h => hp2 ?_, ?_⟩
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    · rw [orderOf_pow' _ (by positivity), hac, Nat.gcd_eq_right (Dvd.intro c rfl),
        Nat.mul_div_cancel_left c (by positivity)]
      exact hc

end SU

end FQ

end CFSG.LocalAnalysis.GLTheoremA
