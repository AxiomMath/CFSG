module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UPair
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UReg
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5URegDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (gramSU commute_scalar)
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KCUnitaryRegular (conj_injective_primeFormP)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {m : ℕ} {F : Type} [Field F]

private theorem not_five_dvd_of_dvd (h5 : 5 ∣ 2 ^ m + 1) (h25 : ¬ 25 ∣ 2 ^ m + 1) : ¬ 5 ∣ m := by
  rintro ⟨k, rfl⟩
  rw [pow_mul'] at h5 h25
  apply h25
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ k = y := ⟨_, rfl⟩
  rw [hy] at h5 ⊢
  have key : ∀ r < 25, (r ^ 5 + 1) % 5 = 0 → (r ^ 5 + 1) % 25 = 0 := by decide +kernel
  have e25 : Nat.ModEq 25 ((y % 25) ^ 5 + 1) (y ^ 5 + 1) :=
    ((Nat.mod_modEq y 25).pow 5).add_right 1
  have e5 : Nat.ModEq 5 ((y % 25) ^ 5 + 1) (y ^ 5 + 1) := Nat.ModEq.of_dvd (by norm_num) e25
  refine Nat.dvd_of_mod_eq_zero ?_
  exact Eq.trans e25.symm
    (key _ (Nat.mod_lt _ (by norm_num)) (Eq.trans e5 (Nat.mod_eq_zero_of_dvd h5)))

private theorem mem_primeFormD_of_pow_eq_one (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1)
    (h25 : ¬ 25 ∣ 2 ^ m + 1)
    {α : MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))} {n : ℕ}
    (hα : α ^ 5 ^ n = 1) :
    α ∈ primeFormD hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
  have hn : 3 ≤ 5 := by norm_num
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  rw [← ker_primeFormFieldFactor hF isPrimeFormGram_idGram hn hne, MonoidHom.mem_ker]
  obtain ⟨-, -, -, -, hAut, -⟩ := finite_field_automorphism_fixed_field_cardinality hF.prime
    (by have := hF.one_le; omega) hF.card
  have h1 : orderOf (primeFormFieldFactor hF isPrimeFormGram_idGram hn hne α) ∣ 5 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have h2 := orderOf_dvd_natCard (primeFormFieldFactor hF isPrimeFormGram_idGram hn hne α)
  rw [hAut] at h2
  have hm : ¬ 5 ∣ 2 * m := fun h => not_five_dvd_of_dvd h5 h25 (by omega)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hm)) h1 h2)

private theorem exists_conj_eq_scalar_mul_of_commute (hF : UnitaryFieldData 2 m F)
    {N R : primeFormUnitary hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)}
    (hNR : primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) N *
        primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) R =
      primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) R *
        primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) N) :
    ∃ c : Fˣ, c ^ 5 = 1 ∧ (N : GL (Fin 5) F) * R * (N : GL (Fin 5) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) c * R := by
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  have hcomm : primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
      (N * R * N⁻¹ * R⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hNR, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 hcomm
  have hNRN : (N : GL (Fin 5) F) * R * (N : GL (Fin 5) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) c * R := mul_inv_eq_iff_eq_mul.1 hc
  refine ⟨c, ?_, hNRN⟩
  have h1 := congrArg GeneralLinearGroup.det hNRN
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, map_mul, GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at h1
  exact mul_eq_right.1 h1.symm

private theorem pow_conj_eq_scalar_pow_mul {G : Type*} [Group G] {w x z : G}
    (h : w * x * w⁻¹ = z * x) (hwz : Commute w z) (k : ℕ) :
    w ^ k * x * (w ^ k)⁻¹ = z ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc w ^ (k + 1) * x * (w ^ (k + 1))⁻¹ = w * (w ^ k * x * (w ^ k)⁻¹) * w⁻¹ := by
          rw [pow_succ']; group
      _ = w * z ^ k * w⁻¹ * (w * x * w⁻¹) := by rw [ih]; group
      _ = z ^ (k + 1) * x := by
        rw [(hwz.pow_right k).eq, mul_inv_cancel_right, h, ← mul_assoc, ← pow_succ]

private theorem exists_commute_mul_pow {t : Fin 5 → F} (ht : Function.Injective t)
    (ht5 : ∀ i, t i ^ 5 = 1) {c ν : Fˣ} (hc : IsPrimitiveRoot c 5) (hν : ν ^ 5 = 1)
    {Q s a y : GL (Fin 5) F}
    (hQ : ((Q⁻¹ * s * Q : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = diagonal t)
    (has : a * s = GeneralLinearGroup.scalar (Fin 5) c * s * a) (hys : y * s = s * y)
    (hya : y * a = GeneralLinearGroup.scalar (Fin 5) ν * a * y) :
    ∃ k : ℕ, ∀ w : GL (Fin 5) F, y * s ^ k * w = w * (y * s ^ k) := by
  have hc' : IsPrimitiveRoot (c : F) 5 := IsPrimitiveRoot.coe_units_iff.2 hc
  have hconj : ∀ {x x' : GL (Fin 5) F} {e : Fˣ},
      x * x' = GeneralLinearGroup.scalar (Fin 5) e * x' * x → (Q⁻¹ * x * Q) * (Q⁻¹ * x' * Q) =
        GeneralLinearGroup.scalar (Fin 5) e * (Q⁻¹ * x' * Q) * (Q⁻¹ * x * Q) := by
    intro x x' e h
    calc (Q⁻¹ * x * Q) * (Q⁻¹ * x' * Q) = Q⁻¹ * (x * x') * Q := by group
      _ = Q⁻¹ * GeneralLinearGroup.scalar (Fin 5) e * (x' * x) * Q := by rw [h]; group
      _ = _ := by rw [(commute_scalar e Q⁻¹).eq]; group
  have hys' : y * s = GeneralLinearGroup.scalar (Fin 5) 1 * s * y := by
    rw [map_one, one_mul, hys]
  have h1 := hconj has
  have h2 := hconj hys'
  have h3 := hconj hya
  obtain ⟨d, hd⟩ : ∃ d : GL (Fin 5) F, Q⁻¹ * s * Q = d := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ x : GL (Fin 5) F, Q⁻¹ * a * Q = x := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ x : GL (Fin 5) F, Q⁻¹ * y * Q = x := ⟨_, rfl⟩
  rw [hd] at hQ
  rw [hd, ha'] at h1
  rw [hd, hy', map_one, one_mul] at h2
  rw [ha', hy'] at h3
  have hm1 := congrArg (fun x : GL (Fin 5) F => (x : Matrix (Fin 5) (Fin 5) F)) h1
  have hm2 := congrArg (fun x : GL (Fin 5) F => (x : Matrix (Fin 5) (Fin 5) F)) h2
  have hm3 := congrArg (fun x : GL (Fin 5) F => (x : Matrix (Fin 5) (Fin 5) F)) h3
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hQ] at hm1 hm2 hm3
  obtain ⟨u, hu⟩ : ∃ u : Fin 5 → F, (y' : Matrix (Fin 5) (Fin 5) F) = diagonal u := by
    refine ⟨fun i => (y' : Matrix (Fin 5) (Fin 5) F) i i, Matrix.ext fun i j => ?_⟩
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · have e := congrFun (congrFun hm2 i) j
      rw [mul_diagonal, diagonal_mul] at e
      rw [diagonal_apply_ne _ hij]
      have h0 : (t i - t j) * (y' : Matrix (Fin 5) (Fin 5) F) i j = 0 := by linear_combination -e
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 fun h => hij (ht h))
  rw [hu] at hm3
  have hrow : ∀ i, ∃ k, (a' : Matrix (Fin 5) (Fin 5) F) i k ≠ 0 := fun i => by
    by_contra h0
    push Not at h0
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a'.isUnit).ne_zero (det_eq_zero_of_row_eq_zero i h0)
  choose g hg using hrow
  have hgt : ∀ i, t (g i) = (c : F) * t i := fun i => by
    have e := congrFun (congrFun hm1 i) (g i)
    simp only [mul_diagonal, diagonal_mul_diagonal, diagonal_mul] at e
    exact mul_left_cancel₀ (hg i) (by linear_combination e)
  have hgu : ∀ i, u i = (ν : F) * u (g i) := fun i => by
    have e := congrFun (congrFun hm3 i) (g i)
    simp only [mul_diagonal, diagonal_mul] at e
    exact mul_left_cancel₀ (hg i) (by linear_combination e)
  have hν' : (ν : F) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, hν, Units.val_one]
  obtain ⟨k, -, hk⟩ := hc'.eq_pow_of_pow_eq_one hν'
  have hgv : ∀ i, u (g i) * t (g i) ^ k = u i * t i ^ k := fun i => by
    rw [hgt i, hgu i, mul_pow, hk]
    ring
  have key : ∀ l : ℕ, ∀ i j, t j = (c : F) ^ l * t i → u i * t i ^ k = u j * t j ^ k := by
    intro l
    induction l with
    | zero =>
      intro i j h
      rw [pow_zero, one_mul] at h
      rw [ht h]
    | succ l ih =>
      intro i j h
      rw [← hgv i]
      exact ih (g i) j (by rw [h, hgt i, pow_succ, mul_assoc])
  have ht0 : t 0 ≠ 0 := fun h0 => by simpa [h0] using ht5 0
  have hv : ∀ i, u i * t i ^ k = u 0 * t 0 ^ k := fun i => by
    obtain ⟨l, -, hl⟩ := hc'.eq_pow_of_pow_eq_one (ξ := t i * (t 0)⁻¹)
      (by rw [mul_pow, inv_pow, ht5, ht5, inv_one, mul_one])
    exact (key l 0 i (by rw [hl, mul_assoc, inv_mul_cancel₀ ht0, mul_one])).symm
  obtain ⟨Y, hY⟩ : ∃ Y : GL (Fin 5) F, y' * d ^ k = Y := ⟨_, rfl⟩
  have hYm : (Y : Matrix (Fin 5) (Fin 5) F) = diagonal fun _ => u 0 * t 0 ^ k := by
    rw [← hY, Units.val_mul, Units.val_pow_eq_pow_val, hQ, hu, diagonal_pow,
      diagonal_mul_diagonal]
    exact congrArg diagonal (funext hv)
  have hYc : ∀ h : GL (Fin 5) F, Y * h = h * Y := fun h => Units.ext (by
    rw [Units.val_mul, Units.val_mul, hYm]
    ext i j
    rw [diagonal_mul, mul_diagonal]; exact mul_comm _ _)
  have hdk : d ^ k = Q⁻¹ * s ^ k * Q := by
    have e := conj_pow (a := Q⁻¹) (b := s) (i := k)
    rwa [inv_inv, hd] at e
  refine ⟨k, fun w => ?_⟩
  have e := hYc (Q⁻¹ * w * Q)
  rw [← hY, ← hy', hdk] at e
  calc y * s ^ k * w = Q * ((Q⁻¹ * y * Q) * (Q⁻¹ * s ^ k * Q) * (Q⁻¹ * w * Q)) * Q⁻¹ := by group
    _ = Q * ((Q⁻¹ * w * Q) * ((Q⁻¹ * y * Q) * (Q⁻¹ * s ^ k * Q))) * Q⁻¹ := by rw [e]
    _ = w * (y * s ^ k) := by group

theorem mem_of_commute_of_pow_eq_one (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1)
    (h25 : ¬ 25 ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)))}
    (hX : IsElemAbelian 5 X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer 5 (fixSubgroup α) = ⊥)
    (hcard : Nat.card X = 5 ^ 2)
    {α : MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))} {n : ℕ}
    (hα : α ^ 5 ^ n = 1) (hαX : ∀ β ∈ X, α * β = β * α) : α ∈ X := by
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  have hXD := SF.le_primeFormD_of_nl hF (by norm_num) (by norm_num) Nat.prime_five
    (by norm_num) h5 hX hnl
  obtain ⟨M, rfl⟩ := mem_primeFormD_of_pow_eq_one hF h5 h25 hα
  obtain ⟨r, hr1, hrX⟩ := exists_conj_mem_ne_one hF h5 hXD hcard
  obtain ⟨S, rfl⟩ := QuotientGroup.mk_surjective r
  have hS1 : MulAut.conj (S : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ≠
      1 := fun h1 => hr1 (conj_injective_primeFormP hF isPrimeFormGram_idGram (by norm_num) hne
    (by rw [h1, map_one]))
  have hρS := primeFormConjHom_eq_conj hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) S
  obtain ⟨A, hAX, c, hc5, hc1, hASA⟩ :=
    exists_conj_eq_scalar_mul_ne_one hF h5 hXD hX hnl hcard hrX hS1
  obtain ⟨Q, -, t, ht, ht5, hQ⟩ := exists_unitary_diag_injective hF h5 hX hnl
    (A := ⟨S, S.2.1⟩) S.2.2 (by rw [hρS]; exact hrX) (by rw [hρS]; exact hS1)
  have hQ' : ((Q⁻¹ * (S : GL (Fin 5) F) * Q : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      diagonal t := hQ
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : IsPrimitiveRoot c 5 := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hc5 hc1)
  obtain ⟨μ, hμ, hMS⟩ := exists_conj_eq_scalar_mul_of_commute hF (N := M) (R := ⟨S, S.2.1⟩)
    (by rw [hρS]; exact hαX _ hrX)
  obtain ⟨j, -, hj⟩ := hc.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 5 μ).2 hμ)
  have hMS' : (M : GL (Fin 5) F) * S * (M : GL (Fin 5) F)⁻¹ =
      (A : GL (Fin 5) F) ^ j * S * ((A : GL (Fin 5) F) ^ j)⁻¹ := by
    rw [pow_conj_eq_scalar_pow_mul hASA (commute_scalar c _) j,
      ← map_pow (GeneralLinearGroup.scalar (Fin 5)), hj]
    exact hMS
  have hNS : ((A : GL (Fin 5) F) ^ j)⁻¹ * M * S = S * (((A : GL (Fin 5) F) ^ j)⁻¹ * M) := by
    calc _ = ((A : GL (Fin 5) F) ^ j)⁻¹ * ((M : GL (Fin 5) F) * S * (M : GL (Fin 5) F)⁻¹) *
          M := by group
      _ = _ := by rw [hMS']; group
  obtain ⟨ν, hν, hNA⟩ := exists_conj_eq_scalar_mul_of_commute hF (N := (A ^ j)⁻¹ * M) (R := A)
    (by
      rw [map_mul, map_inv, map_pow]
      exact ((Commute.refl _).pow_left j).inv_left.mul_left (hαX _ hAX))
  obtain ⟨k, hk⟩ := exists_commute_mul_pow ht ht5 hc hν hQ' (mul_inv_eq_iff_eq_mul.1 hASA) hNS
    (mul_inv_eq_iff_eq_mul.1 hNA)
  have hN : primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
      ((A ^ j)⁻¹ * M * (⟨S, S.2.1⟩ : primeFormUnitary hF
        ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ^ k) = 1 := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk, MulAut.one_apply]
    congr 1
    refine Subtype.ext ?_
    change ((A : GL (Fin 5) F) ^ j)⁻¹ * M * (S : GL (Fin 5) F) ^ k * g *
      (((A : GL (Fin 5) F) ^ j)⁻¹ * M * (S : GL (Fin 5) F) ^ k)⁻¹ = g
    rw [hk, mul_inv_cancel_right]
  have hM : M = A ^ j * ((A ^ j)⁻¹ * M * (⟨S, S.2.1⟩ : primeFormUnitary hF
      ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ^ k) * ((⟨S, S.2.1⟩ :
        primeFormUnitary hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ^ k)⁻¹ := by
    group
  rw [hM, map_mul, map_mul, hN, mul_one, map_inv, map_pow, map_pow, hρS]
  exact mul_mem (pow_mem hAX j) (inv_mem (pow_mem hrX k))

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
