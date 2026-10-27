module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALin

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def KD292LangConjInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 3 ≤ n →
    ∀ T : Subgroup (MulAut (projectiveSL n K)), IsPGroup 2 T →
      (∀ t ∈ T, (t ∈ linearAutGroup n K ∨ ∃ A : GL (Fin n) K, t = conjAut n K A * dualAut n K) →
        t = 1) →
      ∃ d ∈ linearAutGroup n K,
        ∀ t ∈ T, ∃ (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ d * t * d⁻¹ = fieldAut n K σ * dualAut n K ^ ε

@[expose] def KD292StdSylow : Prop :=
  ∀ (p : ℕ) (K : Type) [Field K] [Finite K], p.Prime → 5 ≤ p →
    ∀ y : GL (Fin p) K, (∀ b : K, b ^ p ≠ (y : Matrix (Fin p) (Fin p) K).det) →
    ∀ S : Subgroup (MulAut (projectiveSL p K)), IsPGroup 2 S →
      (∀ s ∈ S, ∃ (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ s = fieldAut p K σ * dualAut p K ^ ε) →
      (∀ s ∈ S, s * conjAut p K y = conjAut p K y * s) →
      ∃ R : Subgroup (MulAut (projectiveSL p K)), R ≤ linearAutGroup p K ∧ IsPGroup p R ∧
        ¬ p ∣ R.relIndex (linearAutGroup p K) ∧ ∀ s ∈ S, ∀ r ∈ R, s * r = r * s


namespace I292CaseA

variable {K : Type} [Field K] {n : ℕ}

theorem exists_pow_eq_of_sq_mul_pow {d c : K} (hodd : Odd n) (h : d ^ 2 * c ^ n = 1) :
    ∃ b : K, b ^ n = d := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨d * c ^ m, ?_⟩
  rw [mul_pow, ← pow_mul, hm]
  have h2 : d ^ (2 * m + 1) = d * (d ^ 2) ^ m := by rw [← pow_mul, pow_succ, mul_comm]
  have h3 : c ^ (m * (2 * m + 1)) = (c ^ n) ^ m := by rw [← pow_mul, hm, mul_comm]
  rw [h2, h3]
  have h4 : (d ^ 2) ^ m * (c ^ n) ^ m = 1 := by rw [← mul_pow, h, one_pow]
  calc d * (d ^ 2) ^ m * (c ^ n) ^ m = d * ((d ^ 2) ^ m * (c ^ n) ^ m) := by ring
    _ = d := by rw [h4, mul_one]

theorem det_inverseTranspose' (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem not_commute_dual [Finite K] (hn : 3 ≤ n) (hodd : Odd n) (y : GL (Fin n) K)
    (hdet : ∀ b : K, b ^ n ≠ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det)
    (A : GL (Fin n) K) :
    ¬ (conjAut n K A * dualAut n K) * conjAut n K y =
      conjAut n K y * (conjAut n K A * dualAut n K) := by
  intro h
  have h1 : conjAut n K A * dualAut n K * conjAut n K y =
      conjAut n K (A * GeneralLinearGroup.inverseTranspose y) * dualAut n K := by
    rw [mul_assoc, dualAut_mul_conjAut, ← mul_assoc, ← map_mul]
  have h2 : conjAut n K y * (conjAut n K A * dualAut n K) =
      conjAut n K (y * A) * dualAut n K := by
    rw [← mul_assoc, ← map_mul]
  rw [h1, h2] at h
  have h3 : conjAut n K (A * GeneralLinearGroup.inverseTranspose y) = conjAut n K (y * A) :=
    mul_right_cancel h
  have h4 : conjAut n K ((y * A)⁻¹ * (A * GeneralLinearGroup.inverseTranspose y)) *
      fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h3, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h4
  have h5 := congrArg GeneralLinearGroup.det hc
  rw [GeneralLinearGroup.det_scalar, map_mul, map_inv, map_mul, map_mul,
    det_inverseTranspose', Fintype.card_fin] at h5
  have h6 : (GeneralLinearGroup.det y) ^ 2 * c ^ n = 1 := by
    rw [h5]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_one]
    field_simp
    exact div_self (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
  obtain ⟨b, hb⟩ := exists_pow_eq_of_sq_mul_pow (d := ((GeneralLinearGroup.det y : Kˣ) : K))
    (c := (c : K)) hodd (by simpa using congrArg Units.val h6)
  exact hdet b (by rw [hb, GeneralLinearGroup.val_det_apply])

end I292CaseA


theorem kd292LinLangInput_of_conj_std (h1 : KD292LangConjInput) (h2 : KD292StdSylow) :
    KD292LinLangInput := by
  intro p K _ _ hp hp5 y hdet T hT2 hTD hTc
  have hn3 : 3 ≤ p := by omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hT' : ∀ t ∈ T, (t ∈ linearAutGroup p K ∨
      ∃ A : GL (Fin p) K, t = conjAut p K A * dualAut p K) → t = 1 := by
    intro t ht h
    rcases h with hD | ⟨A, hA⟩
    · have : t ∈ T ⊓ linearAutGroup p K := Subgroup.mem_inf.2 ⟨ht, hD⟩
      rw [hTD] at this
      exact this
    · exfalso
      refine I292CaseA.not_commute_dual hn3 hodd y hdet A ?_
      rw [← hA]
      exact hTc t ht
  obtain ⟨d, hdD, hd⟩ := h1 K p hn3 T hT2 hT'
  obtain ⟨B, rfl⟩ : ∃ B : GL (Fin p) K, conjAut p K B = d := (mem_linearAutGroup_iff).1 hdD
  set c : MulAut (projectiveSL p K) := conjAut p K B with hc
  set y' : GL (Fin p) K := B * y * B⁻¹ with hy'
  have hdet' : ∀ b : K, b ^ p ≠ ((y' : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).det := by
    intro b hb
    apply hdet b
    rw [hb, hy']
    have := I292CaseA.det_conj_eq y B⁻¹
    rw [inv_inv] at this
    exact this
  set S : Subgroup (MulAut (projectiveSL p K)) := T.map (MulAut.conj c).toMonoidHom with hS
  have hS2 : IsPGroup 2 S := hT2.map _
  have hSle : ∀ s ∈ S, ∃ (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      s = fieldAut p K σ * dualAut p K ^ ε := by
    rintro _ ⟨t, ht, rfl⟩
    exact hd t ht
  have hy'c : conjAut p K y' = c * conjAut p K y * c⁻¹ := by
    rw [hy', map_mul, map_mul, map_inv]
  have hSc : ∀ s ∈ S, s * conjAut p K y' = conjAut p K y' * s := by
    rintro _ ⟨t, ht, rfl⟩
    change c * t * c⁻¹ * conjAut p K y' = conjAut p K y' * (c * t * c⁻¹)
    rw [hy'c]
    calc c * t * c⁻¹ * (c * conjAut p K y * c⁻¹) = c * (t * conjAut p K y) * c⁻¹ := by group
      _ = c * (conjAut p K y * t) * c⁻¹ := by rw [hTc t ht]
      _ = c * conjAut p K y * c⁻¹ * (c * t * c⁻¹) := by group
  obtain ⟨R, hRD, hRp, hRidx, hRc⟩ := h2 p K hp hp5 y' hdet' S hS2 hSle hSc
  have hcD : c ∈ linearAutGroup p K := hdD
  have hconjD : ∀ u ∈ linearAutGroup p K, c⁻¹ * u * c ∈ linearAutGroup p K := fun u hu =>
    mul_mem (mul_mem (inv_mem hcD) hu) hcD
  have hmapD : (linearAutGroup p K).map (MulAut.conj c⁻¹).toMonoidHom = linearAutGroup p K := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply] using hconjD u hu
    · intro hx
      refine ⟨c * x * c⁻¹, mul_mem (mul_mem hcD hx) (inv_mem hcD), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  refine ⟨R.map (MulAut.conj c⁻¹).toMonoidHom, ?_, hRp.map _, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    simpa [MulAut.conj_apply] using hconjD r (hRD hr)
  · have hinj : Function.Injective (MulAut.conj c⁻¹).toMonoidHom := (MulAut.conj c⁻¹).injective
    have := Subgroup.relIndex_map_map_of_injective R (linearAutGroup p K) hinj
    rw [hmapD] at this
    rw [this]
    exact hRidx
  · rintro t ht _ ⟨r, hr, rfl⟩
    have h3 := hRc (c * t * c⁻¹) ⟨t, ht, rfl⟩ r hr
    change t * (c⁻¹ * r * c⁻¹⁻¹) = c⁻¹ * r * c⁻¹⁻¹ * t
    calc t * (c⁻¹ * r * c⁻¹⁻¹) = c⁻¹ * ((c * t * c⁻¹) * r) * c⁻¹⁻¹ := by group
      _ = c⁻¹ * (r * (c * t * c⁻¹)) * c⁻¹⁻¹ := by rw [h3]
      _ = c⁻¹ * r * c⁻¹⁻¹ * t := by group

theorem kd292CaseALin_of_conj_std (h1 : KD292LangConjInput) (h2 : KD292StdSylow) : KD292CaseALin :=
  kd292CaseALin_of_input (kd292LinLangInput_of_conj_std h1 h2)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
