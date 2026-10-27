module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.PartOne.OutStructure (ringAut_comm)

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.LinkPSUAux

section Diag

variable {p f : ℕ} {K : Type} [Field K]

theorem det_scalar_eq {d : ℕ} (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) c) = c ^ d := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem det_glAut {d : ℕ} (ψ : K ≃+* K) (A : GL (Fin d) K) :
    Matrix.GeneralLinearGroup.det (glAut ψ A) =
      Units.map (ψ : K →* K) (Matrix.GeneralLinearGroup.det A) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_glAut, Units.coe_map,
    Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det ((ψ : K →+* K).mapMatrix (A : Matrix (Fin d) (Fin d) K)) = _
  rw [← RingHom.map_det]
  rfl

theorem exists_unitary_exponent (h : UnitaryFieldData p f K) {d : ℕ} (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ p ^ f = 2)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (τa τy : MulAut (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)))
    (hrel : τa * τy * τa⁻¹ = τy⁻¹)
    (hyr : τy ^ r ∈ inner (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)))
    (hy1 : τy ∉ inner (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))) :
    ∃ (A : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) (ψ : K ≃+* K)
      (u : ℕ), τa = primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_one ψ ∧
        (∀ x : K, ψ x = x ^ u) ∧ r ∣ u + 1 := by
  classical
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin d) K) := isPrimeFormGram_one
  obtain ⟨-, hΨsurj, hker1, -, -, -, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hd hq
  set Q := primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hQ
  set U := primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hU
  set Θ := primeFormFieldFactor h hC hd hq with hΘ
  have hInnD : inner Q ≤ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    fun α hα => by
      obtain ⟨s, rfl⟩ := (hinn α).1 hα
      exact ⟨_, rfl⟩
  have hΘy2 : Θ τy ^ 2 = 1 := by
    have h1 : Θ τa * Θ τy * (Θ τa)⁻¹ = (Θ τy)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hrel, map_inv]
    have h2 : Θ τa * Θ τy * (Θ τa)⁻¹ = Θ τy := by
      rw [ringAut_comm K (Θ τa) (Θ τy), mul_inv_cancel_right]
    rw [h2] at h1
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 h1
  have hΘyr : Θ τy ^ r = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (hFker ▸ hInnD hyr)
  have hΘy : Θ τy = 1 := by
    have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)
    have h1 : orderOf (Θ τy) ∣ Nat.gcd 2 r :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hΘy2) (orderOf_dvd_of_pow_eq_one hΘyr)
    rw [hcop] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  obtain ⟨Ay, hAy⟩ : τy ∈ (primeFormConjHom h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).range := by
    have : τy ∈ Θ.ker := MonoidHom.mem_ker.2 hΘy
    rw [hFker] at this
    exact this
  obtain ⟨⟨Aa, ψ⟩, hxa⟩ := hΨsurj τa
  rw [primeFormPsi_apply] at hxa
  have hconj1 : ∀ A : U, primeFormConjHom h _ A = 1 ↔
      ∃ c : Kˣ, h.norm (c : K) = 1 ∧
        (A : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    intro A
    have e := hker1 ⟨A, 1⟩
    rw [primeFormPsi_apply, map_one, mul_one] at e
    rw [e]
    exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩
  obtain ⟨k, -, hk⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow h.prime
    (by have := h.one_le; omega : 1 ≤ 2 * f) h.card ψ
  set u := p ^ k with hu
  set B : U := Aa * primeFormFieldU h hC ψ Ay * Aa⁻¹ with hB
  have hconj : τa * τy * τa⁻¹ = primeFormConjHom h _ B := by
    rw [← hxa, ← hAy, hB, map_mul, map_mul, map_inv, ← primeFormField_conj_eq h hC ψ Ay]
    group
  have hone : primeFormConjHom h _ (B * Ay) = 1 := by
    rw [map_mul, ← hconj, hrel, hAy, inv_mul_cancel]
  obtain ⟨c, hc, hBc⟩ := (hconj1 _).1 hone
  set δ := Matrix.GeneralLinearGroup.det (Ay : GL (Fin d) K) with hδdef
  have hδu : Units.map (ψ : K →* K) δ = δ ^ u :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hk (δ : K))
  have hdet1 : δ ^ (u + 1) = c ^ d := by
    have e1 := congrArg Matrix.GeneralLinearGroup.det hBc
    rw [det_scalar_eq] at e1
    rw [← e1, pow_succ]
    simp only [hB, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, map_mul, map_inv,
      det_glAut]
    rw [← hδdef, hδu, mul_right_comm _ (δ ^ u), mul_inv_cancel, one_mul]
  obtain ⟨s, hs⟩ := (hinn _).1 hyr
  have hone' : primeFormConjHom h _ (Ay ^ r * (⟨(s : GL (Fin d) K), s.2.1⟩ : U)⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, hAy, ← hs, mul_inv_cancel]
  obtain ⟨c', hc', hc'e⟩ := (hconj1 _).1 hone'
  have hdets : Matrix.GeneralLinearGroup.det (s : GL (Fin d) K) = 1 :=
    Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact s.2.2)
  have hdet2 : δ ^ r = c' ^ d := by
    have e1 := congrArg Matrix.GeneralLinearGroup.det hc'e
    rw [det_scalar_eq] at e1
    rw [← e1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_inv, map_pow,
      hdets, inv_one, mul_one]
    rfl
  have hnot : ∀ c'' : Kˣ, h.norm (c'' : K) = 1 → c'' ^ d ≠ δ := by
    intro c'' hc'' hcd
    apply hy1
    have hcU : Matrix.GeneralLinearGroup.scalar (Fin d) c'' ∈ U :=
      scalar_mem_primeFormUnitary_one h hc''
    set A' : U := Ay * (⟨_, hcU⟩ : U)⁻¹ with hA'
    have hdetA' : Matrix.GeneralLinearGroup.det (A' : GL (Fin d) K) = 1 := by
      simp only [hA', Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, det_scalar_eq, hcd]
      rw [← hδdef, mul_inv_cancel]
    have hA'S : (A' : GL (Fin d) K) ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      ⟨A'.2, by
        have := congrArg Units.val hdetA'
        rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this⟩
    have hcA' : primeFormConjHom h _ A' = τy := by
      rw [hA', map_mul, map_inv, hAy, (hconj1 _).2 ⟨c'', hc'', rfl⟩, inv_one, mul_one]
    exact (hinn _).2 ⟨⟨_, hA'S⟩, hcA'.symm⟩
  refine ⟨Aa, ψ, u, hxa.symm, hk, ?_⟩
  by_contra hndvd
  have hcop : Nat.Coprime r (u + 1) := (Nat.Prime.coprime_iff_not_dvd hr).2 hndvd
  obtain ⟨σ₁, σ₂, hσ⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hpow : ∀ (a : Kˣ) (n : ℤ), (a ^ n) ^ d = (a ^ d) ^ n := fun a n => by
    rw [← zpow_natCast, ← zpow_natCast a d, ← zpow_mul, ← zpow_mul, mul_comm]
  have hδeq : (c' ^ σ₁ * c ^ σ₂) ^ d = δ := by
    rw [mul_pow, hpow, hpow, ← hdet2, ← hdet1, ← zpow_natCast δ r, ← zpow_natCast δ (u + 1),
      ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (r : ℤ) * σ₁ + ((u + 1 : ℕ) : ℤ) * σ₂ = 1 := by linarith
    rw [this, zpow_one]
  have hmemN : c' ^ σ₁ * c ^ σ₂ ∈ (Units.map h.normHom).ker :=
    mul_mem (zpow_mem ((h.mem_ker_normUnits).2 hc') σ₁) (zpow_mem ((h.mem_ker_normUnits).2 hc) σ₂)
  exact hnot _ ((h.mem_ker_normUnits).1 hmemN) hδeq

end Diag

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.LinkPSUAux
