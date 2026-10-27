module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem hpow2_aux {G : Type} [CommGroup G] (a : G) (k : ℤ) (m : ℕ) :
    (a ^ k) ^ m = (a ^ m) ^ k := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

theorem exists_pow_of_pow_three_mem {G : Type} [CommGroup G] (S : Subgroup G) {N n : ℕ}
    (hN : ∀ x ∈ S, x ^ N = 1) (hdiv : ¬ 3 ∣ Nat.gcd n N) {c u : G} (hc : c ∈ S) (hu : u ∈ S)
    (h3 : c ^ 3 = u ^ n) : ∃ μ ∈ S, c = μ ^ n := by
  have hpow2 := hpow2_aux (G := G)
  set d : ℕ := Nat.gcd n N with hd
  have hbez : (d : ℤ) = (n : ℤ) * Nat.gcdA n N + (N : ℤ) * Nat.gcdB n N := Nat.gcd_eq_gcd_ab n N
  have hcN : c ^ (N : ℤ) = 1 := by
    rw [zpow_natCast]
    exact hN c hc
  have hcd : c ^ (d : ℤ) = (c ^ Nat.gcdA n N) ^ n := by
    rw [hbez, zpow_add, zpow_mul, zpow_mul, hcN, one_zpow, mul_one, zpow_natCast]
    exact (hpow2 c (Nat.gcdA n N) n).symm
  have hcop : Nat.Coprime 3 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hdiv
  have hbez3 : (1 : ℤ) = 3 * Nat.gcdA 3 d + (d : ℤ) * Nat.gcdB 3 d := by
    have h := Nat.gcd_eq_gcd_ab 3 d
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact_mod_cast h
  set s : ℤ := Nat.gcdA 3 d
  set t : ℤ := Nat.gcdB 3 d
  refine ⟨u ^ s * (c ^ Nat.gcdA n N) ^ t, ?_, ?_⟩
  · refine S.mul_mem (S.zpow_mem hu s) (S.zpow_mem (S.zpow_mem hc _) t)
  · have key : c = (c ^ (3 : ℤ)) ^ s * (c ^ (d : ℤ)) ^ t := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez3, zpow_one]
    calc c = (c ^ (3 : ℤ)) ^ s * (c ^ (d : ℤ)) ^ t := key
      _ = (u ^ n) ^ s * ((c ^ Nat.gcdA n N) ^ n) ^ t := by
          rw [zpow_ofNat, h3, hcd]
      _ = (u ^ s * (c ^ Nat.gcdA n N) ^ t) ^ n := by
          rw [mul_pow, hpow2 u s n, hpow2 (c ^ Nat.gcdA n N) t n]

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem scalar_central (n : ℕ) (μ : Kˣ) (g : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.scalar (Fin n) μ * g * (Matrix.GeneralLinearGroup.scalar (Fin n) μ)⁻¹
      = g := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin n) μ * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin n) μ := by
    apply Units.ext
    exact (Matrix.scalar_commute (n := Fin n) (μ : K) (fun _ => Commute.all _ _)
      (g : Matrix (Fin n) (Fin n) K)).eq
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem norm_eq_one_iff_pow (h : UnitaryFieldData ℓ f K) (x : Kˣ) :
    h.norm (x : K) = 1 ↔ x ^ (ℓ ^ f + 1) = 1 := by
  have key : h.norm (x : K) = ((x ^ (ℓ ^ f + 1) : Kˣ) : K) := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val, pow_succ,
      mul_comm]
  rw [key, Units.val_eq_one]

theorem primeFormConjHom_scalar_eq_one (h : UnitaryFieldData ℓ f K) {m : ℕ}
    (C : Matrix (Fin m) (Fin m) K) (μ : Kˣ)
    (hμ : Matrix.GeneralLinearGroup.scalar (Fin m) μ ∈ primeFormUnitary h C) :
    primeFormConjHom h C ⟨_, hμ⟩ = 1 := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  exact congrArg (fun x : CFSG.ClassicalGroups.UnitaryFlag.gramSU h C => (x : primeFormP h C))
    (Subtype.ext (scalar_central m μ g))

theorem primeFormConjHom_mem_inner_of_det (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n)
    (hdiv : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (c : Kˣ)
    (hc : h.norm (c : K) = 1)
    (hA3 : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A ∈
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  set S : Subgroup Kˣ := rootsOfUnity (ℓ ^ f + 1) K with hS
  have hmemS : ∀ x : Kˣ, x ∈ S ↔ h.norm (x : K) = 1 := fun x => by
    rw [hS, mem_rootsOfUnity, norm_eq_one_iff_pow]
  have hN : ∀ x ∈ S, x ^ (ℓ ^ f + 1) = 1 := fun x hx => (mem_rootsOfUnity _ _).mp hx
  have hdS : Matrix.GeneralLinearGroup.det (A : GL (Fin n) K) ∈ S := by
    rw [hmemS, Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h (1 : GL (Fin n) K) A.2
  have hcS : c ∈ S := (hmemS c).mpr hc
  have hd3 : (Matrix.GeneralLinearGroup.det (A : GL (Fin n) K)) ^ 3 = c ^ n := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hA3
    rw [map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    exact h1
  obtain ⟨μ, hμS, hμ⟩ := exists_pow_of_pow_three_mem S hN hdiv hdS hcS hd3
  have hμn : h.norm (μ : K) = 1 := (hmemS μ).mp hμS
  have hμinvS : μ⁻¹ ∈ S := S.inv_mem hμS
  have hμinvn : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := (hmemS _).mp hμinvS
  have hμU : Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    scalar_mem_primeFormUnitary_one h hμinvn
  have hμU' : Matrix.GeneralLinearGroup.scalar (Fin n) μ ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    scalar_mem_primeFormUnitary_one h hμn
  set B : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (A : GL (Fin n) K) with hB
  have hBU : B ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).mul_mem hμU A.2
  have hBdet : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := by
      rw [hB, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hμ,
        inv_pow, inv_mul_cancel]
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  have hBgram : B ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (mem_gramSU_iff_unitary h).mpr ⟨hBU, hBdet⟩
  have hA : A = (⟨Matrix.GeneralLinearGroup.scalar (Fin n) μ, hμU'⟩ :
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ⟨B, hBU⟩ := by
    apply Subtype.ext
    show (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) μ * B
    rw [hB, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hA, map_mul, primeFormConjHom_scalar_eq_one h _ μ hμU', one_mul]
  have hconj := primeFormConjHom_eq_conj h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    ⟨B, hBgram⟩
  rw [hconj]
  exact ⟨_, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
