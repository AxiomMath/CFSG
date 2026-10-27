module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem scalar_mem_primeFormUnitary_one {c : Kˣ} (hc : h.norm (c : K) = 1) :
    GeneralLinearGroup.scalar (Fin n) c ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hc,
    one_smul]

theorem exists_mem_primeFormUnitary_one_det_eq (hn : 1 ≤ n) {u : Kˣ} (hu : h.norm (u : K) = 1) :
    ∃ A : GL (Fin n) K, A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (A : Matrix (Fin n) (Fin n) K).det = u := by
  classical
  have hdet : (Matrix.diagonal (Pi.mulSingle (⟨0, hn⟩ : Fin n) (u : K))).det = u := by
    rw [Matrix.det_diagonal, Finset.prod_pi_mulSingle']
    simp
  refine ⟨GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal (Pi.mulSingle (⟨0, hn⟩ : Fin n) (u : K))) (by rw [hdet]; exact u.ne_zero),
    ?_, hdet⟩
  rw [mem_primeFormUnitary]
  change ((Matrix.diagonal (Pi.mulSingle (⟨0, hn⟩ : Fin n) (u : K))).map h.bar)ᵀ *
    (1 : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (Pi.mulSingle (⟨0, hn⟩ : Fin n) (u : K)) = 1
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose, Matrix.mul_one,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = ⟨0, hn⟩
  · subst hi
    rw [Pi.mulSingle_eq_same, mul_comm]
    exact hu
  · rw [Pi.mulSingle_eq_of_ne hi, map_one, one_mul]

@[expose] def unitaryOneDet :
    primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
      (Units.map h.normHom).ker :=
  (GeneralLinearGroup.det.comp (primeFormUnitary h _).subtype).codRestrict _ fun A =>
    (h.mem_ker_normUnits).2 (norm_det_eq_one h 1 A.2)

theorem coe_unitaryOneDet
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    (((unitaryOneDet h A : (Units.map h.normHom).ker) : Kˣ) : K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det :=
  rfl

theorem unitaryOneDet_surjective (hn : 1 ≤ n) : Function.Surjective (unitaryOneDet (n := n) h) := by
  rintro ⟨u, hu⟩
  obtain ⟨A, hA, hdet⟩ :=
    exists_mem_primeFormUnitary_one_det_eq h hn ((h.mem_ker_normUnits).1 hu)
  exact ⟨⟨A, hA⟩, Subtype.ext (Units.ext hdet)⟩

theorem exists_unitaryOne_diagonal_quotient (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    ∃ Φ : (Units.map h.normHom).ker →*
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
          (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
            (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      Function.Surjective Φ ∧
        Φ.ker =
          (powMonoidHom n : (Units.map h.normHom).ker →* (Units.map h.normHom).ker).range := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, hker1, -, -, -, -, -, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set U := primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set I := inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  have hconj1 : ∀ A : U, primeFormConjHom h _ A = 1 ↔
      ∃ c : Kˣ, h.norm (c : K) = 1 ∧ (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
    intro A
    have e := hker1 ⟨A, 1⟩
    rw [primeFormPsi_apply, map_one, mul_one] at e
    rw [e]
    exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩
  have hdetsc : ∀ c : Kˣ,
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
        (c : K) ^ n := fun c => by
    have e := congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin n) c)
    rw [Units.val_pow_eq_pow_val, Fintype.card_fin] at e
    exact e
  set δ := unitaryOneDet (n := n) h
  have hδ : Function.Surjective δ := unitaryOneDet_surjective h (by omega)
  set c : U →* D := (primeFormConjHom h _).codRestrict D fun A => ⟨A, rfl⟩
  set Φ : U →* D ⧸ I.subgroupOf D := (QuotientGroup.mk' (I.subgroupOf D)).comp c
  have hΦ : ∀ A : U, Φ A = 1 ↔ primeFormConjHom h _ A ∈ I := fun A => by
    change (QuotientGroup.mk' (I.subgroupOf D) (c A)) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hle : δ.ker ≤ Φ.ker := fun A hA => by
    rw [MonoidHom.mem_ker, hΦ, hinn]
    have hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [← coe_unitaryOneDet h A, MonoidHom.mem_ker.1 hA]
      rfl
    exact ⟨⟨A, A.2, hdet⟩, rfl⟩
  set Ψ := (QuotientGroup.lift δ.ker Φ hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective δ hδ).symm.toMonoidHom
  have hΨ : ∀ A, Ψ (δ A) = Φ A := fun A => by
    have e : (QuotientGroup.quotientKerEquivOfSurjective δ hδ).symm (δ A) =
        (A : U ⧸ δ.ker) := (MulEquiv.symm_apply_eq _).mpr rfl
    change QuotientGroup.lift δ.ker Φ hle
      ((QuotientGroup.quotientKerEquivOfSurjective δ hδ).symm (δ A)) = _
    rw [e, QuotientGroup.lift_mk]
  have hΦsurj : Function.Surjective Φ := by
    refine (QuotientGroup.mk'_surjective _).comp fun y => ?_
    obtain ⟨A, hA⟩ := y.2
    exact ⟨A, Subtype.ext hA⟩
  refine ⟨Ψ, fun y => ?_, le_antisymm (fun x hx => ?_) ?_⟩
  · obtain ⟨A, rfl⟩ := hΦsurj y
    exact ⟨δ A, hΨ A⟩
  ·
    obtain ⟨A, rfl⟩ := hδ x
    rw [MonoidHom.mem_ker, hΨ, hΦ, hinn] at hx
    obtain ⟨s, hs⟩ := hx
    have hAs : primeFormConjHom h _ (A * (⟨s, s.2.1⟩ : U)⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    obtain ⟨c, hc, hcA⟩ := (hconj1 _).1 hAs
    have hcU : c ∈ (Units.map h.normHom).ker := (h.mem_ker_normUnits).2 hc
    refine ⟨⟨c, hcU⟩, Subtype.ext (Units.ext ?_)⟩
    have hA : (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * s := by
      rw [← hcA, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [powMonoidHom_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_unitaryOneDet, hA,
      Units.val_mul, Matrix.det_mul, s.2.2, mul_one, hdetsc]
  ·
    rintro _ ⟨y, rfl⟩
    have hyU : GeneralLinearGroup.scalar (Fin n) (y : Kˣ) ∈ U :=
      scalar_mem_primeFormUnitary_one h ((h.mem_ker_normUnits).1 y.2)
    have hδy : δ ⟨_, hyU⟩ = powMonoidHom n y := by
      refine Subtype.ext (Units.ext ?_)
      rw [coe_unitaryOneDet, powMonoidHom_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      exact hdetsc _
    rw [MonoidHom.mem_ker, ← hδy, hΨ, hΦ, (hconj1 _).2 ⟨y, (h.mem_ker_normUnits).1 y.2, rfl⟩]
    exact one_mem _

theorem unitary_full_diagonal_outer_order (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Nonempty (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃* unitaryPSU h n) ∧
    IsCyclic (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
      (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
        (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
    Nat.card (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
      (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
        (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      Nat.gcd n (p ^ f + 1) ∧
    Nat.card (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      2 * f * Nat.gcd n (p ^ f + 1) ∧
    Nat.card (Outer (unitaryPSU h n)) = 2 * f * Nat.gcd n (p ^ f + 1) ∧
    (n = 3 → ∀ r : ℕ, r.Prime → 3 < r → ¬ r ∣ f →
      ∀ P : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
        IsPGroup r P →
          P ≤ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
  classical
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨eT⟩, -, -, -, -, -, hFsurj, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set I := inner T
  obtain ⟨Φ, hΦ, hker⟩ := exists_unitaryOne_diagonal_quotient h hn hq
  have hK1 : Nat.card (Units.map h.normHom).ker = p ^ f + 1 := (unitary_field_norm h).2.2.1
  have hcyc : IsCyclic (D ⧸ I.subgroupOf D) := isCyclic_of_surjective Φ hΦ
  have hcardDI : Nat.card (D ⧸ I.subgroupOf D) = Nat.gcd n (p ^ f + 1) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ).toEquiv,
      ← Subgroup.index_eq_card, hker, IsCyclic.index_powMonoidHom_range, hK1, Nat.gcd_comm]
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have hDindex : D.index = 2 * f := by
    rw [← hFker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hFsurj, Subgroup.card_top]
    exact (card_ringAut_and_isCyclic h.prime K h.card).1
  have hout : Nat.card (Outer T) = 2 * f * Nat.gcd n (p ^ f + 1) := by
    change Nat.card (MulAut T ⧸ I) = _
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex_mul_index hID, hDindex, mul_comm,
      Subgroup.relIndex, Subgroup.index_eq_card, hcardDI]
  refine ⟨⟨eT⟩, hcyc, hcardDI, hout, ?_, fun hn3 r hr hr3 hrf P hP x hx => ?_⟩
  · rw [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eT).toEquiv]
    exact hout
  ·
    have hcop : Nat.Coprime r (Nat.card (Outer T)) := by
      rw [hout, hn3]
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right
        ((Nat.coprime_primes hr Nat.prime_two).2 (by omega))
        ((Nat.Prime.coprime_iff_not_dvd hr).2 hrf)) ?_
      exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
        ((Nat.coprime_primes hr Nat.prime_three).2 (by omega))
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hxk : x ^ (r ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : (QuotientGroup.mk x : Outer T) ^ (r ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow, hxk, QuotientGroup.mk_one]
    have h3 := pow_gcd_eq_one.2 ⟨h1, pow_card_eq_one'⟩
    rw [Nat.Coprime.pow_left k hcop, pow_one] at h3
    exact (QuotientGroup.eq_one_iff x).1 h3

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
