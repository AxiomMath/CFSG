module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

namespace T4OutCore

theorem commutator_mem_of_decomposition {G : Type*} [Group G] (I : Subgroup G) [I.Normal]
    (D Φ : Set G) (hdec : ∀ g : G, ∃ d ∈ D, ∃ φ ∈ Φ, g = d * φ)
    (hΦ : ∀ φ ∈ Φ, ∀ ψ ∈ Φ, φ * ψ = ψ * φ)
    (hD : ∀ d ∈ D, ∀ g : G, d * g * d⁻¹ * g⁻¹ ∈ I) (a b : G) :
    a * b * a⁻¹ * b⁻¹ ∈ I := by
  have hcen : ∀ d ∈ D, ∀ g : G, ((d : G) : G ⧸ I) * (g : G ⧸ I) = (g : G ⧸ I) * (d : G ⧸ I) := by
    intro d hd g
    have h1 := hD d hd g
    rw [← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    have h2 : (d : G ⧸ I) * (g : G ⧸ I) =
        ((d : G ⧸ I) * (g : G ⧸ I) * (d : G ⧸ I)⁻¹ * (g : G ⧸ I)⁻¹) *
          ((g : G ⧸ I) * (d : G ⧸ I)) := by group
    rw [h2, h1, one_mul]
  obtain ⟨d, hd, φ, hφ, rfl⟩ := hdec a
  obtain ⟨e, he, ψ, hψ, rfl⟩ := hdec b
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hxu := hcen d hd e
  have hxv := hcen d hd ψ
  have huy := hcen e he φ
  have hyv : (φ : G ⧸ I) * (ψ : G ⧸ I) = (ψ : G ⧸ I) * (φ : G ⧸ I) := by
    have := congrArg (QuotientGroup.mk (s := I)) (hΦ φ hφ ψ hψ)
    simpa [QuotientGroup.mk_mul] using this
  generalize (d : G ⧸ I) = x at *
  generalize (φ : G ⧸ I) = y at *
  generalize (e : G ⧸ I) = u at *
  generalize (ψ : G ⧸ I) = v at *
  have key : x * y * (u * v) = u * v * (x * y) := by
    calc x * y * (u * v) = x * (y * u) * v := by group
      _ = x * (u * y) * v := by rw [← huy]
      _ = x * u * (y * v) := by group
      _ = x * u * (v * y) := by rw [hyv]
      _ = u * x * (v * y) := by rw [hxu]
      _ = u * (x * v) * y := by group
      _ = u * (v * x) * y := by rw [hxv]
      _ = u * v * (x * y) := by group
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  calc x * y * (u * v) * (y⁻¹ * x⁻¹) * (v⁻¹ * u⁻¹)
      = (x * y * (u * v)) * (x * y)⁻¹ * (u * v)⁻¹ := by group
    _ = 1 := by rw [key]; group

theorem mem_of_commutator_mem {G : Type*} [Group G] {S : Subgroup G}
    (h : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) {x : G} (hx : x ∈ commutator G) : x ∈ S := by
  have : commutator G ≤ S := by
    change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ S
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact h a b
  exact this hx

theorem exists_pow_four_of_sq {Γ : Type*} [Group Γ] {y : Γ} {k : ℕ} (hk : Odd k)
    (hy : y ^ (2 * k) = 1) : ∃ j : ℕ, (y ^ j) ^ 4 = y ^ 2 := by
  obtain ⟨a, rfl⟩ := hk
  refine ⟨2 * (a + 1) ^ 2, ?_⟩
  have h : y ^ (2 * (a + 1) ^ 2 * 4) = y ^ 2 * (y ^ (2 * (2 * a + 1))) ^ (2 * a + 3) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [← pow_mul, h, hy, one_pow, mul_one]

theorem exists_odd_zpow_units {K : Type*} [Field K] [Finite K] (hK : (2 : K) ≠ 0) (σ : K ≃+* K) :
    ∃ m : ℤ, Odd m ∧ ∀ x : Kˣ, Units.map ((σ : K →+* K) : K →* K) x = x ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Units.map ((σ : K →+* K) : K →* K))
  refine ⟨m, ?_, hm⟩
  by_contra hodd
  rw [Int.not_odd_iff_even] at hodd
  obtain ⟨j, hj⟩ := hodd
  have h1 : Units.map ((σ : K →+* K) : K →* K) (-1) = -1 := by
    ext
    simp
  have h2 : ((-1 : Kˣ)) ^ m = 1 := by
    rw [hj, ← two_mul, _root_.zpow_mul]
    simp
  rw [hm, h2] at h1
  have := congrArg (fun u : Kˣ => (u : K)) h1
  simp at this
  apply hK
  linear_combination this

theorem two_ne_zero_of_charP {K : Type*} [Field K] {p : ℕ} [CharP K p] (hp : p.Prime)
    (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem two_ne_zero_of_odd_card {K : Type*} [Field K] [Finite K] (h : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  intro h2
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have h3 : ringChar K = 2 := ringChar.eq K 2
  have h4 : Even (Fintype.card K) := Nat.even_iff.mpr (FiniteField.even_card_iff_char_two.mp h3)
  rw [Nat.card_eq_fintype_card] at h
  exact (Nat.not_even_iff_odd.mpr h) h4

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] {n : ℕ}


theorem det_inverseTranspose (A : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose A) =
      (GeneralLinearGroup.det A)⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose,
    Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply, map_inv]

theorem conjAut_mem_inner_of_det {C : GL (Fin n) K} {y : Kˣ}
    (hC : GeneralLinearGroup.det C = y ^ n) :
    conjAut n K C ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_range_conj_of_det_eq_pow hC

variable [Finite K]

theorem exists_conj_det (hn : 3 ≤ n) (hK2 : (2 : K) ≠ 0) (g : MulAut (projectiveSL n K)) :
    ∃ m : ℤ, Odd m ∧ ∀ A : GL (Fin n) K, ∃ A' : GL (Fin n) K,
      g * conjAut n K A * g⁻¹ = conjAut n K A' ∧
        GeneralLinearGroup.det A' = (GeneralLinearGroup.det A) ^ m := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨B, σ, ε, hε, rfl⟩ := hform g
  obtain ⟨-, -, hfc, hδδ, hδc, -, -⟩ := standard_automorphism_transport (K := K) (n := n)
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
  obtain ⟨m, hm, hσ⟩ := exists_odd_zpow_units hK2 σ
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · refine ⟨m, hm, fun A => ⟨B * GeneralLinearGroup.map (σ : K →+* K) A * B⁻¹, ?_, ?_⟩⟩
    · rw [pow_zero, mul_one]
      calc conjAut n K B * fieldAut n K σ * conjAut n K A * (conjAut n K B * fieldAut n K σ)⁻¹
          = conjAut n K B * (fieldAut n K σ * conjAut n K A * (fieldAut n K σ)⁻¹) *
              (conjAut n K B)⁻¹ := by group
        _ = _ := by rw [hfc σ A, ← map_inv, ← map_mul, ← map_mul]
    · rw [map_mul, map_mul, map_inv, GeneralLinearGroup.map_det, hσ,
        mul_comm (GeneralLinearGroup.det B), mul_inv_cancel_right]
  · refine ⟨-m, hm.neg, fun A => ⟨B * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose A) * B⁻¹, ?_, ?_⟩⟩
    · rw [pow_one, _root_.mul_inv_rev, hδinv]
      calc conjAut n K B * fieldAut n K σ * dualAut n K * conjAut n K A *
            (dualAut n K * (conjAut n K B * fieldAut n K σ)⁻¹)
          = conjAut n K B * (fieldAut n K σ * (dualAut n K * conjAut n K A * dualAut n K) *
              (fieldAut n K σ)⁻¹) * (conjAut n K B)⁻¹ := by group
        _ = _ := by rw [hδc A, hfc σ, ← map_inv, ← map_mul, ← map_mul]
    · rw [map_mul, map_mul, map_inv, GeneralLinearGroup.map_det, det_inverseTranspose, map_inv, hσ,
        mul_comm (GeneralLinearGroup.det B), mul_inv_cancel_right, _root_.zpow_neg]

theorem linear_commutator_inner_four (hK : Nat.card K % 4 = 3) (α β : MulAut (projectiveSL 4 K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  have hodd : Odd (Nat.card K) := by rw [Nat.odd_iff]; omega
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have htrans := standard_automorphism_transport (K := K) (n := 4)
  obtain ⟨-, -, -, hδδ, -, hδf, -⟩ := standard_automorphism_transport (K := K) (n := 4)
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcommK : ∀ σ τ : K ≃+* K, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm σ τ
  have hff : ∀ σ τ : K ≃+* K, Commute (fieldAut 4 K σ) (fieldAut 4 K τ) := by
    intro σ τ
    change _ * _ = _ * _
    rw [htrans.2.1, htrans.2.1, hcommK]
  have hfδ : ∀ σ : K ≃+* K, Commute (fieldAut 4 K σ) (dualAut 4 K) := by
    intro σ
    change _ * _ = _ * _
    calc fieldAut 4 K σ * dualAut 4 K = dualAut 4 K * fieldAut 4 K σ * dualAut 4 K * dualAut 4 K :=
          by rw [hδf σ]
      _ = dualAut 4 K * fieldAut 4 K σ := by
          rw [mul_assoc _ (dualAut 4 K) (dualAut 4 K), hδδ, mul_one]
  have hcard : ∃ k : ℕ, Odd k ∧ Nat.card Kˣ = 2 * k := by
    refine ⟨(Nat.card K - 1) / 2, ?_, ?_⟩
    · rw [Nat.odd_iff]; omega
    · rw [Nat.card_units]; omega
  refine commutator_mem_of_decomposition (inner (projectiveSL 4 K)) (Set.range (conjAut 4 K))
    {φ | ∃ (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ φ = fieldAut 4 K σ * dualAut 4 K ^ ε} ?_ ?_ ?_ α β
  · intro g
    obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
    obtain ⟨A, σ, ε, hε, rfl⟩ := hform g
    exact ⟨conjAut 4 K A, ⟨A, rfl⟩, fieldAut 4 K σ * dualAut 4 K ^ ε, ⟨σ, ε, hε, rfl⟩,
      by rw [mul_assoc]⟩
  · rintro _ ⟨σ, ε, -, rfl⟩ _ ⟨τ, η, -, rfl⟩
    exact (((hff σ τ).mul_right ((hfδ σ).pow_right η)).mul_left
      (((hfδ τ).symm.pow_left ε).mul_right ((Commute.refl (dualAut 4 K)).pow_pow ε η))).eq
  · rintro _ ⟨A, rfl⟩ g
    obtain ⟨m, hm, hg⟩ := exists_conj_det (by norm_num) hK2 g
    obtain ⟨A', hA', hdet⟩ := hg A
    have hc : conjAut 4 K A * g * (conjAut 4 K A)⁻¹ * g⁻¹ = conjAut 4 K (A * A'⁻¹) := by
      rw [map_mul, map_inv, ← hA']
      group
    rw [hc]
    obtain ⟨j, hj⟩ := hm
    obtain ⟨k, hk, hkc⟩ := hcard
    generalize hx : GeneralLinearGroup.det A = x at hdet
    have h1 : GeneralLinearGroup.det (A * A'⁻¹) = (x ^ (-j)) ^ 2 := by
      rw [map_mul, map_inv, hdet, hj, hx]
      group
    have h2 : (x ^ (-j)) ^ (2 * k) = 1 := by
      rw [← hkc]
      exact pow_card_eq_one'
    obtain ⟨i, hi⟩ := exists_pow_four_of_sq hk h2
    exact conjAut_mem_inner_of_det (y := (x ^ (-j)) ^ i) (by rw [h1, ← hi])

theorem linear_involution_inner_five {a : MulAut (projectiveSL 5 K)}
    (ha : a ∈ commutator (MulAut (projectiveSL 5 K))) (ha2 : a ^ 2 = 1) :
    a ∈ (MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range := by
  have hD : a ∈ linearAutGroup 5 K := mem_of_commutator_mem
    (fun α β => CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
      (by norm_num) α β) ha
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hD
  obtain ⟨-, hcard⟩ := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_diagonal_outer
    (K := K) (n := 5) (by norm_num)
  set φ := (QuotientGroup.mk' (inner (projectiveSL 5 K))).comp (conjAut 5 K) with hφ
  have hmem : (QuotientGroup.mk a : MulAut (projectiveSL 5 K) ⧸ inner (projectiveSL 5 K)) ∈
      φ.range := ⟨A, by rw [hφ, MonoidHom.comp_apply, hA]; rfl⟩
  set x : ↥φ.range := ⟨_, hmem⟩ with hxdef
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    change (QuotientGroup.mk a : MulAut (projectiveSL 5 K) ⧸ inner (projectiveSL 5 K)) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, ha2, QuotientGroup.mk_one]
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf x ∣ Nat.card ↥φ.range := orderOf_dvd_natCard x
  have h5 : orderOf x ∣ 5 := h2.trans (hcard.trans (Nat.gcd_dvd_left 5 _))
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h5
    simpa using this
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have h4 : (QuotientGroup.mk a : MulAut (projectiveSL 5 K) ⧸ inner (projectiveSL 5 K)) = 1 :=
    congrArg Subtype.val hx1
  exact (QuotientGroup.eq_one_iff (N := inner (projectiveSL 5 K)) a).mp h4

end Linear

section Unitary

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem primeFormConjHom_scalar (c : Kˣ) (hc : h.norm (c : K) = 1) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ⟨GeneralLinearGroup.scalar (Fin n) c, scalar_mem_primeFormUnitary_one h hc⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change GeneralLinearGroup.scalar (Fin n) c * (g : GL (Fin n) K) *
    (GeneralLinearGroup.scalar (Fin n) c)⁻¹ = g
  rw [(commute_scalar c (g : GL (Fin n) K)).symm.eq, mul_inv_cancel_right]

theorem primeFormConjHom_mem_inner_of_det
    (M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {v : Kˣ} (hv : h.norm (v : K) = 1)
    (hM : GeneralLinearGroup.det (M : GL (Fin n) K) = v ^ n) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M ∈
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hv' : h.norm ((v⁻¹ : Kˣ) : K) = 1 :=
    (UnitaryFieldData.mem_ker_normUnits h).mp (inv_mem ((UnitaryFieldData.mem_ker_normUnits h).mpr hv))
  set Z : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨GeneralLinearGroup.scalar (Fin n) v⁻¹, scalar_mem_primeFormUnitary_one h hv'⟩ with hZ
  have hS : ((Z * M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨(Z * M).2, ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, Subgroup.coe_mul, map_mul, hM]
    change ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) v⁻¹) * v ^ n : Kˣ) : K) = 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, inv_mul_cancel, Units.val_one]
  have hcZ : primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Z = 1 :=
    primeFormConjHom_scalar h v⁻¹ hv'
  have hM' : M = Z⁻¹ * (Z * M) := by group
  rw [hM', map_mul, map_inv, hcZ, inv_one, one_mul]
  rw [mem_inner_primeFormP h]
  exact ⟨⟨_, hS⟩, rfl⟩

theorem det_glAut (σ : K ≃+* K) (A : GL (Fin n) K) :
    GeneralLinearGroup.det (glAut σ A) =
      Units.map ((σ : K →+* K) : K →* K) (GeneralLinearGroup.det A) := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_glAut, Units.coe_map, GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K)).symm

theorem exists_conj_det_unitary [Finite K] (hK2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2))
    (g : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∃ m : ℤ, Odd m ∧ ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      ∃ A' : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        g * primeFormConjHom h _ A * g⁻¹ = primeFormConjHom h _ A' ∧
          GeneralLinearGroup.det (A' : GL (Fin n) K) =
            GeneralLinearGroup.det (A : GL (Fin n) K) ^ m := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, huniq, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨φ, ⟨B, rfl⟩, -⟩ := huniq g
  obtain ⟨m, hm, hφ⟩ := exists_odd_zpow_units hK2 φ
  refine ⟨m, hm, fun A => ⟨B * primeFormFieldU h hC φ A * B⁻¹, ?_, ?_⟩⟩
  · rw [map_mul, map_mul, map_inv, ← primeFormField_conj_eq h hC φ A]
    group
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
      coe_primeFormFieldU, det_glAut, hφ, mul_comm (GeneralLinearGroup.det (B : GL (Fin n) K)),
      mul_inv_cancel_right]

theorem commutator_mem_primeFormD' (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (α β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    α * β * α⁻¹ * β⁻¹ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have : Finite K := h.finite
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hq
  set F := primeFormFieldFactor h (isPrimeFormGram_one (n := n) (K := K)) hn hq
  rw [← hFker, MonoidHom.mem_ker, map_mul F, map_mul F, map_mul F, map_inv F, map_inv F,
    (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm (F α) (F β), mul_inv_cancel_right,
    mul_inv_cancel]

theorem unitary_commutator_inner_four (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (α β : MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range := by
  have : Finite K := h.finite
  have := h.charP
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_charP h.prime hp2
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_one
  have hq' : ¬((4 : ℕ) = 3 ∧ p ^ f = 2) := fun hh => absurd hh.1 (by norm_num)
  obtain ⟨-, -, -, -, huniq, -⟩ := unitary_prime_form_full_semilinear_realization h hC
    (by norm_num : 3 ≤ 4) hq'
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcommK : ∀ σ τ : K ≃+* K, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm σ τ
  obtain ⟨k, hk, hkc⟩ : ∃ k : ℕ, Odd k ∧ p ^ f + 1 = 2 * k := by
    refine ⟨(p ^ f + 1) / 2, ?_, ?_⟩
    · rw [Nat.odd_iff]; omega
    · omega
  refine commutator_mem_of_decomposition (inner _)
    (Set.range (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
    (Set.range (primeFormFieldHom h hC)) ?_ ?_ ?_ α β
  · intro g
    obtain ⟨φ, ⟨A, hA⟩, -⟩ := huniq g
    exact ⟨_, ⟨A, rfl⟩, _, ⟨φ, rfl⟩, hA⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, hcommK]
  · rintro _ ⟨A, rfl⟩ g
    obtain ⟨m, hm, hg⟩ := exists_conj_det_unitary h hK2 (by norm_num : 3 ≤ 4) hq' g
    obtain ⟨A', hA', hdet⟩ := hg A
    have hc : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A * g *
        (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A)⁻¹ * g⁻¹ =
        primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (A * A'⁻¹) := by
      rw [map_mul, map_inv, ← hA']
      group
    rw [hc]
    obtain ⟨j, hj⟩ := hm
    have hN := norm_det_eq_one h (1 : GL (Fin 4) K) A.2
    have hxN : (GeneralLinearGroup.det (A : GL (Fin 4) K)) ^ (p ^ f + 1) = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, ← UnitaryFieldData.norm_eq_pow]
      rw [GeneralLinearGroup.val_det_apply]
      exact hN
    generalize hx : GeneralLinearGroup.det (A : GL (Fin 4) K) = x at hdet hxN
    have h1 : GeneralLinearGroup.det ((A * A'⁻¹ : primeFormUnitary h
        ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : GL (Fin 4) K) = (x ^ (-j)) ^ 2 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hdet, hj, hx]
      group
    have h2 : (x ^ (-j)) ^ (2 * k) = 1 := by
      have hx2 : x ^ (2 * k) = 1 := by rw [← hkc]; exact hxN
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm (-j), _root_.zpow_mul,
        _root_.zpow_natCast, hx2, _root_.one_zpow]
    obtain ⟨i, hi⟩ := exists_pow_four_of_sq hk h2
    have h2' : (x ^ (-j)) ^ (p ^ f + 1) = 1 := by rw [hkc]; exact h2
    have hv : h.norm (((x ^ (-j)) ^ i : Kˣ) : K) = 1 := by
      rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, ← _root_.pow_mul, mul_comm i,
        _root_.pow_mul, h2', one_pow, Units.val_one]
    exact primeFormConjHom_mem_inner_of_det h (A * A'⁻¹) hv (by rw [h1, ← hi])

theorem unitary_involution_inner_five
    {a : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))}
    (ha : a ∈ commutator (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))
    (ha2 : a ^ 2 = 1) :
    a ∈ (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range := by
  have hq' : ¬((5 : ℕ) = 3 ∧ p ^ f = 2) := fun hh => absurd hh.1 (by norm_num)
  have hD : a ∈ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    mem_of_commutator_mem (fun α β => commutator_mem_primeFormD' h (by norm_num) hq' α β) ha
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (by norm_num : 3 ≤ 5) hq'
  set D := primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hDdef
  set I := inner (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) with hIdef
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk ⟨a, hD⟩ with hxdef
  have hx2 : x ^ 2 = 1 := by
    rw [hxdef, ← QuotientGroup.mk_pow]
    have : (⟨a, hD⟩ : D) ^ 2 = 1 := Subtype.ext ha2
    rw [this, QuotientGroup.mk_one]
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf x ∣ Nat.card (D ⧸ I.subgroupOf D) := orderOf_dvd_natCard x
  have h5 : orderOf x ∣ 5 := h2.trans ((dvd_of_eq hcard).trans (Nat.gcd_dvd_left 5 _))
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h5
    simpa using this
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have : (⟨a, hD⟩ : D) ∈ I.subgroupOf D := (QuotientGroup.eq_one_iff (N := I.subgroupOf D) _).mp hx1
  exact this

end Unitary

section Models

open CFSG.ComponentClassification

theorem commutator_inner_of_mulEquiv {J P : Type*} [Group J] [Group P] (e : J ≃* P)
    (hP : ∀ α β : MulAut P, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : P →* MulAut P).range)
    (α β : MulAut J) : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : J →* MulAut J).range := by
  have h1 := hP (MulAut.congr e α) (MulAut.congr e β)
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
  have h2 : MulAut.congr e (α * β * α⁻¹ * β⁻¹) ∈ (OuterAutomorphisms.inner J).map (MulAut.congr e).toMonoidHom := by
    rw [OuterAutomorphisms.inner_map_congr]
    exact h1
  obtain ⟨y, hy, hyeq⟩ := h2
  have h3 : y = α * β * α⁻¹ * β⁻¹ := (MulAut.congr e).injective hyeq
  rw [← h3]
  exact hy

theorem congr_mem_commutator {J P : Type*} [Group J] [Group P] (e : J ≃* P) {a : MulAut J}
    (ha : a ∈ commutator (MulAut J)) : MulAut.congr e a ∈ commutator (MulAut P) :=
  mem_of_commutator_mem
    (S := (commutator (MulAut P)).comap (MulAut.congr e).toMonoidHom) (fun x y => by
      rw [Subgroup.mem_comap]
      change MulAut.congr e (x * y * x⁻¹ * y⁻¹) ∈ commutator (MulAut P)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) ha

theorem inner_of_involution_of_mulEquiv {J P : Type*} [Group J] [Group P] (e : J ≃* P)
    (hP : ∀ a : MulAut P, a ∈ commutator (MulAut P) → a ^ 2 = 1 →
      a ∈ (MulAut.conj : P →* MulAut P).range)
    {a : MulAut J} (ha : a ∈ commutator (MulAut J)) (ha2 : a ^ 2 = 1) :
    a ∈ (MulAut.conj : J →* MulAut J).range := by
  have hc : MulAut.congr e a ∈ commutator (MulAut P) := congr_mem_commutator e ha
  have h1 := hP _ hc (by rw [← map_pow, ha2, map_one])
  have h2 : MulAut.congr e a ∈ (OuterAutomorphisms.inner J).map (MulAut.congr e).toMonoidHom := by
    rw [OuterAutomorphisms.inner_map_congr]
    exact h1
  obtain ⟨y, hy, hyeq⟩ := h2
  have h3 : y = a := (MulAut.congr e).injective hyeq
  rw [← h3]
  exact hy

theorem stated_PSL {J : Type} [Group J] {n p f : ℕ} (h : CFSG.Blueprint.LieModel J .PSL n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem stated_PSU {J : Type} [Group J] {n p f : ℕ} (h : CFSG.Blueprint.LieModel J .PSU n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

end Models


section ModelLemmas

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem linear_model {J : Type} [Group J] {n p f : ℕ} (hL : LieModel J .PSL n p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (J ≃* LinearFlag.projectiveSL n F) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := stated_PSL hL
  exact ⟨F, inferInstance, inferInstance, hF, ⟨e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n F).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F))⟩⟩

theorem primeForm_model {J : Type} [Group J] {n p f : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (hL : LieModel J .PSU n p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K),
      Nonempty (J ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := stated_PSU hL
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one (n := n)) hn hq
  exact ⟨F, inferInstance, h, ⟨(e₀.trans (unitaryPSUEquiv h (by omega)).symm).trans eT.symm⟩⟩

theorem commutator_inner_of_psl4 {J : Type} [Group J] {p f : ℕ} (hq : p ^ f % 4 = 3)
    (hL : LieModel J .PSL 4 p f) (α β : MulAut J) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : J →* MulAut J).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := linear_model hL
  exact commutator_inner_of_mulEquiv e (fun a b => linear_commutator_inner_four (by rw [hF]; exact hq) a b) α β

theorem commutator_inner_of_psu4 {J : Type} [Group J] {p f : ℕ} (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (hL : LieModel J .PSU 4 p f) (α β : MulAut J) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : J →* MulAut J).range := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := primeForm_model (n := 4) (by norm_num)
    (fun hh => absurd hh.1 (by norm_num)) hL
  exact commutator_inner_of_mulEquiv e (fun a b => unitary_commutator_inner_four h hp2 hq a b) α β

theorem inner_of_involution_psl5 {J : Type} [Group J] {p f : ℕ} (hL : LieModel J .PSL 5 p f)
    {a : MulAut J} (ha : a ∈ commutator (MulAut J)) (ha2 : a ^ 2 = 1) :
    a ∈ (MulAut.conj : J →* MulAut J).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := linear_model hL
  exact inner_of_involution_of_mulEquiv e (fun b hb hb2 => linear_involution_inner_five hb hb2) ha ha2

theorem inner_of_involution_psu5 {J : Type} [Group J] {p f : ℕ} (hL : LieModel J .PSU 5 p f)
    {a : MulAut J} (ha : a ∈ commutator (MulAut J)) (ha2 : a ^ 2 = 1) :
    a ∈ (MulAut.conj : J →* MulAut J).range := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := primeForm_model (n := 5) (by norm_num)
    (fun hh => absurd hh.1 (by norm_num)) hL
  exact inner_of_involution_of_mulEquiv e (fun b hb hb2 => unitary_involution_inner_five h hb hb2) ha ha2

theorem exists_model_commutator_diag_psl {J : Type} [Group J] {n p f : ℕ} (hn : 3 ≤ n)
    (hL : LieModel J .PSL n p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : J ≃* LinearFlag.projectiveSL n F),
      Nat.card F = p ^ f ∧ ∀ x ∈ commutator (MulAut J),
        ∃ A : GL (Fin n) F, x = MulAut.congr e.symm (LinearFlag.conjAut n F A) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := stated_PSL hL
  let ψ : J ≃* LinearFlag.projectiveSL n F := e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n F).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F))
  refine ⟨F, inferInstance, inferInstance, ψ, hF, fun x hx => ?_⟩
  have hD : MulAut.congr ψ x ∈ LinearFlag.linearAutGroup n F := mem_of_commutator_mem
    (fun α β => OuterDerived.commutator_mem_linearAutGroup hn α β) (congr_mem_commutator ψ hx)
  obtain ⟨A, hA⟩ := LinearFlag.mem_linearAutGroup_iff.mp hD
  refine ⟨A, ?_⟩
  rw [hA]
  exact ((MulAut.congr ψ).symm_apply_apply x).symm

open Matrix in
theorem exists_model_commutator_diag_psu {J : Type} [Group J] {n p f : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) (hL : LieModel J .PSU n p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K)
      (e : J ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      ∀ x ∈ commutator (MulAut J),
        ∃ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
          x = MulAut.congr e.symm (primeFormConjHom h _ A) := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := primeForm_model hn hq hL
  refine ⟨K, inferInstance, h, e, fun x hx => ?_⟩
  have hD : MulAut.congr e x ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    mem_of_commutator_mem (fun α β => commutator_mem_primeFormD' h hn hq α β)
      (congr_mem_commutator e hx)
  obtain ⟨A, hA⟩ := hD
  refine ⟨A, ?_⟩
  rw [hA]
  exact ((MulAut.congr e).symm_apply_apply x).symm

end ModelLemmas

theorem mem_of_conjNormal_mem_inner {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {t : N}
    (ht : (MulAut.conjNormal t : MulAut ↥H) ∈ (MulAut.conj : ↥H →* MulAut ↥H).range) : t ∈ H := by
  obtain ⟨c, hc⟩ := ht
  have key : ∀ x : ↥H, (c : N) * x * (c : N)⁻¹ = t * x * t⁻¹ := by
    intro x
    have := congrArg (fun a : MulAut ↥H => ((a x : ↥H) : N)) hc
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this
  have hcomm : ∀ x ∈ H, (c : N)⁻¹ * t * x = x * ((c : N)⁻¹ * t) := by
    intro x hx
    have h1 := key ⟨x, hx⟩
    have h2 : t * x = (c : N) * x * (c : N)⁻¹ * t := by
      have h3 : (c : N) * x * (c : N)⁻¹ * t = t * x * t⁻¹ * t := by
        rw [show (c : N) * x * (c : N)⁻¹ = t * x * t⁻¹ from h1]
      rw [h3, inv_mul_cancel_right]
    calc (c : N)⁻¹ * t * x = (c : N)⁻¹ * (t * x) := mul_assoc _ _ _
      _ = (c : N)⁻¹ * ((c : N) * x * (c : N)⁻¹ * t) := by rw [h2]
      _ = x * ((c : N)⁻¹ * t) := by group
  have h1 : (c : N)⁻¹ * t = 1 := hfaith _ hcomm
  have h2 : t = c := by
    have : t = (c : N) * ((c : N)⁻¹ * t) := by group
    rw [this, h1, mul_one]
  rw [h2]
  exact c.2


end T4OutCore

end CFSG.GH74.Generic.BProg.B2.T4
