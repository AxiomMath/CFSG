module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAutArith
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
public import CFSG.GH74.GLS.Stage4.T2F1LocH90
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem isElemAbelian_mono {p : ℕ} {G : Type*} [Group G] {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hle : F ≤ E) : IsElemAbelian p F :=
  CFSG.Open.IsElemAbelian.mono hE hle

theorem isElemAbelian_subgroupOf {p : ℕ} {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian p E) (D : Subgroup G) : IsElemAbelian p (E.subgroupOf D) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE D

theorem exists_ne_one_inf_of_cyclic {G : Type*} [Group G] [Finite G] (D N : Subgroup G)
    [(N.subgroupOf D).Normal] [IsCyclic (D ⧸ N.subgroupOf D)] {p : ℕ} (hp : p.Prime)
    (E : Subgroup G) (hle : E ≤ D) (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) :
    ∃ x ∈ E ⊓ N, x ≠ 1 := by
  have h1 := card_le_mul_card_inf_of_cyclic (N.subgroupOf D) hp (E.subgroupOf D)
    (isElemAbelian_subgroupOf hE D)
  have hcard : Nat.card (E.subgroupOf D) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hcard, hc] at h1
  have h2 : p ≤ Nat.card ↥(E.subgroupOf D ⊓ N.subgroupOf D) := by
    have : p * p ≤ p * Nat.card ↥(E.subgroupOf D ⊓ N.subgroupOf D) := by simpa [sq] using h1
    exact Nat.le_of_mul_le_mul_left this hp.pos
  by_contra hcon
  push Not at hcon
  have hbot : E.subgroupOf D ⊓ N.subgroupOf D = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hcon z ⟨hz.1, hz.2⟩)
  rw [hbot, Subgroup.card_bot] at h2
  exact absurd h2 (not_le.2 hp.one_lt)

theorem succ_dvd_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by zify [Nat.one_le_pow 2 q (by omega), hq]; ring⟩

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {n : ℕ}

theorem finite_mulAut_primeFormP (C : Matrix (Fin n) (Fin n) K) :
    Finite (MulAut (primeFormP h C)) := by
  have := h.finite
  exact Finite.of_injective (fun g : MulAut (primeFormP h C) => (g : primeFormP h C → primeFormP h C))
    fun a b hab => MulEquiv.ext (congrFun hab)

theorem primeFormConjHom_eq_one_iff (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ A = 1 ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨-, -, hker1, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hq
  have e := hker1 ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at e
  rw [e]
  exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩

theorem card_le_pow_unitary (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ n := by
  classical
  have : Finite K := h.finite
  have := finite_mulAut_primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, hFsurj, hFker, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set Φ := primeFormFieldFactor h hC hn hq with hΦ
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have : IsCyclic (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⧸ Φ.ker) :=
    isCyclic_of_surjective (QuotientGroup.quotientKerEquivOfSurjective Φ hFsurj).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective Φ hFsurj).symm.surjective
  have h1 := card_le_mul_card_inf_of_cyclic Φ.ker hp E hE
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card_eq_sq]
    exact hpq.trans (succ_dvd_sq_sub_one hq1)
  have h2 : Nat.card ↥(E ⊓ Φ.ker) ≤ p ^ (n - 1) :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel hp hp2 hpK (by omega)
      (primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (primeFormConjHom h _)
      (fun A => by
        rw [primeFormConjHom_eq_one_iff h hn hq A,
          CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
        constructor
        · rintro ⟨c, -, hc⟩
          exact ⟨c, hc⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) _ (hc ▸ A.2), hc⟩)
      (E ⊓ Φ.ker) (inf_le_right.trans hFker.le) (isElemAbelian_mono hE inf_le_left)
  calc Nat.card E ≤ p * Nat.card ↥(E ⊓ Φ.ker) := h1
    _ ≤ p * p ^ (n - 1) := Nat.mul_le_mul_left _ h2
    _ = p ^ n := by
      rw [← pow_succ']
      congr 1
      omega

theorem isCyclic_unitaryD_quotient (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    IsCyclic (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
      (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
        (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
  (unitary_full_diagonal_outer_order h hn hq).2.1


private theorem pow_succ_apply {F : Type} [Field F] (σ : F ≃+* F) (k : ℕ) (z : F) :
    (σ ^ (k + 1)) z = σ ((σ ^ k) z) := by
  rw [pow_succ']
  rfl

theorem prod_range_succ_apply {F : Type} [Field F] (σ : F ≃+* F) (x : F) (k : ℕ) :
    x * σ (∏ j ∈ Finset.range k, (σ ^ j) x) = ∏ j ∈ Finset.range (k + 1), (σ ^ j) x := by
  rw [Finset.prod_range_succ', map_prod, mul_comm]
  simp [pow_succ_apply]

theorem det_scalar_val (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  have e := congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin n) c)
  rw [Units.val_pow_eq_pow_val, Fintype.card_fin] at e
  exact e

theorem prod_eq_one_of_map_eq_smul (hn : 1 ≤ n) {a : GL (Fin n) K} {p : ℕ} {σ : K ≃+* K}
    (hσp : σ ^ p = 1) {u : K}
    (hma : (a : Matrix (Fin n) (Fin n) K).map σ = u • (a : Matrix (Fin n) (Fin n) K)) :
    ∏ i ∈ Finset.range p, (σ ^ i) u = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hiter : ∀ k : ℕ, (a : Matrix (Fin n) (Fin n) K).map (σ ^ k) =
      (∏ i ∈ Finset.range k, (σ ^ i) u) • (a : Matrix (Fin n) (Fin n) K) := by
    intro k
    induction k with
    | zero => ext i j; simp
    | succ k ih =>
      ext i j
      have h1 : (σ ^ k) ((a : Matrix (Fin n) (Fin n) K) i j) =
          (∏ x ∈ Finset.range k, (σ ^ x) u) * (a : Matrix (Fin n) (Fin n) K) i j := by
        have := congrFun (congrFun ih i) j
        simpa using this
      have h2 : σ ((a : Matrix (Fin n) (Fin n) K) i j) = u * (a : Matrix (Fin n) (Fin n) K) i j := by
        have := congrFun (congrFun hma i) j
        simpa using this
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      rw [pow_succ_apply, h1, map_mul, h2, ← prod_range_succ_apply]
      ring
  have e := hiter p
  rw [hσp] at e
  have h3 : (∏ i ∈ Finset.range p, (σ ^ i) u - 1) • (a : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [sub_smul, ← e, one_smul]
    ext i j
    simp
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 a.ne_zero

theorem conjHom_mem_inner_of_commute (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (hg : ¬ p ^ 2 ∣ Nat.gcd n (ℓ ^ f + 1)) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hcomm : primeFormFieldHom h isPrimeFormGram_one σ * primeFormConjHom h _ A =
      primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_one σ)
    (hAp : primeFormConjHom h _ A ^ p = 1) :
    primeFormConjHom h _ A ∈
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨u, hu1, hu⟩ : ∃ u : Kˣ, h.norm (u : K) = 1 ∧
      glAut σ (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) u * A := by
    have h1 := primeFormField_conj_eq h hC σ A
    rw [hcomm, mul_inv_cancel_right] at h1
    have h2 : primeFormConjHom h _ (primeFormFieldU h hC σ A * A⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    obtain ⟨u, hu1, hu⟩ := (primeFormConjHom_eq_one_iff h hn hq _).1 h2
    refine ⟨u, hu1, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at hu
    rw [← coe_primeFormFieldU h hC σ A]
    exact eq_mul_of_mul_inv_eq hu
  set a : GL (Fin n) K := (A : GL (Fin n) K) with ha
  have hma : (a : Matrix (Fin n) (Fin n) K).map σ = (u : K) • (a : Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hu
    simp only [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
  have hnorm : ∏ i ∈ Finset.range p, (σ ^ i) (u : K) = 1 :=
    prod_eq_one_of_map_eq_smul (by omega) hσp hma
  obtain ⟨y, hy0, hy⟩ := CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField σ hσ hnorm
  set d : K := (a : Matrix (Fin n) (Fin n) K).det with hd
  have hd0 : d ≠ 0 := primeFormGram_det_ne_zero a
  have hσd : σ d = (u : K) ^ n * d := by
    have e1 : σ (a : Matrix (Fin n) (Fin n) K).det = ((a : Matrix (Fin n) (Fin n) K).map σ).det :=
      RingHom.map_det (σ : K →+* K) _
    rw [hd, e1, hma, Matrix.det_smul, Fintype.card_fin]
  have hfix : σ (y ^ n * d) = y ^ n * d := by
    rw [map_mul, map_pow, hσd]
    calc σ y ^ n * ((u : K) ^ n * d) = ((u : K) * σ y) ^ n * d := by ring
      _ = y ^ n * d := by rw [hy]
  have hpK : p ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq]
    exact hpq.trans (succ_dvd_sq_sub_one hq1)
  obtain ⟨ν, hν⟩ := fixed_unit_isPow hp hp2 σ hσ hpK (y ^ n * d) hfix
    (mul_ne_zero (pow_ne_zero _ hy0) hd0)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero _ hy0) hd0 (by rw [← hν, zero_pow hp.ne_zero])
  obtain ⟨w, hw1, hwA⟩ := (primeFormConjHom_eq_one_iff h hn hq (A ^ p)).1 (by rw [map_pow]; exact hAp)
  have hdw : d ^ p = (w : K) ^ n := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).det) hwA
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow, det_scalar_val] at this
    exact this
  have : IsCyclic Kˣ := inferInstance
  set dU : Kˣ := GeneralLinearGroup.det a with hdU
  have hdUv : (dU : K) = d := rfl
  set yU : Kˣ := Units.mk0 y hy0
  set νU : Kˣ := Units.mk0 ν hν0
  have hνU : νU ^ p = yU ^ n * dU :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val, hdUv]; exact hν)
  have hdwU : dU ^ p = w ^ n :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hdUv]; exact hdw)
  have hq1' : ∀ z : Kˣ, h.norm (z : K) = 1 → z ^ (ℓ ^ f + 1) = 1 := fun z hz =>
    Units.ext (by rw [Units.val_pow_eq_pow_val, ← h.norm_eq_pow, hz, Units.val_one])
  have hdU1 : dU ^ (ℓ ^ f + 1) = 1 := hq1' _ (norm_det_eq_one h 1 A.2)
  have hcardK : Nat.card Kˣ = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    rw [Nat.card_units, h.card_eq_sq]
    zify [Nat.one_le_pow 2 (ℓ ^ f) (by omega), hq1]
    ring
  have hg' : ¬ p ^ 2 ∣ Nat.gcd n (Nat.card Kˣ) := by
    rw [Nat.card_units, h.card_eq_sq]
    exact not_sq_dvd_gcd_sq_sub_one hp hp2 hq1 hpq hg
  have hsq : νU ^ (p ^ 2) = (yU ^ p * w) ^ n := by
    calc νU ^ (p ^ 2) = (νU ^ p) ^ p := by rw [← pow_mul, sq, mul_comm]
      _ = (yU ^ n * dU) ^ p := by rw [hνU]
      _ = yU ^ (n * p) * w ^ n := by rw [mul_pow, ← pow_mul, hdwU]
      _ = (yU ^ p * w) ^ n := by rw [mul_pow, ← pow_mul, mul_comm p n]
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_sq_eq hp hg' hsq
  have hξ : (μ * yU⁻¹) ^ n = dU := by
    rw [mul_pow, hμ, hνU, inv_pow, mul_comm (yU ^ n * dU), inv_mul_cancel_left]
  obtain ⟨c, hc1, hcd⟩ := exists_pow_eq_of_mem_roots (Z := Kˣ) hp hcardK
    (not_dvd_pred_of_dvd_succ hp2 hp hq1 hpq) hg hdU1 ⟨μ * yU⁻¹, hξ⟩
    ⟨w, hq1' w hw1, hdwU.symm⟩
  have hcn : h.norm ((c⁻¹ : Kˣ) : K) = 1 := by
    rw [h.norm_eq_pow, Units.val_inv_eq_inv_val, inv_pow]
    have := congrArg Units.val hc1
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [this, inv_one]
  have hsU : GeneralLinearGroup.scalar (Fin n) c⁻¹ ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    scalar_mem_primeFormUnitary_one h hcn
  set sU : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨_, hsU⟩ * A with hsUdef
  have hρ : primeFormConjHom h _ sU = primeFormConjHom h _ A := by
    have : primeFormConjHom h _ (⟨_, hsU⟩ : primeFormUnitary h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = 1 :=
      (primeFormConjHom_eq_one_iff h hn hq _).2 ⟨c⁻¹, hcn, rfl⟩
    rw [hsUdef, map_mul, this, one_mul]
  have hdetS : ((sU : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [hsUdef, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul]
    change ((GeneralLinearGroup.scalar (Fin n) c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      d = 1
    rw [det_scalar_val, Units.val_inv_eq_inv_val, inv_pow, ← Units.val_pow_eq_pow_val, hcd, hdUv]
    exact inv_mul_cancel₀ hd0
  rw [← hρ, mem_inner_primeFormP]
  exact ⟨⟨(sU : GL (Fin n) K), sU.2, hdetS⟩, rfl⟩


theorem exists_ne_one_of_one_lt_card {G : Type*} [Group G] (H : Subgroup G)
    (h : 1 < Nat.card H) : ∃ x ∈ H, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hcon
  rw [this, Subgroup.card_bot] at h
  exact lt_irrefl _ h

theorem meets_inner_unitary (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hg : ¬ p ^ 2 ∣ Nat.gcd n (ℓ ^ f + 1))
    (D' : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD' : IsElemAbelian p D') (hc : Nat.card D' = p ^ 2) :
    ∃ x ∈ D' ⊓ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), x ≠ 1 := by
  classical
  have : Finite K := h.finite
  have := finite_mulAut_primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, hFsurj, hFker, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set Φ := primeFormFieldFactor h hC hn hq with hΦ
  by_cases hle : D' ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  · have := isCyclic_unitaryD_quotient h hn hq
    exact exists_ne_one_inf_of_cyclic _ _ hp D' hle hD' hc
  · obtain ⟨x, hxD', hxD⟩ := IsConcreteLE.not_le_iff_exists.1 hle
    have hx1 : x ^ p = 1 := hD'.2 x hxD'
    have hxΦ : Φ x ≠ 1 := fun h1 => hxD (hFker ▸ h1)
    have hx0 : x ≠ 1 := fun h1 => hxΦ (by rw [h1, map_one])
    have hσ : orderOf (Φ x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hx1, map_one]) hxΦ
    have hxo : orderOf x = p := orderOf_eq_prime hx1 hx0
    have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic h.prime K h.card).2
    have : IsCyclic (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⧸
        Φ.ker) :=
      isCyclic_of_surjective (QuotientGroup.quotientKerEquivOfSurjective Φ hFsurj).symm.toMonoidHom
        (QuotientGroup.quotientKerEquivOfSurjective Φ hFsurj).symm.surjective
    have h1 := card_le_mul_card_inf_of_cyclic Φ.ker hp D' hD'
    rw [hc] at h1
    have h2 : 1 < Nat.card ↥(D' ⊓ Φ.ker) := by
      have : p * p ≤ p * Nat.card ↥(D' ⊓ Φ.ker) := by simpa [sq] using h1
      exact lt_of_lt_of_le hp.one_lt (Nat.le_of_mul_le_mul_left this hp.pos)
    obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_one_lt_card _ h2
    obtain ⟨descent⟩ : Nonempty (∃ M : primeFormUnitary h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ * x *
            primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M =
          primeFormFieldHom h isPrimeFormGram_one (Φ x)) := by
      obtain ⟨-, -, -, -, -, M⟩ := CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent'
        h hn hq hp hp2 x hxo (Φ x) rfl hσ
      exact ⟨M⟩
    obtain ⟨M, hM⟩ := descent
    set g := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hg0
    have hy' : g⁻¹ * y * g ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← hFker]
      have := (inferInstance : Φ.ker.Normal).conj_mem y hy.2 g⁻¹
      simpa using this
    obtain ⟨A, hA⟩ := hy'
    have hAp : primeFormConjHom h _ A ^ p = 1 := by
      rw [hA]
      have := conj_pow (a := g⁻¹) (b := y) (i := p)
      simp only [inv_inv] at this
      rw [this, hD'.2 y hy.1, mul_one, inv_mul_cancel]
    have hcomm : primeFormFieldHom h isPrimeFormGram_one (Φ x) * primeFormConjHom h _ A =
        primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_one (Φ x) := by
      rw [← hM, hA]
      have hxy : x * y = y * x := by
        have := hD'.1.is_comm.comm (⟨x, hxD'⟩ : D') ⟨y, hy.1⟩
        exact congrArg Subtype.val this
      calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
        _ = g⁻¹ * (y * x) * g := by rw [hxy]
        _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
    have hin := conjHom_mem_inner_of_commute h hn hq hp hp2 hpq hg (Φ x) hσ A hcomm hAp
    rw [hA] at hin
    refine ⟨y, ⟨hy.1, ?_⟩, hy1⟩
    have := (inferInstance : (inner (primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K))).Normal).conj_mem _ hin g
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e]
    exact this

end Unitary

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
