module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67N2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

abbrev Cid (n : ℕ) (K : Type) [Field K] : Matrix (Fin n) (Fin n) K :=
  ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

section Kernel

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem conj_eq_one_iff (hn : 3 ≤ n) (A : primeFormUnitary h (Cid n K)) :
    primeFormConjHom h (Cid n K) A = 1 ↔
      ∃ c : Kˣ, (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  constructor
  · intro hA
    have h1 : primeFormPsi h (isPrimeFormGram_one (n := n)) ⟨A, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, hA]
    obtain ⟨-, c, -, hc⟩ :=
      (primeFormPsi_eq_one_iff h (isPrimeFormGram_one (n := n)) hn ⟨A, 1⟩).1 h1
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk]
    have e : (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g := by
      rw [hc, ← (commute_scalar c (g : GL (Fin n) K)).eq, mul_inv_cancel_right]
    congr 1
    exact Subtype.ext e

theorem pow_succ_eq_one_of_scalar_mem (hn : 0 < n) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (Cid n K)) :
    c ^ (p ^ f + 1) = 1 := by
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0, hn⟩ ⟨0, hn⟩)
    (mem_primeFormUnitary.1 hc)
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply, Units.val_one,
    Matrix.one_apply, Finset.mem_univ, ite_true, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq'] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_succ, ← h.bar_apply, Units.val_one]
  simpa [mul_comm] using h1

theorem scalar_mem_of_pow_succ_eq_one {c : Kˣ} (hc : c ^ (p ^ f + 1) = 1) :
    GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (Cid n K) := by
  rw [mem_primeFormUnitary]
  have h1 : h.bar (c : K) * (c : K) = 1 := by
    rw [h.bar_apply, ← pow_succ]
    simpa using congrArg Units.val hc
  ext i j
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [h1]
  · simp [hij, Ne.symm hij]

end Kernel

section Lift

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_one_of_pow_both {r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ p ^ f + 1) {c : Kˣ}
    (h1 : c ^ r = 1) (h2 : c ^ (p ^ f + 1) = 1) : c = 1 := by
  have hcop : Nat.Coprime r (p ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hr).2 hrq
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))

theorem ker_u (hn : 3 ≤ n) (x : ↥(primeFormUnitary h (Cid n K)))
    (hx : primeFormConjHom h (Cid n K) x = 1) :
    ∃ c : Kˣ, (x : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c ∧
      c ^ (p ^ f + 1) = 1 := by
  obtain ⟨c, hc⟩ := (conj_eq_one_iff h hn x).1 hx
  refine ⟨c, hc, pow_succ_eq_one_of_scalar_mem (n := n) h (by omega) ?_⟩
  rw [← hc]
  exact x.2

theorem lifts_commute_u (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ p ^ f + 1)
    {x y : ↥(primeFormUnitary h (Cid n K))}
    (hxy : primeFormConjHom h (Cid n K) x * primeFormConjHom h (Cid n K) y =
      primeFormConjHom h (Cid n K) y * primeFormConjHom h (Cid n K) x) (hy : y ^ r = 1) :
    x * y = y * x := by
  have h1 : primeFormConjHom h (Cid n K) (x * y * x⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc primeFormConjHom h (Cid n K) x * primeFormConjHom h (Cid n K) y *
          (primeFormConjHom h (Cid n K) x)⁻¹ * (primeFormConjHom h (Cid n K) y)⁻¹
        = (primeFormConjHom h (Cid n K) x * primeFormConjHom h (Cid n K) y) *
          (primeFormConjHom h (Cid n K) y * primeFormConjHom h (Cid n K) x)⁻¹ := by group
      _ = 1 := by rw [hxy]; simp
  obtain ⟨c, hc, hcq⟩ := ker_u h hn _ h1
  have h2 : ((x * y * x⁻¹ : ↥(primeFormUnitary h (Cid n K))) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c * (y : GL (Fin n) K) := by
    have : (x * y * x⁻¹ : ↥(primeFormUnitary h (Cid n K))) = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [this, Subgroup.coe_mul, hc]
  have h3 : (x * y * x⁻¹ : ↥(primeFormUnitary h (Cid n K))) ^ r = 1 := by
    rw [conj_pow, hy]
    group
  have h4 : (GeneralLinearGroup.scalar (Fin n) c * (y : GL (Fin n) K)) ^ r = 1 := by
    rw [← h2, ← Subgroup.coe_pow, h3, Subgroup.coe_one]
  have hyr : (y : GL (Fin n) K) ^ r = 1 := by
    rw [← Subgroup.coe_pow, hy, Subgroup.coe_one]
  rw [((commute_scalar c (y : GL (Fin n) K)).symm).mul_pow, hyr, mul_one, ← map_pow] at h4
  have h5 : c ^ r = 1 := Ln.scalar_eq_one (by omega) h4
  have h6 : c = 1 := eq_one_of_pow_both hr hrq h5 hcq
  have h7 : x * y * x⁻¹ * y⁻¹ = 1 := by
    apply Subtype.ext
    rw [hc, h6, map_one, Subgroup.coe_one]
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h7, one_mul]

end Lift

section LiftGroup

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_lift_group_u (hn : 3 ≤ n) {r : ℕ} [Fact r.Prime] (hrq : ¬ r ∣ p ^ f + 1)
    {V : Subgroup (MulAut (primeFormP h (Cid n K)))} (hVD : V ≤ primeFormD h (Cid n K))
    [hVe : IsElementaryAbelian r ↥V] (hVc : Nat.card ↥V = r ^ 2) :
    ∃ W : Subgroup ↥(primeFormUnitary h (Cid n K)), IsElementaryAbelian r ↥W ∧
      Nat.card ↥W = r ^ 2 ∧ (∀ x ∈ W, primeFormConjHom h (Cid n K) x ∈ V) ∧
      (∀ v ∈ V, ∃ x ∈ W, primeFormConjHom h (Cid n K) x = v) ∧
      (∀ x ∈ W, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) := by
  classical
  have hr : r.Prime := Fact.out
  have hcop : Nat.Coprime r (p ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hr).2 hrq
  have hq1 : 1 < p ^ f + 1 := by
    have : 0 < p ^ f := pow_pos h.prime.pos f
    omega
  have hVpow : ∀ v ∈ V, v ^ r = 1 := fun v hv =>
    elemPow_eq_one_of_isElementaryAbelian (A := V) v hv
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have := hVe.toIsMulCommutative.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ x y : ↥(primeFormUnitary h (Cid n K)),
      primeFormConjHom h (Cid n K) x ∈ V → primeFormConjHom h (Cid n K) y ∈ V → y ^ r = 1 →
        x * y = y * x := fun x y hx hy hyr =>
    lifts_commute_u h hn hr hrq (hVcomm _ hx _ hy) hyr
  let W : Subgroup ↥(primeFormUnitary h (Cid n K)) :=
    { carrier := {x | primeFormConjHom h (Cid n K) x ∈ V ∧ x ^ r = 1}
      one_mem' := ⟨by simp, one_pow r⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by rw [map_mul]; exact V.mul_mem hx.1 hy.1, ?_⟩
        rw [(show Commute x y from hcomm x y hx.1 hy.1 hy.2).mul_pow, hx.2, hy.2, mul_one]
      inv_mem' := fun {x} hx => by
        refine ⟨by rw [map_inv]; exact V.inv_mem hx.1, ?_⟩
        rw [inv_pow, hx.2, inv_one] }
  have hWcomm : ∀ x y : ↥W, x * y = y * x := fun x y =>
    Subtype.ext (hcomm x y x.2.1 y.2.1 y.2.2)
  have hWe : IsElementaryAbelian r ↥W :=
    { toIsMulCommutative := ⟨⟨fun a b => hWcomm a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext x.2.2 }
  let g : ↥W → ↥V := fun x => ⟨primeFormConjHom h (Cid n K) x, x.2.1⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : primeFormConjHom h (Cid n K) ((x : ↥(primeFormUnitary h (Cid n K)))⁻¹ * y) = 1 := by
      have := congrArg Subtype.val hxy
      rw [map_mul, map_inv]
      change primeFormConjHom h (Cid n K) x = primeFormConjHom h (Cid n K) y at this
      rw [this]
      simp
    obtain ⟨c, hc, hcq⟩ := ker_u h hn _ h1
    have hxy' : Commute (x : ↥(primeFormUnitary h (Cid n K))) y := hcomm x y x.2.1 y.2.1 y.2.2
    have h2 : ((x : ↥(primeFormUnitary h (Cid n K)))⁻¹ * y) ^ r = 1 := by
      rw [hxy'.inv_left.mul_pow, inv_pow, x.2.2, y.2.2]
      simp
    have h3 : (GeneralLinearGroup.scalar (Fin n) c) ^ r = 1 := by
      rw [← hc, ← Subgroup.coe_pow, h2, Subgroup.coe_one]
    rw [← map_pow] at h3
    have h4 : c = 1 := eq_one_of_pow_both hr hrq (Ln.scalar_eq_one (by omega) h3) hcq
    rw [h4, map_one] at hc
    apply Subtype.ext
    have h5 : (x : ↥(primeFormUnitary h (Cid n K)))⁻¹ * y = 1 := Subtype.ext hc
    exact inv_mul_eq_one.mp h5
  have hsurj : Function.Surjective g := by
    intro v
    obtain ⟨A, hA⟩ := hVD v.2
    have h1 : primeFormConjHom h (Cid n K) (A ^ r) = 1 := by
      rw [map_pow, hA]
      exact hVpow _ v.2
    obtain ⟨ν, hν, hνq⟩ := ker_u h hn _ h1
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq1
    have hνi : (ν⁻¹) ^ (p ^ f + 1) = 1 := by rw [inv_pow, hνq, inv_one]
    have hμq : ((ν⁻¹) ^ s) ^ (p ^ f + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hνi, one_pow]
    have hμr : ((ν⁻¹) ^ s) ^ r = ν⁻¹ := by
      rw [← pow_mul, mul_comm, pow_eq_pow_mod _ hνi, hs, pow_one]
    let sμ : ↥(primeFormUnitary h (Cid n K)) :=
      ⟨GeneralLinearGroup.scalar (Fin n) ((ν⁻¹) ^ s), scalar_mem_of_pow_succ_eq_one h hμq⟩
    have hsμ : primeFormConjHom h (Cid n K) sμ = 1 :=
      (conj_eq_one_iff h hn sμ).2 ⟨(ν⁻¹) ^ s, rfl⟩
    have hc : Commute sμ A := Subtype.ext ((commute_scalar ((ν⁻¹) ^ s) (A : GL (Fin n) K)).symm.eq)
    have hAr : (A : GL (Fin n) K) ^ r = GeneralLinearGroup.scalar (Fin n) ν := by
      rw [← Subgroup.coe_pow]
      exact hν
    have hx0 : (sμ * A) ^ r = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_mul,
        ((commute_scalar ((ν⁻¹) ^ s) (A : GL (Fin n) K)).symm).mul_pow]
      change (GeneralLinearGroup.scalar (Fin n) ((ν⁻¹) ^ s)) ^ r * (A : GL (Fin n) K) ^ r = _
      rw [hAr, ← map_pow, hμr, ← map_mul, inv_mul_cancel, map_one, Subgroup.coe_one]
    refine ⟨⟨sμ * A, ?_, hx0⟩, Subtype.ext ?_⟩
    · rw [map_mul, hsμ, one_mul, hA]
      exact v.2
    · change primeFormConjHom h (Cid n K) (sμ * A) = v.1
      rw [map_mul, hsμ, one_mul, hA]
  refine ⟨W, hWe, ?_, fun x hx => hx.1, fun v hv => ?_, fun x hx => ?_⟩
  · have := Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)
    rw [this, hVc]
  · obtain ⟨⟨x, hx⟩, hxv⟩ := hsurj ⟨v, hv⟩
    exact ⟨x, hx, congrArg Subtype.val hxv⟩
  · set M : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
    have hd1 : M.det ^ r = 1 := by
      have h1 : ((x : GL (Fin n) K)) ^ r = 1 := by
        rw [← Subgroup.coe_pow, hx.2, Subgroup.coe_one]
      have h2 := congrArg (fun U : GL (Fin n) K => (U : Matrix (Fin n) (Fin n) K).det) h1
      simpa [Units.val_pow_eq_pow_val, Matrix.det_pow] using h2
    have hd2 : M.det ^ (p ^ f + 1) = 1 := by
      have h3 : (M.map h.bar)ᵀ * (1 : Matrix (Fin n) (Fin n) K) * M = 1 :=
        mem_primeFormUnitary.1 x.2
      have h4 := congrArg Matrix.det h3
      have hb : (M.map h.bar).det = h.bar M.det := (RingHom.map_det h.bar M).symm
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, mul_one, hb] at h4
      rw [pow_succ, ← h.bar_apply]
      simpa [mul_comm] using h4
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hd1)
        (orderOf_dvd_of_pow_eq_one hd2))

end LiftGroup

section Cyclic

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem primeFormUnitary_eq_statedGU :
    primeFormUnitary h (Cid n K) = CFSG.Quasithin.StatedGU n (p ^ f) K := by
  have hbar : (⇑h.bar : K → K) = fun x => x ^ p ^ f := funext fun x => h.bar_apply x
  apply le_antisymm
  · intro A hA
    apply Subgroup.subset_closure
    simpa [hbar] using mem_primeFormUnitary.1 hA
  · unfold CFSG.Quasithin.StatedGU
    rw [Subgroup.closure_le]
    intro A hA
    rw [SetLike.mem_coe, mem_primeFormUnitary]
    simpa [hbar] using hA

theorem false_of_u_cyclic (hn : n = 4 ∨ n = 5) {r : ℕ} (hrp : r ≠ p)
    (hrq : ¬ r ∣ (p ^ f) ^ 2 - 1)
    {V Z : Subgroup (MulAut (primeFormP h (Cid n K)))} (hVD : V ≤ primeFormD h (Cid n K))
    (h2 : N2Cfg (primeFormP h (Cid n K)) r V Z) : False := by
  classical
  obtain ⟨hr, hr2, hVe, hVc, -⟩ := h2
  have : Fact r.Prime := ⟨hr⟩
  have : IsElementaryAbelian r ↥V := hVe
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hn3 : 3 ≤ n := by omega
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hfac : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    simpa using Nat.sq_sub_sq (p ^ f) 1
  have hrq1 : ¬ r ∣ p ^ f + 1 := fun hd => hrq (hfac ▸ hd.mul_right _)
  obtain ⟨W, hWe, hWc, -, -, -⟩ := exists_lift_group_u h hn3 hrq1 hVD hVc
  have hpq : ¬ r ∣ p ^ f := fun hd => hrp ((Nat.prime_dvd_prime_iff_eq hr h.prime).1
    (hr.dvd_of_dvd_pow hd))
  have hcard : Fintype.card K = (p ^ f) ^ 2 := by
    rw [Fintype.card_eq_nat_card, h.card, ← pow_mul, mul_comm, pow_mul]
  have hne : (-((p ^ f : ℕ) : ZMod r)) ^ 2 ≠ 1 := by
    intro h1
    apply hrq
    have h3 : (((p ^ f) ^ 2 : ℕ) : ZMod r) = 1 := by
      push_cast
      simpa [neg_sq] using h1
    have h4 : (((p ^ f) ^ 2 - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by positivity)), h3]
      simp
    exact (ZMod.natCast_eq_zero_iff _ _).mp h4
  have he3 : 3 ≤ orderOf (-((p ^ f : ℕ) : ZMod r)) := by
    have hq0 : ((p ^ f : ℕ) : ZMod r) ≠ 0 := fun h0 => hpq ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have hpos : 0 < orderOf (-((p ^ f : ℕ) : ZMod r)) :=
      orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
        ⟨r - 1, by have := hr.two_le; omega, ZMod.pow_card_sub_one_eq_one (neg_ne_zero.2 hq0)⟩)
    by_contra hlt
    push Not at hlt
    have hd : orderOf (-((p ^ f : ℕ) : ZMod r)) ∣ 2 := by
      interval_cases (orderOf (-((p ^ f : ℕ) : ZMod r))) <;> simp
    exact hne (orderOf_dvd_iff_pow_eq_one.1 hd)
  have hdiv : n / orderOf (-((p ^ f : ℕ) : ZMod r)) ≤ 1 := by
    have : n < 2 * orderOf (-((p ^ f : ℕ) : ZMod r)) := by omega
    have := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega : n < 2 * orderOf (-((p ^ f : ℕ) : ZMod r)))
    omega
  let e : ↥(primeFormUnitary h (Cid n K)) ≃* ↥(CFSG.Quasithin.StatedGU n (p ^ f) K) :=
    MulEquiv.subgroupCongr (primeFormUnitary_eq_statedGU h)
  let W' : Subgroup ↥(CFSG.Quasithin.StatedGU n (p ^ f) K) := W.map e.toMonoidHom
  let e' : ↥W ≃* ↥W' := Subgroup.equivMapOfInjective W e.toMonoidHom e.injective
  have hW'c : Nat.card ↥W' = r ^ 2 := by rw [Nat.card_congr e'.toEquiv.symm, hWc]
  have hW'p : IsPGroup r ↥W' := IsPGroup.of_card hW'c
  obtain ⟨P, hP⟩ := hW'p.exists_le_sylow
  obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.sylow_GU hr2 K hcard hpq (by omega) P
  have hcyc : IsCyclic ↥P := (MulEquiv.isCyclic φ).mpr
    (OddAut.isCyclic_sigmaModel_of_div_le_one hr.one_lt hdiv)
  have hW'cyc : IsCyclic ↥W' := isCyclic_of_injective (Subgroup.inclusion hP)
    (Subgroup.inclusion_injective hP)
  have hWcyc : IsCyclic ↥W := (MulEquiv.isCyclic e').mpr hW'cyc
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hWc hWcyc

end Cyclic

end CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC
