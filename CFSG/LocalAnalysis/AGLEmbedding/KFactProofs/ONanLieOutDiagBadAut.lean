module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadEigen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadTorus
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.AGLEmbedding.LieOut

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

theorem exists_unitary_of_outer {n : ℕ} (h : UnitaryFieldData 2 2 K) (hn : 3 ≤ n)
    (α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hα : α ^ 5 = 1)
    (hnin : α ∉ innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∃ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A = α := by
  have hq : ¬(n = 3 ∧ 2 ^ 2 = 2) := fun ⟨_, h2⟩ => by omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  have hαD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← ker_primeFormFieldFactor h hC1 hn hq, MonoidHom.mem_ker]
    by_contra hσ1
    have hσp : (primeFormFieldFactor h hC1 hn hq α) ^ 5 = 1 := by
      rw [← map_pow, hα, map_one]
    have hσord : orderOf (primeFormFieldFactor h hC1 hn hq α) = 5 := orderOf_eq_prime hσp hσ1
    have hαord : orderOf α = 5 :=
      orderOf_eq_prime hα (fun h1 => hnin (h1 ▸ one_mem _))
    obtain ⟨hpf, -⟩ := CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn
      hq (p := 5) (by norm_num) (by norm_num) (by norm_num) α hαord _ rfl hσord
    omega
  exact hαD

theorem eq_one_of_pow_eq_one_of_coprime (h : UnitaryFieldData 2 2 K) {x : K} (hx : x ≠ 0) {r : ℕ}
    (hr : Nat.Coprime r 15) (hxr : x ^ r = 1) : x = 1 := by
  have := h.finite
  have := Fintype.ofFinite K
  have h15 : x ^ 15 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [Fintype.card_eq_nat_card, h.card] at this
  have h1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hr (orderOf_dvd_of_pow_eq_one hxr) (orderOf_dvd_of_pow_eq_one h15)
  exact orderOf_eq_one_iff.1 h1

theorem exists_fixed_of_commuting {n : ℕ} (hn : 0 < n) (h : UnitaryFieldData 2 2 K)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) {r : ℕ}
    (hr : r.Prime) (hr15 : Nat.Coprime r 15) (u : Matrix (Fin n) (Fin n) K)
    (hu : adj h.bar u * u = 1) (hAu : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * u =
      u * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hur : u ^ r = 1) (hu1 : u ≠ 1) :
    ∃ y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A y = y ∧
        orderOf y = r := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hu' : u * adj h.bar u = 1 := mul_eq_one_comm.1 hu
  let uGL : GL (Fin n) K := ⟨u, adj h.bar u, hu', hu⟩
  have hdet0 : u.det ≠ 0 := by
    have := congrArg det hu
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have hdet : u.det = 1 := by
    refine eq_one_of_pow_eq_one_of_coprime h hdet0 hr15 ?_
    rw [← det_pow, hur, det_one]
  have hmem : uGL ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine ⟨?_, hdet⟩
    show (u.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * u = _
    rw [Units.val_one, Matrix.mul_one]
    exact hu
  let g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨uGL, hmem⟩
  have hgr : g ^ r = 1 := by
    apply Subtype.ext
    apply Units.ext
    show ((uGL ^ r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_pow_eq_pow_val]
    exact hur
  refine ⟨(g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ?_, ?_⟩
  · rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    show (A : GL (Fin n) K) * uGL * (A : GL (Fin n) K)⁻¹ = uGL
    have : (A : GL (Fin n) K) * uGL = uGL * (A : GL (Fin n) K) := Units.ext hAu
    rw [this, mul_inv_cancel_right]
  · have hy : (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ r = 1 := by
      rw [← QuotientGroup.mk_pow, hgr]
      rfl
    have hy1 : (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 1 := by
      intro h1
      obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff g).1 h1
      apply hu1
      have hc' : u = Matrix.scalar (Fin n) (c : K) := by
        have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
        rwa [Matrix.GeneralLinearGroup.coe_scalar] at this
      have hcr : (c : K) ^ r = 1 := by
        have h2 : Matrix.scalar (Fin n) ((c : K) ^ r) = Matrix.scalar (Fin n) (1 : K) := by
          rw [map_pow, ← hc', hur, map_one]
        exact Matrix.scalar_inj.1 h2
      have hc1 : (c : K) = 1 := eq_one_of_pow_eq_one_of_coprime h c.ne_zero hr15 hcr
      rw [hc', hc1, map_one]
    exact orderOf_eq_prime hy hy1

theorem conjHom_mem_innerAut {n : ℕ} (h : UnitaryFieldData 2 2 K)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A ∈
      innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hA : (A : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (mem_gramSU_iff_unitary h).2 ⟨A.2, hdet⟩
  refine ⟨((⟨(A : GL (Fin n) K), hA⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ?_⟩
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g' => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem exists_fixed_prime_order {n : ℕ} (h : UnitaryFieldData 2 2 K) (hn : 10 ≤ n)
    (α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hα : α ^ 5 = 1)
    (hnin : α ∉ innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∃ y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), α y = y ∧
      (orderOf y = 13 ∨ orderOf y = 41) := by
  obtain ⟨A, rfl⟩ := exists_unitary_of_outer h (by omega) α hα hnin
  have hA5 : A ^ 5 ∈ idScalarKernel h n := by
    rw [← primeFormConjHom_eq_one_iff (h := h) (n := n) (by omega) (by norm_num), map_pow]
    exact hα
  obtain ⟨c, hc, hAc⟩ := hA5
  set M : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hAu : adj h.bar M * M = 1 := by
    have h0 : (M.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M =
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := mem_primeFormUnitary.1 A.2
    simpa [adj, Units.val_one, Matrix.mul_one] using h0
  have hM5 : M ^ 5 = Matrix.scalar (Fin n) (c : K) := by
    have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hAc
    simpa [hM, Matrix.GeneralLinearGroup.coe_scalar] using this
  have hdet : M.det ≠ 1 := fun hd => hnin (conjHom_mem_innerAut h A hd)
  have hc5 : (c : K) ^ 5 = 1 := by
    have : (c : K) ^ (2 ^ 2 + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    simpa using this
  by_cases hc1 : (c : K) = 1
  · have hM5' : M ^ 5 = 1 := by rw [hM5, hc1, map_one]
    obtain ⟨u, hu, hcomm, hu13, hu1⟩ := exists_order_thirteen h hn M hAu hM5' hdet
    obtain ⟨y, hy, hord⟩ := exists_fixed_of_commuting (by omega) h A (r := 13) (by norm_num)
      (by norm_num) u hu hcomm hu13 hu1
    exact ⟨y, hy, Or.inl hord⟩
  · have hM5' : M ^ 5 = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [hM5, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
      simp
    obtain ⟨u, hu, hcomm, hu41, hu1⟩ := exists_order_fortyone h (by omega) M hAu hc5 hc1 hM5'
    obtain ⟨y, hy, hord⟩ := exists_fixed_of_commuting (by omega) h A (r := 41) (by norm_num)
      (by norm_num) u hu hcomm hu41 hu1
    exact ⟨y, hy, Or.inr hord⟩

end CFSG.AGLEmbedding.LieOut
