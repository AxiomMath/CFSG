module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMat

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem eq_of_orderOf_two {G : Type*} [Group G] [IsCyclic G] [Finite G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  haveI := Fintype.ofFinite G
  have hd : 2 ∣ Fintype.card G := by
    rw [← ha, ← Nat.card_eq_fintype_card]
    exact orderOf_dvd_natCard a
  have hcard := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at hcard
  have hmem : ∀ c : G, orderOf c = 2 → c ∈ Finset.univ.filter (fun c : G => orderOf c = 2) :=
    fun c hc => Finset.mem_filter.2 ⟨Finset.mem_univ c, hc⟩
  exact Finset.card_le_one.1 hcard.le a (hmem a ha) b (hmem b hb)

@[expose] noncomputable def barAut {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K) :
    K ≃+* K :=
  RingEquiv.ofRingHom h.bar h.bar (RingHom.ext h.bar_bar) (RingHom.ext h.bar_bar)

theorem barAut_apply {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K) (c : K) :
    barAut h c = h.bar c := rfl

theorem orderOf_barAut {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K) :
    orderOf (barAut h) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · refine RingEquiv.ext fun c => ?_
    change barAut h (barAut h c) = c
    rw [barAut_apply, barAut_apply, h.bar_bar]
  · intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    have := RingEquiv.congr_fun h1 c
    rw [barAut_apply] at this
    exact this

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K) {n : ℕ}

theorem two_elt_mem_inner (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ r ^ f = 2)) (hodd : Odd n)
    {α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hα : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) {k : ℕ}
    (hk : α ^ (2 ^ k) = 1) :
    α ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  set I := inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) with hI
  set c : D ⧸ I.subgroupOf D := QuotientGroup.mk ⟨α, hα⟩ with hc
  have hc2 : c ^ (2 ^ k) = 1 := by
    rw [hc, ← QuotientGroup.mk_pow]
    have : (⟨α, hα⟩ : D) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have hodd' : Odd (Nat.gcd n (r ^ f + 1)) := hodd.of_dvd_nat (Nat.gcd_dvd_left _ _)
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
  have h2 : orderOf c ∣ Nat.gcd n (r ^ f + 1) := by
    rw [← hcard]
    exact orderOf_dvd_natCard c
  have hcop : Nat.Coprime (2 ^ k) (Nat.gcd n (r ^ f + 1)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd')
  have h3 : orderOf c ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  have h4 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have h5 : (⟨α, hα⟩ : D) ∈ I.subgroupOf D := (QuotientGroup.eq_one_iff _).1 h4
  exact Subgroup.mem_subgroupOf.1 h5

theorem mem_primeFormD_of_commute (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ r ^ f = 2)) (hodd : Odd n)
    {y : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hdet : ∀ b : K, b ^ n ≠ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det)
    {α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} {k : ℕ}
    (hk : α ^ (2 ^ k) = 1)
    (hc : α * primeFormConjHom h _ y = primeFormConjHom h _ y * α) :
    α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  classical
  haveI := h.finite
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set F := primeFormFieldFactor h hC1 hn hq with hF
  by_contra hα
  have hφ1 : F α ≠ 1 := by
    intro h1
    apply hα
    have : α ∈ F.ker := h1
    rwa [hF, ker_primeFormFieldFactor] at this
  have hφk : (F α) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hex : ∃ j, (F α) ^ (2 ^ (j + 1)) = 1 :=
    ⟨k, by rw [pow_succ, pow_mul, hφk, one_pow]⟩
  have hj : (F α) ^ (2 ^ (Nat.find hex + 1)) = 1 := Nat.find_spec hex
  have hjne : (F α) ^ (2 ^ (Nat.find hex)) ≠ 1 := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      simpa using hφ1
    · intro h1
      exact Nat.find_min hex (Nat.sub_lt hpos one_pos) (by
        have h2 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rw [h2]
        exact h1)
  set j := Nat.find hex with hjdef
  set α' := α ^ (2 ^ j) with hα'
  set ψ : K ≃+* K := F α' with hψ
  have hψeq : ψ = (F α) ^ (2 ^ j) := by rw [hψ, hα', map_pow]
  have hψ2 : ψ ^ 2 = 1 := by
    rw [hψeq, ← pow_mul, ← pow_succ]
    exact hj
  have hψ1 : ψ ≠ 1 := by rw [hψeq]; exact hjne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψord : orderOf ψ = 2 := orderOf_eq_prime hψ2 hψ1
  obtain ⟨hcardAut, hcyc⟩ := card_ringAut_and_isCyclic h.prime K (n := 2 * f) h.card
  haveI : IsCyclic (K ≃+* K) := hcyc
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; have := h.one_le; omega)
  have hψbar : ψ = barAut h := eq_of_orderOf_two hψord (orderOf_barAut h)
  obtain ⟨φ0, ⟨B, hB⟩, -⟩ := existsUnique_primeFormFieldFactor h hC1 hn hq α'
  have hφ0 : φ0 = ψ := by
    have := primeFormFieldFactor_apply h hC1 hn hq B φ0
    rw [← hB] at this
    exact this.symm
  rw [hφ0] at hB
  have hc' : α' * primeFormConjHom h _ y = primeFormConjHom h _ y * α' :=
    (Commute.pow_left hc (2 ^ j)).eq
  rw [hB] at hc'
  have hconj : primeFormFieldHom h hC1 ψ * primeFormConjHom h _ y *
      (primeFormFieldHom h hC1 ψ)⁻¹ = primeFormConjHom h _ (B⁻¹ * y * B) := by
    rw [map_mul, map_mul, map_inv]
    calc _ = (primeFormConjHom h _ B)⁻¹ * (primeFormConjHom h _ B *
        primeFormFieldHom h hC1 ψ * primeFormConjHom h _ y) * (primeFormFieldHom h hC1 ψ)⁻¹ := by
          group
      _ = (primeFormConjHom h _ B)⁻¹ * (primeFormConjHom h _ y *
        (primeFormConjHom h _ B * primeFormFieldHom h hC1 ψ)) * (primeFormFieldHom h hC1 ψ)⁻¹ := by
          rw [hc']
      _ = _ := by group
  rw [primeFormField_conj_eq h hC1 ψ y] at hconj
  set w : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (B⁻¹ * y * B)⁻¹ * primeFormFieldU h hC1 ψ y with hw
  have hw1 : primeFormPsi h hC1 ⟨w, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one, hw, map_mul, map_inv, ← hconj, inv_mul_cancel]
  obtain ⟨-, c, -, hcw⟩ := (primeFormPsi_eq_one_iff h hC1 hn ⟨w, 1⟩).1 hw1
  change (w : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c at hcw
  have hψy : glAut ψ (y : GL (Fin n) K) =
      (B⁻¹ * y * B : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
    have h1 : ((B⁻¹ * y * B : primeFormUnitary h _) : GL (Fin n) K) *
        (w : GL (Fin n) K) = glAut ψ (y : GL (Fin n) K) := by
      rw [hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU]
      group
    rw [← h1, hcw]
    rfl
  set d := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det with hd
  have hd0 : d ≠ 0 := fun h0 => hdet 0 (by
    rw [h0]
    exact zero_pow (by omega))
  have hdet1 : ψ d = d * (c : K) ^ n := by
    have e1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K).det) hψy
    simp only [coe_glAut] at e1
    have e2 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map ψ =
        (ψ : K →+* K).mapMatrix ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
    rw [e2, ← RingHom.map_det] at e1
    rw [Units.val_mul, Matrix.det_mul, det_scalar_eq] at e1
    have := det_conj_eq (y : GL (Fin n) K) B
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1
    rw [this] at e1
    exact e1
  have hnorm : h.norm d = 1 := norm_det_eq_one h 1 y.2
  have hbar : ψ d = d⁻¹ := by
    rw [hψbar, barAut_apply]
    have : d * h.bar d = 1 := hnorm
    exact eq_inv_of_mul_eq_one_right this
  rw [hbar] at hdet1
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  obtain ⟨m, hm⟩ := hodd
  apply hdet (d * (c : K) ^ m)
  have hd2 : d ^ 2 * (c : K) ^ n = 1 := by
    have : d⁻¹ = d * (c : K) ^ n := hdet1
    field_simp at this
    linear_combination -this
  rw [mul_pow, ← pow_mul, hm]
  have h2 : d ^ (2 * m + 1) = d * (d ^ 2) ^ m := by rw [← pow_mul, pow_succ, mul_comm]
  have h3 : (c : K) ^ (m * (2 * m + 1)) = ((c : K) ^ n) ^ m := by rw [← pow_mul, hm, mul_comm]
  rw [h2, h3]
  have h4 : (d ^ 2) ^ m * ((c : K) ^ n) ^ m = 1 := by
    rw [← mul_pow, hd2, one_pow]
  calc d * (d ^ 2) ^ m * ((c : K) ^ n) ^ m = d * ((d ^ 2) ^ m * ((c : K) ^ n) ^ m) := by ring
    _ = d := by rw [h4, mul_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
