module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPL
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace OrdPU

variable {r f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem scalar_mem_uU (h : UnitaryFieldData r f K) {y : Kˣ} (hy : h.norm (y : K) = 1) :
    GeneralLinearGroup.scalar (Fin n) y ∈ uU h n := by
  rw [UnitaryHigher.mem_primeFormUnitary, GeneralLinearGroup.coe_scalar,
    scalar_barTranspose_mul_mul, hy, one_smul]

theorem norm_zpow (h : UnitaryFieldData r f K) (y : Kˣ) (k : ℤ) :
    h.norm ((y ^ k : Kˣ) : K) = h.norm (y : K) ^ k := by
  rw [UnitaryFieldData.norm, Units.val_zpow_eq_zpow_val, map_zpow₀, ← mul_zpow,
    UnitaryFieldData.norm]

theorem norm_det_of_mem_uU (h : UnitaryFieldData r f K) {A : GL (Fin n) K} (hA : A ∈ uU h n) :
    h.norm ((GeneralLinearGroup.det A : Kˣ) : K) = 1 := by
  have e := congrArg Matrix.det ((mem_uU h).1 hA)
  have hb : ((A : Matrix (Fin n) (Fin n) K).map h.bar).det =
      h.bar (A : Matrix (Fin n) (Fin n) K).det := by
    rw [RingHom.map_det]; rfl
  rw [Matrix.det_mul, Matrix.det_transpose, hb, Matrix.det_one] at e
  rw [GeneralLinearGroup.val_det_apply, UnitaryFieldData.norm, mul_comm]
  exact e

theorem uConjAut_mem_range_conj_of_det (h : UnitaryFieldData r f K) (hn : 3 ≤ n) (A : uU h n)
    {y : Kˣ} (hy : h.norm (y : K) = 1)
    (hdet : GeneralLinearGroup.det (A : GL (Fin n) K) = y ^ n) :
    uConjAut h (by omega) A ∈
      (MulAut.conj : StatedProj (StatedSU n (r ^ f) K) →*
        MulAut (StatedProj (StatedSU n (r ^ f) K))).range := by
  have hn1 : 1 ≤ n := by omega
  have hyinv : h.norm ((y⁻¹ : Kˣ) : K) = 1 := by
    rw [← _root_.zpow_neg_one, norm_zpow, hy, _root_.one_zpow]
  set S : uU h n := ⟨_, scalar_mem_uU h hyinv⟩ with hS
  set B : uU h n := S * A with hB
  have hBdet : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [hB, Subgroup.coe_mul, ← GeneralLinearGroup.val_det_apply, map_mul, hdet, hS]
    change ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) y⁻¹) * y ^ n : Kˣ) : K) = 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, inv_mul_cancel, Units.val_one]
  have hBSU : (B : GL (Fin n) K) ∈ StatedSU n (r ^ f) K := by
    rw [statedSU_eq_gramSU h, mem_gramSU, Units.val_one, Matrix.mul_one]
    exact ⟨(mem_uU h).1 B.2, hBdet⟩
  have hS1 : uConjAut h hn1 S = 1 := (uConjAut_eq_one_iff h hn S).2 ⟨y⁻¹, rfl⟩
  have hAB : A = S⁻¹ * B := by rw [hB, inv_mul_cancel_left]
  refine ⟨projH _ ⟨_, hBSU⟩, ?_⟩
  have hcB : uConjAut h hn1 B = MulAut.conj (projH _ ⟨_, hBSU⟩) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    change uConjAut h hn1 B (projH _ g) = _
    rw [uConjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [hAB, map_mul, map_inv, hS1, inv_one, one_mul, hcB]

theorem uConjAut_inner_of_coprime (h : UnitaryFieldData r f K) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (A : uU h n) (hA : uConjAut h (by omega) A ^ p = 1) :
    uConjAut h (by omega) A ∈
      (MulAut.conj : StatedProj (StatedSU n (r ^ f) K) →*
        MulAut (StatedProj (StatedSU n (r ^ f) K))).range := by
  have hn1 : 1 ≤ n := by omega
  have h1 : uConjAut h hn1 (A ^ p) = 1 := by rw [map_pow, hA]
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn (A ^ p)).1 h1
  have hcN : h.norm (c : K) = 1 := by
    have hmem : GeneralLinearGroup.scalar (Fin n) c ∈ uU h n := by
      rw [← hc]
      exact (A ^ p).2
    have hU := (mem_uU h).1 hmem
    rw [GeneralLinearGroup.coe_scalar] at hU
    have e := scalar_barTranspose_mul_mul h (1 : Matrix (Fin n) (Fin n) K) (c : K)
    rw [Matrix.mul_one, hU] at e
    have e00 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e00
    exact e00.symm
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin n) K) with hd
  have hdN : h.norm (d : K) = 1 := norm_det_of_mem_uU h A.2
  have hdet : d ^ p = c ^ n := by
    rw [hd, ← map_pow, ← Subgroup.coe_pow, hc, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  set u : ℤ := Nat.gcdA p n
  set v : ℤ := Nat.gcdB p n
  have huv : (p : ℤ) * u + (n : ℤ) * v = 1 := by
    have := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one, Nat.cast_one] at this
    exact this.symm
  refine uConjAut_mem_range_conj_of_det h hn A (y := c ^ u * d ^ v) ?_ ?_
  · have e1 : h.norm ((c ^ u * d ^ v : Kˣ) : K) =
        h.norm ((c ^ u : Kˣ) : K) * h.norm ((d ^ v : Kˣ) : K) := by
      rw [Units.val_mul, UnitaryFieldData.norm, UnitaryFieldData.norm, UnitaryFieldData.norm,
        map_mul]
      ring
    rw [e1, norm_zpow, norm_zpow, hcN, hdN, _root_.one_zpow, _root_.one_zpow, one_mul]
  · have e1 : d = d ^ ((p : ℤ) * u + (n : ℤ) * v) := by rw [huv, zpow_one]
    have e2 : (c ^ u * d ^ v) ^ n = d ^ ((p : ℤ) * u + (n : ℤ) * v) := by
      have hc' : c ^ ((n : ℤ) * u) = d ^ ((p : ℤ) * u) := by
        rw [_root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hdet]
      rw [mul_pow, ← zpow_natCast (c ^ u), ← zpow_natCast (d ^ v), ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm u, hc', mul_comm v, ← _root_.zpow_add]
    rw [e2, ← e1]

theorem ordP_psu (h : UnitaryFieldData r f K) (hr2 : r ≠ 2) (hn : n = 3 ∨ n = 4) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (α : MulAut (StatedProj (StatedSU n (r ^ f) K)))
    (hα : orderOf α = p) : OrdPConcl r (StatedProj (StatedSU n (r ^ f) K)) α := by
  have : CharP K r := h.charP
  have : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hq : ¬(n = 3 ∧ r ^ f = 2) := by
    rintro ⟨-, h2⟩
    have hodd : Odd (r ^ f) := (h.prime.odd_of_ne_two hr2).pow
    rw [h2] at hodd
    exact (Nat.not_odd_iff_even.2 (by decide)) hodd
  have hαp : α ^ p = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq α
  have hφp : φ ^ p = 1 := fieldAut_pow_eq_one h hn3 hq (hαeq ▸ hαp)
  by_cases hφ : φ = 1
  · right
    rw [hφ, map_one, mul_one] at hαeq
    subst hαeq
    refine uConjAut_inner_of_coprime h hn3 hp ?_ A hαp
    intro hpn
    have := Nat.le_of_dvd (by omega) hpn
    omega
  · left
    have hφord : orderOf φ = p := orderOf_eq_prime hφp hφ
    let a' : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      MulAut.congr (uTransport h hn1) α
    have ha' : orderOf a' = p :=
      (MulEquiv.orderOf_eq (MulAut.congr (uTransport h hn1)) α).trans hα
    have hσa : primeFormFieldFactor h isPrimeFormGram_one hn3 hq a' = φ := by
      have := uFactor_apply h hn3 hq A φ
      rw [← hαeq] at this
      exact this
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      unitary_prime_descent_char h hn3 hq hp (by omega) a' ha' φ hσa hφord
    have hαh : α = uConjAut h hn1 M * uFieldAut h hn1 φ * (uConjAut h hn1 M)⁻¹ := by
      have h1 : a' = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M *
          primeFormFieldHom h isPrimeFormGram_one φ *
          (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ := by
        rw [← hM]
        group
      have h2 : α = (MulAut.congr (uTransport h hn1)).symm a' :=
        ((MulAut.congr (uTransport h hn1)).symm_apply_apply α).symm
      rw [h2, h1, map_mul, map_mul, map_inv]
      rfl
    rw [hαh]
    exact StepH3U.exists_rgroup_of_field_u h hn3 hn1 M φ

end OrdPU

theorem ordPInner_fu3d : OrdPInner FU3d := by
  intro r p Y _ _ hr hr2 hp hp5 _ hY b hb
  obtain ⟨f, hf, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSU 3 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have h : UnitaryFieldData r f K := ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  change OrdPConcl r Y b
  apply OrdPConcl.of_mulEquiv e
  exact OrdPU.ordP_psu h hr2 (Or.inl rfl) hp hp5 _
    ((MulEquiv.orderOf_eq (MulAut.congr e) b).trans hb)

theorem ordPInner_fu4d : OrdPInner FU4d := by
  intro r p Y _ _ hr hr2 hp hp5 _ hY b hb
  obtain ⟨f, hf, -, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSU 4 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have h : UnitaryFieldData r f K := ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  change OrdPConcl r Y b
  apply OrdPConcl.of_mulEquiv e
  exact OrdPU.ordP_psu h hr2 (Or.inr rfl) hp hp5 _
    ((MulEquiv.orderOf_eq (MulAut.congr e) b).trans hb)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
