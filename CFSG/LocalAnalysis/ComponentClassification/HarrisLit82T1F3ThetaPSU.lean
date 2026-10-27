module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaPSL
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.ComponentClassification.TBLit

theorem pow_eq_one_of_transfer {X T : Type} [Group X] [Finite X] [Group T]
    {ψ' : X →* MulAut T} (hinj' : Function.Injective ψ') {t : X} {k : ℕ}
    (hA : ∀ y' ∈ oddCoreIn ψ'.range (ψ' t), y' ^ k = 1) {y : X}
    (hy : y ∈ oddCentralizerCore t) : y ^ k = 1 := by
  apply hinj'
  rw [map_pow, map_one]
  refine hA _ ?_
  rw [← map_oddCentralizerCore_of_injective hinj']
  exact ⟨y, hy, rfl⟩

end CFSG.ComponentClassification.Burgoyne

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat conj_embedding eq_bot_of_oddCoreIn
  conj_injective_of_mulEquiv)
open CFSG.Blueprint

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem usplit_pow_card_sub_one (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J)
    {y : MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hy : y ∈ oddCoreIn B (uConjAut h (by omega) (uSign h J))) : y ^ (Nat.card K - 1) = 1 := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨α, β, hα, hβ, rfl⟩ := split_oddCoreIn h hp2 hn hinj hB ha hb hy
  have hD : uDiagJ h J α β hα hβ ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_uDiagJ, diagonal_pow, Subgroup.coe_one,
      Units.val_one, ← diagonal_one]
    congr 1
    funext i
    rw [Pi.pow_apply, Nat.card_eq_fintype_card]
    split_ifs
    · exact FiniteField.pow_card_sub_one_eq_one _ α.ne_zero
    · exact FiniteField.pow_card_sub_one_eq_one _ β.ne_zero
  rw [← map_pow, hD, map_one]

omit [Field K] in
theorem prPhi_smul_pow {L : Type} [Field L] (h2 : (2 : L) ≠ 0) {m : ℕ} {l : L} (hl : l ≠ 0)
    (a b : L) (k : ℕ) :
    prPhi m l (a • 1) (b • 1) ^ k = prPhi m l ((a ^ k) • 1) ((b ^ k) • 1) := by
  induction k with
  | zero => simp [prPhi_one h2 hl]
  | succ k ih =>
    rw [pow_succ, ih, prPhi_mul h2 hl, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      smul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, pow_succ, pow_succ]

theorem upaired_pow_card_sub_one (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))).range ≤ B)
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {y : MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))}
    (hy : y ∈ oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN))) :
    y ^ (Nat.card K - 1) = 1 := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, b, D, hab, hD, rfl⟩ := paired_oddCoreIn h hp2 h2 hm hinj hB hl hN hy
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hab
    exact zero_ne_one hab
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact zero_ne_one hab
  have hDk : D ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, prPhi_smul_pow h2 hl,
      Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one _ ha0,
      FiniteField.pow_card_sub_one_eq_one _ hb0, one_smul, prPhi_one h2 hl, Subgroup.coe_one,
      Units.val_one]
  rw [← map_pow, hDk, map_one]

include h in
theorem two_ne_zero_of_unitary (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

theorem innerSplit_pow_eq_one (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} {A : uU h n} (htA : ψ t = uConjAut h (by omega) A) {l : K} (hl0 : l ≠ 0)
    (hlN : h.norm l = 1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1)
    (hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c)
    {y : X} (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K - 1) = 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_unitary h hp2
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = 1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form h h2 hU' hA'2
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M *
      ((HG : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J := by
    rw [hHi, coe_uGL]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul]
  have hHH : Hm * (Hm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
  have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
      by_cases hne : J.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hcon a ha i]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨1, one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hne]
    have e : l⁻¹ • M = s • 1 := by
      calc l⁻¹ • M = (l⁻¹ • M) * (Hm * (Hm.map h.bar)ᵀ) := by rw [hHH, Matrix.mul_one]
        _ = (Hm * signMat K J) * (Hm.map h.bar)ᵀ := by rw [← Matrix.mul_assoc, hHA]
        _ = s • 1 := by
            rw [hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
    apply hns (Units.mk0 (l * s) (mul_ne_zero hl0 hs))
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    change M = _
    have e2 : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e2, e, smul_smul, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨a, ha, b, hb⟩ := hJ
  obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer h hn hψ hInn htA ⟨HG, uGL_mem h _ _⟩
    hl0 (A' := uSign h J) (by rw [coe_uSign]; exact hconj)
  refine pow_eq_one_of_transfer hinj' (fun y' hy' => ?_) hy
  rw [hψ't] at hy'
  exact usplit_pow_card_sub_one h hp2 hn hinj hInn' ha hb hy'

theorem innerPaired_pow_eq_one (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} {A : uU h n} (htA : ψ t = uConjAut h (by omega) A) {l : K} (hl0 : l ≠ 0)
    (hlN : h.norm l = -1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1)
    {y : X} (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K - 1) = 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_unitary h hp2
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_neg, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = -1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨m, rfl⟩ := exists_half_of_antiunitary h h2 hU' hA'2
  have hm : 2 ≤ m := by omega
  obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form h h2 hU' hA'2 hl0 hlN
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) = (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) * M *
      ((HG : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        (1 : K) • ((uPairA (m := m) h h2 hl0 hlN : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) := by
    rw [hHi, coe_uGL, coe_uPairA, one_smul]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]
  obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer h hn hψ hInn htA ⟨HG, uGL_mem h _ _⟩
    one_ne_zero hconj
  refine pow_eq_one_of_transfer hinj' (fun y' hy' => ?_) hy
  rw [hψ't] at hy'
  exact upaired_pow_card_sub_one h hp2 h2 hm hinj hInn' hl0 hlN hy'

end CFSG.ComponentClassification.Burgoyne.U

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.Blueprint

theorem pow_eq_one_of_mem_oddCentralizerCore_PSU (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .PSU n p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
    have hcard : (p ^ f) ^ 2 - 1 = Nat.card K - 1 := by
      rw [h.card, ← pow_mul, mul_comm]
    rw [hcard]
    have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e1, e2⟩ => hq (by rw [e1, e2])
    have hψ := socleAction_injective hsimple hnab θ
    have hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
        MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ (socleAction θ).range := by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_range_socleAction θ x
    have hinj := conj_injective_of_mulEquiv hsimple hnab θ
    obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h hn hq' (socleAction θ t)
    have hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1 := by
      rw [← hα, ← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
    rcases uFieldAut_eq_or_of_sq h hn hq' hsq with rfl | hφ
    ·
      rw [map_one, mul_one] at hα hsq
      rw [← map_pow] at hsq
      obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
      have hAA : Am * Am = (c : K) • 1 := by
        have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
        simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
          at e
        rw [← pow_two, e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
      have hN : h.norm (c : K) = 1 := by
        have e : ((Am * Am).map h.bar)ᵀ * (Am * Am) = 1 := by
          rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
            Matrix.one_mul, hU]
        rw [hAA] at e
        have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
        simp [Matrix.mul_apply, Matrix.one_apply] at e1
        rw [UnitaryFieldData.norm, mul_comm]
        simpa [Matrix.smul_apply, Matrix.one_apply] using e1
      obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hN
      have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
      have hNl : h.norm l * h.norm l = 1 := by
        rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
        ring
      rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
      · have hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c := by
          intro c e
          have h1 : uConjAut h (by omega) A = 1 := (uConjAut_eq_one_iff h hn A).2 ⟨c, e⟩
          rw [h1, ← map_one (socleAction θ)] at hα
          have := hψ hα
          rw [this, orderOf_one] at ht
          exact absurd ht (by decide)
        exact innerSplit_pow_eq_one h hp2 hn hinj hψ hInn hα hl0 hN1 hAA' hns hy
      · exact innerPaired_pow_eq_one h hp2 hn hinj hψ hInn hα hl0 hN1 hAA' hy
    ·
      have hφe : φ = barEq h := RingEquiv.ext hφ
      subst hφe
      rw [graph_sq] at hsq
      obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
      have hAc : Am * Am.map h.bar = (c : K) • 1 := by
        have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
        simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut]
          at e
        change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h) = _
        rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      have h0 : oddCentralizerCore t = ⊥ := by
        refine eq_bot_of_oddCoreIn hψ ?_ le_rfl
        rw [hα]
        exact graph_oddCoreIn_eq_bot h hp2 hn hinj hInn hAc
      rw [h0, mem_bot] at hy
      rw [hy, one_pow]
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.U
