module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUDef
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAOrth
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.ComponentClassification.Burgoyne.U
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.Burgoyne.PSL (signMat)

section Transfer

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ka_u_transfer (hn : 3 ≤ n) {A A' H : uU h n} {c : K} (hc : c ≠ 0)
    (hH : (((H : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        c • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hA' : KAAll (uConjAut h (by omega) A')) : KAAll (uConjAut h (by omega) A) := by
  have e1 : uConjAut h (by omega) (H⁻¹ * A * H) = uConjAut h (by omega) A' := by
    refine uConjAut_eq_of_eq_smul h hn hc ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hH
  have e2 : MulAut.congr (uConjAut h (by omega) H) (uConjAut h (by omega) A') =
      uConjAut h (by omega) A := by
    rw [ka_orth_congr_eq, ← e1]
    simp only [map_mul, map_inv]
    group
  rw [← e2]
  exact KAAll.of_mulEquiv _ hA'

end Transfer

theorem kaAll_pu {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (hSplit : ∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ →
      KAAll (uConjAut h (by omega) (uSign h J)))
    (hPair : ∀ (A : uU h n) (l : K), l ≠ 0 → h.norm l = -1 →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1 →
      KAAll (uConjAut h (by omega) A))
    (hOrth : ∀ A : uU h n, kaUBar h A 1 →
      KAAll (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)))
    (hSymp : ∀ A : uU h n, kaUBar h A (-1) →
      KAAll (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)))
    {α : MulAut (StatedProj (StatedSU n (p ^ f) K))} (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    KAAll α := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h hn hq α
  have hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1 := by
    rw [← hα, sq]
    exact hα2
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
  rcases uFieldAut_eq_or_of_sq h hn hq hsq with rfl | hφ
  ·
    rw [map_one, mul_one] at hα hsq
    rw [← map_pow] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
    have hAA : Am * Am = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
        at e
      rw [← pow_two, e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
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
    ·
      have hNi : h.bar l⁻¹ * l⁻¹ = 1 := by
        rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_one]
      have hU' : ((l⁻¹ • Am).map h.bar)ᵀ * (l⁻¹ • Am) = 1 := by
        rw [show (l⁻¹ • Am).map h.bar = h.bar l⁻¹ • Am.map h.bar by
          ext i j; simp [map_mul]]
        rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
      have hA'2 : (l⁻¹ • Am) * (l⁻¹ • Am) = 1 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
        rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
      obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form h h2 hU' hA'2
      set HG := uGL h Hm hHU with hHG
      have hHi : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (Hm.map h.bar)ᵀ := rfl
      have hconj : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Am *
          ((HG : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J := by
        rw [hHi, coe_uGL]
        have e : Am = l • (l⁻¹ • Am) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
        rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
          Matrix.one_mul]
      have hHH : Hm * (Hm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
      have hJne : J.Nonempty ∧ J ≠ Finset.univ := by
        by_contra hcon
        have hJs : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
          by_cases hne : J.Nonempty
          · have huniv : J = Finset.univ := by
              by_contra hJu
              exact hcon ⟨hne, hJu⟩
            refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
            ext i j
            simp [signMat, diagonal_apply, one_apply, huniv]
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            refine ⟨1, one_ne_zero, ?_⟩
            ext i j
            simp [signMat, diagonal_apply, one_apply, hne]
        obtain ⟨s, hs, hsJ⟩ := hJs
        have e : l⁻¹ • Am = s • 1 := by
          calc l⁻¹ • Am = (l⁻¹ • Am) * (Hm * (Hm.map h.bar)ᵀ) := by rw [hHH, Matrix.mul_one]
            _ = (Hm * signMat K J) * (Hm.map h.bar)ᵀ := by rw [← Matrix.mul_assoc, hHA]
            _ = s • 1 := by
                rw [hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
        apply hα1
        rw [hα]
        apply (uConjAut_eq_one_iff h hn A).2
        refine ⟨Units.mk0 (l * s) (mul_ne_zero hl0 hs), Units.ext ?_⟩
        rw [GeneralLinearGroup.coe_scalar]
        change Am = _
        have e2 : Am = l • (l⁻¹ • Am) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
        rw [e2, e, smul_smul, Matrix.smul_one_eq_diagonal]
        rfl
      rw [hα]
      exact ka_u_transfer h hn hl0 (A' := uSign h J) (H := ⟨HG, uGL_mem h _ _⟩)
        (by rw [coe_uSign]; exact hconj) (hSplit J hJne.1 hJne.2)
    ·
      rw [hα]
      exact hPair A l hl0 hN1 hAA'
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
    rw [hα]
    rcases (exists_graph_frame h hp2 (by omega) hU c.ne_zero hAc).1 with h1 | h1
    · exact hOrth A (by rw [kaUBar, ← h1]; exact hAc)
    · exact hSymp A (by rw [kaUBar, ← h1]; exact hAc)

section Specialize

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem ka_u_two_ne_zero (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

theorem ka_u_pair_anti {n : ℕ} (A : uU h n) {l : K} (hl0 : l ≠ 0) (hN : h.norm l = -1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1) :
    ((((l⁻¹ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ *
        (l⁻¹ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) = -1) ∧
      (l⁻¹ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (l⁻¹ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN, inv_neg, inv_one]
  refine ⟨?_, ?_⟩
  · rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]

theorem ka_u_pair_even (hp2 : p ≠ 2) {n : ℕ} (A : uU h n) {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = -1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1) : ∃ m, n = m + m := by
  obtain ⟨h1, h2⟩ := ka_u_pair_anti h A hl0 hN hAA
  exact exists_half_of_antiunitary h (ka_u_two_ne_zero (h := h) hp2) h1 h2

theorem ka_u4_pair [Finite K] (hP : KAU4Pair) (hp2 : p ≠ 2) (A : uU h 4) (l : K) (hl0 : l ≠ 0)
    (hN : h.norm l = -1)
    (hAA : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (l ^ 2) • 1) :
    KAAll (uConjAut h (by norm_num) A) := by
  have h2 := ka_u_two_ne_zero (h := h) hp2
  obtain ⟨hU', hA'2⟩ := ka_u_pair_anti h A hl0 hN hAA
  obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form (m := 2) h h2 hU' hA'2 hl0 hN
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin (2 + 2)) K)⁻¹ : GL (Fin (2 + 2)) K) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) = (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin (2 + 2)) K)⁻¹ : GL (Fin (2 + 2)) K) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((HG : GL (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
        (1 : K) • ((uPairA (m := 2) h h2 hl0 hN : GL (Fin (2 + 2)) K) :
          Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) := by
    rw [hHi, coe_uGL, coe_uPairA, one_smul]
    have e : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        l • (l⁻¹ • ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
      rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]
  exact ka_u_transfer h (n := 2 + 2) (by norm_num) (A' := uPairA (m := 2) h h2 hl0 hN)
    (H := ⟨HG, uGL_mem h _ _⟩) one_ne_zero hconj (hP p f K h hp2 h2 l hl0 hN)

end Specialize

section Cells

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h

theorem ka_u_q_cases (hp2 : p ≠ 2) : p ^ f = 3 ∨ 5 ≤ p ^ f := by
  have hp := h.prime
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
  obtain ⟨m, hm⟩ := hodd
  omega

theorem ka_u_no_symp_odd (hp2 : p ≠ 2) {n : ℕ} (hn : Odd n) (A : uU h n)
    (hA : kaUBar h A (-1)) : False := by
  have h2 := ka_u_two_ne_zero (h := h) hp2
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
  have d1 : (Am.map h.bar).det * Am.det = 1 := by
    have := congrArg Matrix.det hU
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have d2 : (Am * Am.map h.bar).det = -1 := by
    rw [kaUBar] at hA
    rw [hA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact hn.neg_one_pow
  have d3 : (Am * Am.map h.bar).det = 1 := by
    rw [Matrix.det_mul, mul_comm]
    exact d1
  have : (1 : K) = -1 := d3.symm.trans d2
  exact h2 (by linear_combination this)

theorem kaAll_pu3 [Finite K] (hS : KAUSplit) (hO : KAUGOrth) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {α : MulAut (StatedProj (StatedSU 3 (p ^ f) K))} (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    KAAll α := by
  refine kaAll_pu h hp2 (n := 3) le_rfl (by omega) ?_ ?_ ?_ ?_ hα2 hα1
  · intro J hJ hJu
    exact hS p f K h 3 le_rfl hp2 J hJ hJu (fun _ => h5)
  · intro A l hl0 hN hAA
    obtain ⟨m, hm⟩ := ka_u_pair_even h hp2 A hl0 hN hAA
    omega
  · intro A hA
    exact hO p f K h 3 le_rfl hp2 (by omega) A hA
  · intro A hA
    exact (ka_u_no_symp_odd h hp2 (by decide) A hA).elim

theorem kaAll_pu5 [Finite K] (hS : KAUSplit) (hO : KAUGOrth) (hp2 : p ≠ 2) (h4 : p ^ f % 4 = 1)
    {α : MulAut (StatedProj (StatedSU 5 (p ^ f) K))} (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    KAAll α := by
  have h5 : 5 ≤ p ^ f := by
    rcases ka_u_q_cases h hp2 with h3 | h5
    · omega
    · exact h5
  refine kaAll_pu h hp2 (n := 5) (by norm_num) (by omega) ?_ ?_ ?_ ?_ hα2 hα1
  · intro J hJ hJu
    exact hS p f K h 5 (by norm_num) hp2 J hJ hJu (fun _ => h5)
  · intro A l hl0 hN hAA
    obtain ⟨m, hm⟩ := ka_u_pair_even h hp2 A hl0 hN hAA
    omega
  · intro A hA
    exact hO p f K h 5 (by norm_num) hp2 (by omega) A hA
  · intro A hA
    exact (ka_u_no_symp_odd h hp2 (by decide) A hA).elim

theorem kaAll_pu4 [Finite K] (hS : KAUSplit) (hS3 : KAU4SplitThree) (hP : KAU4Pair) (hO : KAUGOrth)
    (hO3 : KAU4GOrthThree) (hSp : KAU4GSp) (hp2 : p ≠ 2)
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    KAAll α := by
  have hq := ka_u_q_cases h hp2
  refine kaAll_pu h hp2 (n := 4) (by norm_num) (by omega) ?_
    (fun A l hl0 hN hAA => ka_u4_pair h hP hp2 A l hl0 hN hAA) ?_
    (fun A hA => hSp p f K h hp2 A hA) hα2 hα1
  · intro J hJ hJu
    by_cases hc : J.card = 2
    · rcases hq with h3 | h5
      · exact hS3 p f K h hp2 h3 J hc
      · exact hS p f K h 4 (by norm_num) hp2 J hJ hJu (fun _ => h5)
    · exact hS p f K h 4 (by norm_num) hp2 J hJ hJu (fun hh => by omega)
  · intro A hA
    rcases hq with h3 | h5
    · exact hO3 p f K h hp2 h3 A hA
    · exact hO p f K h 4 (by norm_num) hp2 (by omega) A hA

end Cells

section Iso

theorem ka_kaAll_of_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {α : MulAut Y}
    (h : KAAll (MulAut.congr e α)) : KAAll α := by
  have h' := KAAll.of_mulEquiv e.symm h
  have key : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext y
    simp [MulAut.congr_apply]
  rwa [key] at h'

end Iso

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
