module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks3

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mul_map_eq_of_fix_U (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} {A : GL (Fin 4) K} {φ : K ≃+* K}
    {hA : ∀ g : unitarySU p f K 4, A * glAut φ (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4}
    (hlift : ∀ g : unitarySU p f K 4,
      thU p f K (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) =
        α (thU p f K g))
    {U : Matrix (Fin 4) (Fin 4) K} (hU : uStar h U * stdG * U = stdG) (hd : U.det = 1)
    (htr : U.trace = 4)
    (hfx : α (thU p f K (hypSU h P hP U hU hd)) = thU p f K (hypSU h P hP U hU hd)) :
    ((P⁻¹ * A * glAut φ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * U.map φ =
      U * ((P⁻¹ * A * glAut φ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  have hlift' : ∀ g : unitarySU p f K 4,
      (QuotientGroup.mk (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) :
        StatedProj (StatedSU 4 (p ^ f) K)) = α (QuotientGroup.mk g) := hlift
  have e1 := conj_eq_of_fix h4 hlift' hfx (by rw [val_hypSU, StabU.trace_conj]; exact htr)
  have e3 : ((hypSU h P hP U hU hd : unitarySU p f K 4) : GL (Fin 4) K) =
      P * toGL U hd * P⁻¹ := rfl
  rw [e3, map_mul, map_mul, map_inv] at e1
  set A' := P⁻¹ * A * glAut φ P with hA'
  have e2 : A' * glAut φ (toGL U hd) * A'⁻¹ = toGL U hd := by
    rw [hA']
    calc P⁻¹ * A * glAut φ P * glAut φ (toGL U hd) * (P⁻¹ * A * glAut φ P)⁻¹ =
        P⁻¹ * (A * (glAut φ P * glAut φ (toGL U hd) * (glAut φ P)⁻¹) * A⁻¹) * P := by group
      _ = P⁻¹ * (P * toGL U hd * P⁻¹) * P := by rw [e1]
      _ = toGL U hd := by group
  have e4 : A' * glAut φ (toGL U hd) = toGL U hd * A' := by
    calc A' * glAut φ (toGL U hd) = (A' * glAut φ (toGL U hd) * A'⁻¹) * A' := by group
      _ = toGL U hd * A' := by rw [e2]
  have e5 := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K)) e4
  simp only [Units.val_mul, coe_glAut, coe_toGL] at e5
  exact e5

theorem blk_of_fix (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {μ : Kˣ} (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ)
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} {A : GL (Fin 4) K} {φ : K ≃+* K}
    {hA : ∀ g : unitarySU p f K 4, A * glAut φ (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hlift : ∀ g : unitarySU p f K 4,
      thU p f K (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) =
        α (thU p f K g))
    (h1 : α (thU p f K (uU h P hP 1)) = thU p f K (uU h P hP 1))
    (h2 : α (thU p f K (uL h P hP 1)) = thU p f K (uL h P hP 1))
    (h3 : α (thU p f K (uU h P hP μ)) = thU p f K (uU h P hP μ)) :
    ∃ x b e y : K, ((P⁻¹ * A * glAut φ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk x b e y ∧ b * h.bar e + h.bar x * y = 1 ∧
      ((φ = RingEquiv.refl K ∧ b = 0 ∧ e = 0) ∨ ((∀ c, φ c = h.bar c) ∧ x = 0 ∧ y = 0)) := by
  classical
  have hE1 := mul_map_eq_of_fix_U h hp2 P hP hlift (unitary_U12 h 1) (det_U12 h 1)
    (trace_U12 h 1) h1
  have hE2 := mul_map_eq_of_fix_U h hp2 P hP hlift (unitary_U21 h 1) (det_U21 h 1)
    (trace_U21 h 1) h2
  have hE3 := mul_map_eq_of_fix_U h hp2 P hP hlift (unitary_U12 h (μ : K)) (det_U12 h (μ : K))
    (trace_U12 h (μ : K)) h3
  rw [map_U12_equiv, map_one] at hE1
  rw [map_U21_equiv, map_one] at hE2
  rw [map_U12_equiv] at hE3
  obtain ⟨M, hM⟩ : ∃ X : Matrix (Fin 4) (Fin 4) K,
      X = ((P⁻¹ * A * glAut φ P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := ⟨_, rfl⟩
  rw [← hM] at hE1 hE2 hE3
  have hblk := eq_blk_of_comm h hE1 hE2
  rw [hblk] at hE3
  obtain ⟨r1, r2, r3, r4⟩ := blk_rel h hE3
  have hMu : uStar h M * stdG * M = stdG := by
    have hPi := uStar_inv_mul h P hP
    rw [hM, Units.val_mul, Units.val_mul, coe_glAut, uStar_mul, uStar_mul]
    calc uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
          (uStar h (A : Matrix (Fin 4) (Fin 4) K) * uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
          stdG * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
            (P : Matrix (Fin 4) (Fin 4) K).map φ) =
        uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
          (uStar h (A : Matrix (Fin 4) (Fin 4) K) * ((uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            stdG * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (A : Matrix (Fin 4) (Fin 4) K))) *
          (P : Matrix (Fin 4) (Fin 4) K).map φ := by simp only [Matrix.mul_assoc]
      _ = uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
          (P : Matrix (Fin 4) (Fin 4) K).map φ := by
          rw [hPi, Matrix.one_mul, hAu, Matrix.mul_one]
      _ = stdG := by
          rw [uStar_map_equiv, ← Matrix.map_mul, hP]
          exact stdG_map (φ : K →+* K)
  rw [hblk] at hMu
  have hun := blk_unitary h hMu
  have hμb := bar_ne_of_generator h hμ
  refine ⟨M 0 0, M 0 3, M 2 1, M 2 2, hM ▸ hblk, hun, ?_⟩
  by_cases hφμ : φ (μ : K) = μ
  · left
    refine ⟨RingEquiv.ext fun c => eq_of_eq_on_generator hμ (φ : K →+* K) (RingHom.id K) hφμ c,
      ?_, ?_⟩
    · rw [hφμ] at r2
      rcases mul_eq_zero.1 r2 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hμb
    · rw [hφμ] at r3
      rcases mul_eq_zero.1 r3 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0).symm hμb
  · right
    have hx : M 0 0 = 0 := by
      rcases mul_eq_zero.1 r1 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hφμ
    have hy : M 2 2 = 0 := by
      rcases mul_eq_zero.1 r4 with h0 | h0
      · exact h0
      · exfalso
        apply hφμ
        have e := congrArg h.bar (sub_eq_zero.1 h0)
        rwa [h.bar_bar, h.bar_bar] at e
    rw [hx, hy, map_zero, zero_mul, add_zero] at hun
    have hf0 : M 2 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero, mul_zero] at hun
      exact zero_ne_one hun
    have hφμb : φ (μ : K) = h.bar μ := by
      rcases mul_eq_zero.1 r3 with h0 | h0
      · exact absurd h0 hf0
      · exact sub_eq_zero.1 h0
    exact ⟨eq_of_eq_on_generator hμ (φ : K →+* K) h.bar hφμb, hx, hy⟩

@[expose] noncomputable def hypBasisMat (u : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 2⁻¹, 0; u, 0, -(u * 2⁻¹), 0; 0, 1, 0, 2⁻¹; 0, u, 0, -(u * 2⁻¹)]

theorem uStar_hypBasisMat (hp2 : p ≠ 2) {u : K} (hu : h.bar u * u = -1) :
    uStar h (hypBasisMat u) * hypBasisMat u = stdG := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hb2 : h.bar (2⁻¹ : K) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uStar, hypBasisMat, stdG, Matrix.mul_apply, Fin.sum_univ_four, hb2] <;>
    (try field_simp) <;>
    first | linear_combination hu | linear_combination -hu

theorem exists_hypBasis (hp2 : p ≠ 2) :
    ∃ P : GL (Fin 4) K,
      uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG := by
  obtain ⟨u, hu⟩ := exists_bar_mul_eq_neg_one h
  have hP := uStar_hypBasisMat h hp2 hu
  have hdet : (hypBasisMat u).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hP
    have hs : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
    rw [det_mul, h0, mul_zero, hs] at this
    exact zero_ne_one this
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, by
    rw [GeneralLinearGroup.val_mkOfDetNeZero]; exact hP⟩

theorem trace_gfix (β γ : K) : (gfix β γ).trace = 4 := by
  simp only [gfix, Matrix.trace, Matrix.diag, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val]
  norm_num

theorem lift_of_isCU {M : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h M α) :
    ∃ hA : ∀ g : unitarySU p f K 4,
        M * glAut (RingEquiv.refl K) (g : GL (Fin 4) K) * M⁻¹ ∈ unitarySU p f K 4,
      ∀ g : unitarySU p f K 4,
        thU p f K (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom M
          (RingEquiv.refl K) hA g) = α (thU p f K g) := by
  have hgl : ∀ X : GL (Fin 4) K, glAut (RingEquiv.refl K) X = X := fun X => by
    change glAut 1 X = X
    rw [map_one]
    rfl
  refine ⟨fun g => by rw [hgl]; exact conj_mem_SU h hα.1 g, fun g => ?_⟩
  rw [hα.apply h]
  congr 1

theorem eq_smul_one_of_isCU_one (hp2 : p ≠ 2) {M : GL (Fin 4) K} (hM : IsCU h M 1) :
    ∃ c : K, (M : Matrix (Fin 4) (Fin 4) K) = c • 1 := by
  classical
  have : Finite K := h.finite
  obtain ⟨P, hP⟩ := exists_hypBasis h hp2
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨hA, hlift⟩ := lift_of_isCU h hM
  obtain ⟨x, b, e, y, hblk, -, hcase⟩ := blk_of_fix h hp2 P hP hμ (mem_uMat h |>.1 hM.1) hlift
    rfl rfl rfl
  rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hb, -, -⟩
  · obtain ⟨c, hc⟩ := h.exists_bar_ne
    set β : K := c - h.bar c with hβ
    have hβ0 : β ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    have hββ : β + h.bar β = 0 := by rw [hβ, map_sub, h.bar_bar]; ring
    have hγ : (0 : K) + h.bar 0 = 0 := by rw [map_zero, add_zero]
    have hE := mul_map_eq_of_fix_U h hp2 P hP hlift (unitary_gfix h hββ hγ) (det_gfix β 0)
      (trace_gfix β 0) rfl
    have hmap : (gfix β (0 : K)).map (RingEquiv.refl K) = gfix β 0 := by
      ext i j
      rfl
    rw [hmap, hblk] at hE
    have hxy := eq_of_blk_comm_gfix hβ0 hE
    subst hxy
    refine ⟨x, ?_⟩
    have hPM : (M : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) *
        ((P⁻¹ * M * glAut (RingEquiv.refl K) P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      have hgl : glAut (RingEquiv.refl K) P = P := by
        change glAut 1 P = P
        rw [map_one]
        rfl
      rw [hgl, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have hblk1 : blk x 0 0 x = x • (1 : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blk]
    rw [hPM, hblk, hblk1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  · exfalso
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (hb c).symm

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
