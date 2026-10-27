module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Levi

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Irred

variable {p f : ℕ} {K : Type} [Field K]

theorem stepA_u_e0 (h : UnitaryFieldData p f K) (v : HypIndex 2 0 → K) (τ : K) :
    h.bar τ • (leviMat h (uEl 1) *ᵥ v - v) - (leviMat h (uEl τ) *ᵥ v - v) =
      ((h.bar τ - τ) * v (Sum.inl 1)) • (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) := by
  ext x
  rcases x with i | k | i
  · fin_cases i
    · simp [levi_u_e0]; ring
    · simp [levi_u_e1]
  · exact k.elim0
  · fin_cases i
    · simp [levi_u_f0]
    · simp [levi_u_f1]

theorem stepA_u_f1 (h : UnitaryFieldData p f K) (v : HypIndex 2 0 → K) (τ : K) :
    τ • (leviMat h (uEl 1) *ᵥ v - v) - (leviMat h (uEl τ) *ᵥ v - v) =
      ((h.bar τ - τ) * v (Sum.inr (Sum.inr 0))) •
        (Pi.single (Sum.inr (Sum.inr 1)) 1 : HypIndex 2 0 → K) := by
  ext x
  rcases x with i | k | i
  · fin_cases i
    · simp [levi_u_e0]
    · simp [levi_u_e1]
  · exact k.elim0
  · fin_cases i
    · simp [levi_u_f0]
    · simp [levi_u_f1]; ring

theorem stepA_l_e1 (h : UnitaryFieldData p f K) (v : HypIndex 2 0 → K) (τ : K) :
    h.bar τ • (leviMat h (lEl 1) *ᵥ v - v) - (leviMat h (lEl τ) *ᵥ v - v) =
      ((h.bar τ - τ) * v (Sum.inl 0)) • (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) := by
  ext x
  rcases x with i | k | i
  · fin_cases i
    · simp [levi_l_e0]
    · simp [levi_l_e1]; ring
  · exact k.elim0
  · fin_cases i
    · simp [levi_l_f0]
    · simp [levi_l_f1]

theorem stepA_l_f0 (h : UnitaryFieldData p f K) (v : HypIndex 2 0 → K) (τ : K) :
    τ • (leviMat h (lEl 1) *ᵥ v - v) - (leviMat h (lEl τ) *ᵥ v - v) =
      ((h.bar τ - τ) * v (Sum.inr (Sum.inr 1))) •
        (Pi.single (Sum.inr (Sum.inr 0)) 1 : HypIndex 2 0 → K) := by
  ext x
  rcases x with i | k | i
  · fin_cases i
    · simp [levi_l_e0]
    · simp [levi_l_e1]
  · exact k.elim0
  · fin_cases i
    · simp [levi_l_f0]; ring
    · simp [levi_l_f1]

theorem levi_l_one_e0 (h : UnitaryFieldData p f K) :
    leviMat h (lEl 1) *ᵥ (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) - Pi.single (Sum.inl 0) 1 =
      (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) := by
  generalize hv : (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) = v
  have h0 : v (Sum.inl 0) = 1 := by rw [← hv]; simp
  have h1 : v (Sum.inl 1) = 0 := by rw [← hv]; simp
  have hf0 : v (Sum.inr (Sum.inr 0)) = 0 := by rw [← hv]; simp
  have hf1 : v (Sum.inr (Sum.inr 1)) = 0 := by rw [← hv]; simp
  ext x
  rcases x with i | k | i
  · fin_cases i
    · simp [levi_l_e0, h0]
    · simp [levi_l_e1, h0, h1]
  · exact k.elim0
  · fin_cases i
    · simp [levi_l_f0, hf0, hf1]
    · simp [levi_l_f1, hf1]

theorem levi_u_one_e1 (h : UnitaryFieldData p f K) :
    leviMat h (uEl 1) *ᵥ (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) - Pi.single (Sum.inl 1) 1 =
      (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) := by
  generalize hv : (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) = v
  have h0 : v (Sum.inl 0) = 0 := by rw [← hv]; simp
  have h1 : v (Sum.inl 1) = 1 := by rw [← hv]; simp
  have hf0 : v (Sum.inr (Sum.inr 0)) = 0 := by rw [← hv]; simp
  have hf1 : v (Sum.inr (Sum.inr 1)) = 0 := by rw [← hv]; simp
  ext x
  rcases x with i | k | i
  · fin_cases i
    · simp [levi_u_e0, h0, h1]
    · simp [levi_u_e1, h1]
  · exact k.elim0
  · fin_cases i
    · simp [levi_u_f0, hf0]
    · simp [levi_u_f1, hf0, hf1]

theorem irred_of_levi_swap (h : UnitaryFieldData p f K) (W : Submodule K (HypIndex 2 0 → K))
    (hL : ∀ A : SL(2, K), ∀ v ∈ W, leviMat h A *ᵥ v ∈ W)
    {w : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (hw1 : ∀ i : Fin 2, w *ᵥ Pi.single (Sum.inl i) 1 = c • Pi.single (Sum.inr (Sum.inr i)) 1)
    (hw2 : ∀ i : Fin 2, w *ᵥ Pi.single (Sum.inr (Sum.inr i)) 1 = d • Pi.single (Sum.inl i) 1)
    (hJ : ∀ v ∈ W, w *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨τ, hτ⟩ := h.exists_bar_ne
  have hτ' : h.bar τ - τ ≠ 0 := sub_ne_zero.2 hτ
  have hC0 : (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ W →
      (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) ∈ W := fun he => by
    rw [← levi_l_one_e0 h]
    exact W.sub_mem (hL _ _ he) he
  have hC1 : (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) ∈ W →
      (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ W := fun he => by
    rw [← levi_u_one_e1 h]
    exact W.sub_mem (hL _ _ he) he
  have hF0 : (Pi.single (Sum.inr (Sum.inr 0)) 1 : HypIndex 2 0 → K) ∈ W →
      (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ W := fun hf => by
    have := hJ _ hf
    rw [hw2] at this
    have h2 := W.smul_mem d⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  have hF1 : (Pi.single (Sum.inr (Sum.inr 1)) 1 : HypIndex 2 0 → K) ∈ W →
      (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) ∈ W := fun hf => by
    have := hJ _ hf
    rw [hw2] at this
    have h2 := W.smul_mem d⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  have hall : (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ W →
      (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) ∈ W →
      (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ W ∧
      (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) ∈ W ∧
      (Pi.single (Sum.inr (Sum.inr 0)) 1 : HypIndex 2 0 → K) ∈ W ∧
      (Pi.single (Sum.inr (Sum.inr 1)) 1 : HypIndex 2 0 → K) ∈ W := by
    intro he0 he1
    refine ⟨he0, he1, ?_, ?_⟩
    · have := hJ _ he0
      rw [hw1] at this
      have h2 := W.smul_mem c⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    · have := hJ _ he1
      rw [hw1] at this
      have h2 := W.smul_mem c⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv0
  have hbasis : (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ W ∧
      (Pi.single (Sum.inl 1) 1 : HypIndex 2 0 → K) ∈ W ∧
      (Pi.single (Sum.inr (Sum.inr 0)) 1 : HypIndex 2 0 → K) ∈ W ∧
      (Pi.single (Sum.inr (Sum.inr 1)) 1 : HypIndex 2 0 → K) ∈ W := by
    rcases a with i | k | i
    · fin_cases i
      ·
        have ha0 : v (Sum.inl 0) ≠ 0 := by simpa using ha
        have h1 := W.sub_mem (W.smul_mem (h.bar τ) (W.sub_mem (hL (lEl 1) v hvW) hvW))
          (W.sub_mem (hL (lEl τ) v hvW) hvW)
        rw [stepA_l_e1] at h1
        have h2 := W.smul_mem (((h.bar τ - τ) * v (Sum.inl 0))⁻¹) h1
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ' ha0), one_smul] at h2
        exact hall (hC1 h2) h2
      · have ha0 : v (Sum.inl 1) ≠ 0 := by simpa using ha
        have h1 := W.sub_mem (W.smul_mem (h.bar τ) (W.sub_mem (hL (uEl 1) v hvW) hvW))
          (W.sub_mem (hL (uEl τ) v hvW) hvW)
        rw [stepA_u_e0] at h1
        have h2 := W.smul_mem (((h.bar τ - τ) * v (Sum.inl 1))⁻¹) h1
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ' ha0), one_smul] at h2
        exact hall h2 (hC0 h2)
    · exact k.elim0
    · fin_cases i
      · have ha0 : v (Sum.inr (Sum.inr 0)) ≠ 0 := by simpa using ha
        have h1 := W.sub_mem (W.smul_mem τ (W.sub_mem (hL (uEl 1) v hvW) hvW))
          (W.sub_mem (hL (uEl τ) v hvW) hvW)
        rw [stepA_u_f1] at h1
        have h2 := W.smul_mem (((h.bar τ - τ) * v (Sum.inr (Sum.inr 0)))⁻¹) h1
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ' ha0), one_smul] at h2
        have h3 := hF1 h2
        exact hall (hC1 h3) h3
      · have ha0 : v (Sum.inr (Sum.inr 1)) ≠ 0 := by simpa using ha
        have h1 := W.sub_mem (W.smul_mem τ (W.sub_mem (hL (lEl 1) v hvW) hvW))
          (W.sub_mem (hL (lEl τ) v hvW) hvW)
        rw [stepA_l_f0] at h1
        have h2 := W.smul_mem (((h.bar τ - τ) * v (Sum.inr (Sum.inr 1)))⁻¹) h1
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ' ha0), one_smul] at h2
        have h3 := hF0 h2
        exact hall h3 (hC0 h3)
  rw [eq_top_iff, ← (Pi.basisFun K (HypIndex 2 0)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases i with i | k | i
  · fin_cases i
    · simpa using hbasis.1
    · simpa using hbasis.2.1
  · exact k.elim0
  · fin_cases i
    · simpa using hbasis.2.2.1
    · simpa using hbasis.2.2.2

theorem u4_cls2_irred_frame (h : UnitaryFieldData p f K) {l : K} (hl0 : l ≠ 0) (hN : h.norm l = -1)
    (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub (hypPhi h (a0U h hl0 hN)) → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨w, c, d, hc, hd, hw1, hw2⟩ := exists_swap h
  refine irred_of_levi_swap h W (fun A v hv => hW (leviSU h 0 A)
    (hypProj_mem_fixSub_of_comm h hl0 hN _ (a0Mat_comm_levi h l A)) v hv) hc hd hw1 hw2
    (fun v hv => hW w (hypProj_mem_fixSub_of_anticomm h hl0 hN w
      (a0Mat_anticomm_of_swap l hw1 hw2)) v hv)

end Irred

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
