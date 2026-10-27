module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldDesc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEigen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupTransport

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF exists_orth_normal_form)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}

theorem gram_comb (R : Matrix (Fin d) (Fin d) K) {m : ℕ} (u : Fin m → Fin d → K)
    (P : Matrix (Fin m) (Fin m) K) (j k : Fin m) :
    (∑ i, P i j • u i) ⬝ᵥ R *ᵥ (∑ l, P l k • u l) =
      (Pᵀ * Matrix.of (fun i l => u i ⬝ᵥ R *ᵥ u l) * P) j k := by
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, sum_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, Matrix.mul_apply, transpose_apply, of_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem exists_field_frame (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hd3 : 3 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {A' : Matrix (Fin d) (Fin d) K}
    (hA'2 : A' * A'.map h.bar = 1) {r : K} (hr0 : r ≠ 0)
    (hF : ∀ v w, A' *ᵥ barV h v = v → A' *ᵥ barV h w = w →
      r⁻¹ * (v ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ w) ∈ h.fixedField) :
    ∃ (cv : Fin d → Fin d → K) (wF : Fin d → h.fixedField), OrthNF wF ∧
      (∀ j, A' *ᵥ barV h (cv j) = cv j) ∧
      ∀ j k, cv j ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ cv k =
        r * (if j = k then (wF j : K) else 0) := by
  have := h.finite
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  set τ := semilinearMatrixMap h A' with hτ
  have hτv : ∀ v, τ v = A' *ᵥ barV h v := fun v => semilinearMatrixMap_apply h A' v
  have hττ : ∀ v, τ (τ v) = v := by
    intro v
    rw [hτv, hτv, mulVec_barV_mulVec, hA'2, one_mulVec]
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  set t₀ := c₀ - h.bar c₀ with ht₀
  have ht : h.bar t₀ = -t₀ := by
    rw [ht₀, map_sub, h.bar_bar]
    ring
  have ht0 : t₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hc₀)
  have : Module.Finite h.fixedField (conjFixed h τ) := finite_conjFixed
  have hfin : Module.finrank h.fixedField (conjFixed h τ) = d :=
    (finrank_conjFixed hττ ht ht0 h2).trans (Module.finrank_fin_fun K)
  set wb := Module.finBasisOfFinrankEq h.fixedField (conjFixed h τ) hfin with hwb
  set u : Fin d → Fin d → K := fun i => (wb i : Fin d → K) with hu
  have huW : ∀ i, A' *ᵥ barV h (u i) = u i := fun i => by
    rw [← hτv]
    exact mem_conjFixed.1 (wb i).2
  set GF : Matrix (Fin d) (Fin d) h.fixedField :=
    Matrix.of fun i j => ⟨r⁻¹ * (u i ⬝ᵥ Rm *ᵥ u j), hF _ _ (huW i) (huW j)⟩ with hGFdef
  have hGF : ∀ i j, (GF i j : K) = r⁻¹ * (u i ⬝ᵥ Rm *ᵥ u j) := fun i j => rfl
  have hGsym : GFᵀ = GF := by
    ext i j
    rw [transpose_apply, hGF, hGF, dot_symm hR]
  have hspan := span_conjFixed hττ ht ht0 h2
  have hnd : ∀ y ∈ conjFixed h τ, (∀ z ∈ conjFixed h τ, z ⬝ᵥ Rm *ᵥ y = 0) → y = 0 := by
    intro y hy hz
    have hall : ∀ z, z ⬝ᵥ Rm *ᵥ y = 0 := by
      intro z
      have hzs : z ∈ Submodule.span K (conjFixed h τ : Set (Fin d → K)) :=
        hspan ▸ Submodule.mem_top
      induction hzs using Submodule.span_induction with
      | mem x hx => exact hz x hx
      | zero => simp
      | add x y' _ _ hx hy' => rw [add_dotProduct, hx, hy', add_zero]
      | smul a x _ hx => rw [smul_dotProduct, hx, smul_zero]
    have hRy : Rm *ᵥ y = 0 := by
      funext i
      have := hall (Pi.single i 1)
      rwa [single_one_dotProduct] at this
    have e1 : ((R⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (Rm *ᵥ y) = y := by
      rw [mulVec_mulVec, hRm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [← e1, hRy, mulVec_zero]
  have hdet : GF.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set y : conjFixed h τ := ∑ j, x j • wb j with hy
    have hyv : (y : Fin d → K) = ∑ j, (x j : K) • u j := by
      rw [hy, Submodule.coe_sum]
      rfl
    have hyR : ∀ i, u i ⬝ᵥ Rm *ᵥ (y : Fin d → K) = 0 := by
      intro i
      have e := congrArg (fun a : h.fixedField => (a : K)) (congrFun hx i)
      simp only [mulVec, dotProduct, Pi.zero_apply, ZeroMemClass.coe_zero] at e
      push_cast at e
      rw [hyv, mulVec_sum, dotProduct_sum]
      simp only [mulVec_smul, dotProduct_smul, smul_eq_mul]
      have e' : ∑ j, (GF i j : K) * (x j : K) = r⁻¹ * ∑ j, (x j : K) * (u i ⬝ᵥ Rm *ᵥ u j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hGF]
        ring
      have e2 : r⁻¹ * ∑ j, (x j : K) * (u i ⬝ᵥ Rm *ᵥ u j) = 0 := by
        rw [← e']
        convert e using 2
      exact (mul_eq_zero.1 e2).resolve_left (inv_ne_zero hr0)
    have hy0 : (y : Fin d → K) = 0 := by
      refine hnd _ y.2 fun z hz => ?_
      have hz' : z = ∑ i, ((wb.repr ⟨z, hz⟩ i : h.fixedField) : K) • u i := by
        have := congrArg Subtype.val (wb.sum_repr ⟨z, hz⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [hz', sum_dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_dotProduct, hyR, smul_zero]
    have hli := wb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    exact hx0 (funext (hli x (by rw [← hy]; exact Subtype.ext hy0)))
  set GG : GL (Fin d) h.fixedField := Matrix.nonsingInvUnit GF (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨P, wF, hNF, hP⟩ := exists_orth_normal_form (two_ne_zero_fixedField h hp2) hd3 GG hGsym
  set cvW : Fin d → conjFixed h τ := fun j =>
    ∑ i, (P : Matrix (Fin d) (Fin d) h.fixedField) i j • wb i
  set Pm := (P : Matrix (Fin d) (Fin d) h.fixedField).map h.fixedField.subtype with hPm
  have hcv : ∀ j, (cvW j : Fin d → K) = ∑ i, Pm i j • u i := by
    intro j
    simp only [cvW, Submodule.coe_sum]
    rfl
  refine ⟨fun j => (cvW j : Fin d → K), wF, hNF, fun j => ?_, fun j k => ?_⟩
  · rw [← hτv]
    exact mem_conjFixed.1 (cvW j).2
  · have hG : GF.map h.fixedField.subtype = r⁻¹ • Matrix.of (fun i l => u i ⬝ᵥ Rm *ᵥ u l) := by
      ext i l
      rfl
    have e := congrArg (fun M : Matrix (Fin d) (Fin d) h.fixedField =>
      M.map h.fixedField.subtype) hP
    simp only [Matrix.map_mul, transpose_map] at e
    have e2 := congrFun (congrFun e j) k
    change (Pmᵀ * GF.map h.fixedField.subtype * Pm) j k =
      ((diagonal wF).map h.fixedField.subtype) j k at e2
    rw [hG, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
      diagonal_apply] at e2
    change (cvW j : Fin d → K) ⬝ᵥ Rm *ᵥ (cvW k : Fin d → K) = _
    rw [hcv, hcv, gram_comb]
    have e3 : (Pmᵀ * Matrix.of (fun i l => u i ⬝ᵥ Rm *ᵥ u l) * Pm) j k =
        r * (r⁻¹ * (Pmᵀ * Matrix.of (fun i l => u i ⬝ᵥ Rm *ᵥ u l) * Pm) j k) := by
      field_simp
    rw [e3, e2]
    congr 1
    split_ifs <;> simp

end CFSG.ComponentClassification.Burgoyne.O
