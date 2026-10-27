module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3E8Core

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.LieType.Steinberg
  CFSG.GH74.Generic.BProg.B2.GenLocU3NF CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

namespace GenLocU3E8Frame

open GenLocU3Good GenLocU3Small GenLocU3Seven GenLocU3E8Elem GenLocU3E8Core

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

@[expose] def OddAt (d : Fin 3 → F) (k : Fin 3) : Prop :=
  (∀ u, u ≠ k → d k = -d u) ∧ ∀ u v, u ≠ k → v ≠ k → d u = d v

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem exists_oddAt {d : Fin 3 → F}
    (hc : (d 1 = d 2 ∧ d 0 = -d 1) ∨ (d 0 = d 2 ∧ d 1 = -d 0) ∨ (d 0 = d 1 ∧ d 2 = -d 0)) :
    ∃ k, OddAt d k := by
  rcases hc with ⟨h12, h0⟩ | ⟨h02, h1⟩ | ⟨h01, h2⟩
  · refine ⟨0, fun u hu => ?_, fun u v hu hv => ?_⟩
    · fin_cases u
      · exact absurd rfl hu
      · exact h0
      · exact h0.trans (congrArg Neg.neg h12)
    · fin_cases u <;> fin_cases v <;>
        first | exact absurd rfl hu | exact absurd rfl hv | rfl | exact h12 | exact h12.symm
  · refine ⟨1, fun u hu => ?_, fun u v hu hv => ?_⟩
    · fin_cases u
      · exact h1
      · exact absurd rfl hu
      · exact h1.trans (congrArg Neg.neg h02)
    · fin_cases u <;> fin_cases v <;>
        first | exact absurd rfl hu | exact absurd rfl hv | rfl | exact h02 | exact h02.symm
  · refine ⟨2, fun u hu => ?_, fun u v hu hv => ?_⟩
    · fin_cases u
      · exact h2
      · exact h2.trans (congrArg Neg.neg h01)
      · exact absurd rfl hu
    · fin_cases u <;> fin_cases v <;>
        first | exact absurd rfl hu | exact absurd rfl hv | rfl | exact h01 | exact h01.symm

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem prod_eq_of_oddAt {d d' : Fin 3 → F} {k : Fin 3} (h1 : OddAt d k) (h3 : OddAt d' k)
    (u v : Fin 3) : d u * d' u = d v * d' v := by
  by_cases hu : u = k <;> by_cases hv : v = k
  · rw [hu, hv]
  · subst hu
    have e1 := h1.1 v hv
    have e3 := h3.1 v hv
    rw [e1, e3]; ring
  · subst hv
    have e1 := h1.1 u hu
    have e3 := h3.1 u hu
    rw [e1, e3]; ring
  · rw [h1.2 u v hu hv, h3.2 u v hu hv]

theorem exists_perm_of_ne (k₁ k₃ : Fin 3) (h : k₁ ≠ k₃) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = k₁ ∧ σ 2 = k₃ := by
  revert k₁ k₃
  decide

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem mul_diag_apply {A B : Matrix (Fin 3) (Fin 3) F} (hA : A.IsDiag) (u : Fin 3) :
    (A * B) u u = A u u * B u u := by
  rw [Matrix.mul_apply, Finset.sum_eq_single u]
  · intro k _ hk
    rw [hA hk.symm, zero_mul]
  · simp

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem gl_diag_comm {A B : GL (Fin 3) F} (hA : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hB : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) : A * B = B * A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine diag_comm_of hA fun i j => ?_
  by_cases hij : i = j
  · rw [hij, mul_comm]
  · rw [hB hij, mul_zero, zero_mul]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem oddAt_of_A0 (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {A : Type} [Group A] (α : A →* MulAut J)
    (hsq : ∀ a : A, a * a = 1) {a : A} {Δ : GL (Fin 3) F} (hl : IsLift θ Δ 1 (α a)) (hD : DU h Δ)
    (hne : α a ≠ 1) : ∃ k, OddAt (fun u => (Δ : Matrix (Fin 3) (Fin 3) F) u u) k := by
  have h2 : (2 : F) ≠ 0 := GenLocU3Desc.two_ne_zero' h hp2
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  have hPerf : Group.IsPerfect ↥(unitarySU p f F 3) :=
    (CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)).1
  obtain ⟨c, hc⟩ := sq_scalar_of_isLift h h2 hPerf hker (by rw [← map_mul, hsq a, map_one]) hl
  have hd2 := diag_sq_eq hD.2 hc
  have hnot : ¬ ((Δ : Matrix (Fin 3) (Fin 3) F) 0 0 = (Δ : Matrix (Fin 3) (Fin 3) F) 1 1 ∧
      (Δ : Matrix (Fin 3) (Fin 3) F) 1 1 = (Δ : Matrix (Fin 3) (Fin 3) F) 2 2) := fun hs =>
    hne (eq_one_of_scalar_lift hθ hl hD.2 hs)
  exact exists_oddAt (d := fun u => (Δ : Matrix (Fin 3) (Fin 3) F) u u) (odd_index hd2 hnot)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem glAut_dgl3_inv (h : UnitaryFieldData p f F) {ψ : F ≃+* F} (hψ : ∀ c, ψ c = h.bar c)
    {ys : Fin 3 → F} (hys0 : ∀ u, ys u ≠ 0) (hysn : ∀ u, h.bar (ys u) * ys u = 1) :
    glAut ψ (dgl3 ys hys0) = (dgl3 ys hys0)⁻¹ := by
  apply Units.ext
  rw [coe_glAut_dgl3, coe_dgl3_inv]
  congr 1; ext u
  rw [hψ]
  exact eq_inv_of_mul_eq_one_left (hysn u)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem diag_mul_inv_eq {d ys : Fin 3 → F} (hys0 : ∀ u, ys u ≠ 0) (hd0 : ∀ u, d u ≠ 0)
    (hyd : ∀ u, ys u * ys u = d 0 * d u) {Δ : GL (Fin 3) F}
    (hΔ : (Δ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d) :
    Δ * (dgl3 ys hys0)⁻¹ =
      dgl3 ys hys0 * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) := by
  apply Units.ext
  simp only [Units.val_mul, coe_dgl3, coe_dgl3_inv, hΔ, Matrix.diagonal_mul_diagonal]
  congr 1; ext u
  have h1 := hys0 u
  have h2 := hd0 0
  field_simp
  linear_combination (-1 : F) * hyd u

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem frame_identity (h : UnitaryFieldData p f F) {ψ : F ≃+* F} (hψ : ∀ c, ψ c = h.bar c)
    (σ : Equiv.Perm (Fin 3)) {d ys : Fin 3 → F} (hys0 : ∀ u, ys u ≠ 0)
    (hysn : ∀ u, h.bar (ys u) * ys u = 1) (hd0 : ∀ u, d u ≠ 0)
    (hyd : ∀ u, ys u * ys u = d 0 * d u) {Δ : GL (Fin 3) F}
    (hΔ : (Δ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d) :
    Δ * glAut ψ (dgl3 ys hys0 * pgl σ) =
      (dgl3 ys hys0 * pgl σ) * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) := by
  have hSP : dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) * pgl σ =
      pgl σ * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) :=
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_dgl3]
      exact diagonal_const_comm _ _)
  calc Δ * glAut ψ (dgl3 ys hys0 * pgl σ)
      = Δ * (glAut ψ (dgl3 ys hys0) * glAut ψ (pgl σ)) := by rw [map_mul]
    _ = Δ * ((dgl3 ys hys0)⁻¹ * pgl σ) := by rw [glAut_dgl3_inv h hψ hys0 hysn, glAut_pgl]
    _ = (Δ * (dgl3 ys hys0)⁻¹) * pgl σ := by rw [mul_assoc]
    _ = (dgl3 ys hys0 * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0))) * pgl σ := by
        rw [diag_mul_inv_eq hys0 hd0 hyd hΔ]
    _ = dgl3 ys hys0 * (dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) * pgl σ) := by
        rw [mul_assoc]
    _ = dgl3 ys hys0 * (pgl σ * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0))) := by
        rw [hSP]
    _ = (dgl3 ys hys0 * pgl σ) * dgl3 (fun _ => (d 0)⁻¹) (fun _ => inv_ne_zero (hd0 0)) := by
        rw [mul_assoc]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem conj_diag_eq (σ : Equiv.Perm (Fin 3)) {ys : Fin 3 → F} (hys0 : ∀ u, ys u ≠ 0)
    {Δ : GL (Fin 3) F} (hΔ : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) :
    (dgl3 ys hys0 * pgl σ)⁻¹ * Δ * (dgl3 ys hys0 * pgl σ) = (pgl σ)⁻¹ * Δ * pgl σ := by
  have hcomm : dgl3 ys hys0 * Δ = Δ * dgl3 ys hys0 := gl_diag_comm (isDiag_dgl3 ys hys0) hΔ
  calc (dgl3 ys hys0 * pgl σ)⁻¹ * Δ * (dgl3 ys hys0 * pgl σ)
      = (pgl σ)⁻¹ * ((dgl3 ys hys0)⁻¹ * (Δ * dgl3 ys hys0)) * pgl σ := by group
    _ = (pgl σ)⁻¹ * ((dgl3 ys hys0)⁻¹ * (dgl3 ys hys0 * Δ)) * pgl σ := by rw [hcomm]
    _ = (pgl σ)⁻¹ * Δ * pgl σ := by group

theorem gammaAct_eq_top_of_exc7E8 (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : p ^ f = 7)
    {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {A : Type} [Group A]
    [Finite A] (hA : IsRank23 A) (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1)
    (hE : Exc7E8 h θ α hsq) : gammaAct α = ⊤ := by
  obtain ⟨D⟩ := nonempty_gauss h hq
  obtain ⟨a₁, ha₁, a₃, ha₃, hne₁, hne₃, hne₁₃, a, ha, Δ, ψ, hl, hψ, hD, s01, s02, s12⟩ := hE
  have hm₁ : a₁ ∈ A0 h θ α hsq := ha₁
  have hm₃ : a₃ ∈ A0 h θ α hsq := ha₃
  obtain ⟨Δ₁, hl₁, hD₁⟩ := ha₁
  obtain ⟨Δ₃, hl₃, hD₃⟩ := ha₃
  obtain ⟨k₁, hk₁⟩ := oddAt_of_A0 h hp2 hθ α hsq hl₁ hD₁ hne₁
  obtain ⟨k₃, hk₃⟩ := oddAt_of_A0 h hp2 hθ α hsq hl₃ hD₃ hne₃
  have hk13 : k₁ ≠ k₃ := by
    intro hk
    subst hk
    have hlm : IsLift θ (Δ₁ * Δ₃) 1 (α a₁ * α a₃) := by
      have := hl₁.mul hl₃
      rwa [glAut_one_apply, mul_one] at this
    have hdiag : ((Δ₁ * Δ₃ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
      rw [Units.val_mul]; exact isDiag_mul' hD₁.2 hD₃.2
    have hprod : ∀ u : Fin 3, ((Δ₁ * Δ₃ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) u u =
        (Δ₁ : Matrix (Fin 3) (Fin 3) F) u u * (Δ₃ : Matrix (Fin 3) (Fin 3) F) u u := fun u => by
      rw [Units.val_mul]; exact mul_diag_apply hD₁.2 u
    have h1 : α a₁ * α a₃ = 1 := eq_one_of_scalar_lift hθ hlm hdiag
      ⟨by rw [hprod, hprod]; exact prod_eq_of_oddAt hk₁ hk₃ 0 1,
        by rw [hprod, hprod]; exact prod_eq_of_oddAt hk₁ hk₃ 1 2⟩
    apply hne₁₃
    have hsq3 : α a₃ * α a₃ = 1 := by rw [← map_mul, hsq a₃, map_one]
    calc α a₁ = α a₁ * (α a₃ * α a₃) := by rw [hsq3, mul_one]
      _ = (α a₁ * α a₃) * α a₃ := by rw [mul_assoc]
      _ = α a₃ := by rw [h1, one_mul]
  obtain ⟨σ, hσ0, hσ2⟩ := exists_perm_of_ne k₁ k₃ hk13
  have hσ1₁ : σ 1 ≠ k₁ := fun e => absurd (σ.injective (e.trans hσ0.symm)) (by decide)
  have hσ2₁ : σ 2 ≠ k₁ := fun e => absurd (σ.injective (e.trans hσ0.symm)) (by decide)
  have hσ0₃ : σ 0 ≠ k₃ := fun e => absurd (σ.injective (e.trans hσ2.symm)) (by decide)
  have hσ1₃ : σ 1 ≠ k₃ := fun e => absurd (σ.injective (e.trans hσ2.symm)) (by decide)
  set d : Fin 3 → F := fun u => (Δ : Matrix (Fin 3) (Fin 3) F) u u with hd
  have hd0 : ∀ u, d u ≠ 0 := fun u => hD.entry_ne_zero u
  have hdn : ∀ u, h.bar (d u) * d u = 1 := fun u => hD.entry_norm u
  have hΔd : (Δ : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d := hD.2.diagonal_diag.symm
  obtain ⟨n1, hn1, hn1sq⟩ := s01
  obtain ⟨n2, hn2, hn2sq⟩ := s02
  have hne : ∀ n : F, h.bar n * n = 1 → n ≠ 0 := fun n hn h0 => by
    rw [h0] at hn; simp at hn
  set ys : Fin 3 → F := ![d 0, n1, n2] with hys
  have hys0 : ∀ u, ys u ≠ 0 := by
    intro u; fin_cases u
    · exact hd0 0
    · exact hne n1 hn1
    · exact hne n2 hn2
  have hysn : ∀ u, h.bar (ys u) * ys u = 1 := by
    intro u; fin_cases u
    · exact hdn 0
    · exact hn1
    · exact hn2
  have hyd : ∀ u, ys u * ys u = d 0 * d u := by
    intro u; fin_cases u
    · rfl
    · exact hn1sq
    · exact hn2sq
  have hyU : DU h (dgl3 ys hys0) := dgl3_du h ys hys0 hysn
  have hCu : (((dgl3 ys hys0 * pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((dgl3 ys hys0 * pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    (mem_unitaryIsom3 (h := h)).1 (mul_mem ((mem_unitaryIsom3 (h := h)).2 hyU.1)
      ((mem_unitaryIsom3 (h := h)).2 (pgl_unitary h σ)))
  have hθ' := isCover_comp_conj h hθ hCu
  have hl₁' := isLift_conj_cover h hCu hl₁ (Δ := (dgl3 ys hys0 * pgl σ)⁻¹ * Δ₁ * (dgl3 ys hys0 * pgl σ))
    (by rw [glAut_one_apply]; group)
  have hl₃' := isLift_conj_cover h hCu hl₃ (Δ := (dgl3 ys hys0 * pgl σ)⁻¹ * Δ₃ * (dgl3 ys hys0 * pgl σ))
    (by rw [glAut_one_apply]; group)
  have hla := isLift_conj_cover h hCu hl
    (frame_identity h hψ σ hys0 hysn hd0 hyd hΔd)
  rw [conj_diag_eq σ hys0 hD₁.2] at hl₁'
  rw [conj_diag_eq σ hys0 hD₃.2] at hl₃'
  have hα1 : a₁ ≠ 1 := fun e => hne₁ (by rw [e, map_one])
  have hα3 : a₃ ≠ 1 := fun e => hne₃ (by rw [e, map_one])
  have hαa : a ≠ 1 := fun e => ha (e ▸ (A0 h θ α hsq).one_mem)
  exact gammaAct_eq_top_core h hq D hθ' hA α hα1 hα3 hαa
    (fun e => hne₁₃ (by rw [e])) (fun e => ha (e ▸ hm₁)) (fun e => ha (e ▸ hm₃))
    hl₁' (isDiag_conj_pgl σ hD₁.2)
    (by rw [coe_conj_pgl, coe_conj_pgl]; exact hk₁.2 (σ 1) (σ 2) hσ1₁ hσ2₁)
    hl₃' (isDiag_conj_pgl σ hD₃.2)
    (by rw [coe_conj_pgl, coe_conj_pgl]; exact hk₃.2 (σ 0) (σ 1) hσ0₃ hσ1₃)
    hla (fun M => by
      rw [coe_dgl3]
      exact diagonal_const_comm _ M)

end GenLocU3E8Frame

end CFSG.GH74.Generic.BProg.B2
