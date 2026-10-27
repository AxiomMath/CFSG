module

public import CFSG.GH74.Generic.Front.SpNFa
public import CFSG.GH74.Generic.Front.SpNFb
public import CFSG.GH74.Generic.Front.SpFld
public import CFSG.GH74.Generic.Front.Sch
public import CFSG.GH74.Generic.Front.Transport

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Involution

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem tau_fix (A : gsp 2 F) (σ : F ≃+* F) (h : ↥(StatedSp 2 F))
    (hh : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ =
      ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    (conjSp 2 F A * fieldSp 2 F σ) h = h := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_tau, hh, Matrix.mul_assoc]
  have : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
  rw [this, Matrix.mul_one]

omit [Finite F] in
theorem map_one_ringEquiv (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    N.map (1 : F ≃+* F) = N := by
  ext i j
  rfl

omit [Finite F] in
theorem exists_inner_of_square_multiplier (A : gsp 2 F) (μ : Fˣ)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * sp2Gram F *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (μ : F) • sp2Gram F) (ν : F) (hν : (μ : F) = ν * ν) :
    ∃ g : ↥(StatedSp 2 F), ∀ k : ↥(StatedSp 2 F), conjSp 2 F A k = g * k * g⁻¹ := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  let s : GL (Fin 2 ⊕ Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 ν⁻¹ (inv_ne_zero hν0))
  have hs : ∀ x : GL (Fin 2 ⊕ Fin 2) F, s * x = x * s := by
    intro x
    have hcen : s ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.1 hcen x).symm
  have hmem : s * (A : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := by
    refine Subgroup.subset_closure ?_
    show (((s * (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 *
        (((s * (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 0 1 (-1) 0
    have hsv : ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ν⁻¹ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      simp [s, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hsA : (((s * (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ν⁻¹ • ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      rw [Units.val_mul, hsv, Matrix.smul_mul, Matrix.one_mul]
    rw [hsA]
    have hμ' := hμ
    rw [hν] at hμ'
    calc (ν⁻¹ • ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))ᵀ *
          fromBlocks 0 1 (-1) 0 *
          (ν⁻¹ • ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
        = (ν⁻¹ * ν⁻¹) • (((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
            sp2Gram F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) := by
          simp [Matrix.transpose_smul, smul_smul]
      _ = fromBlocks 0 1 (-1) 0 := by
          rw [hμ', smul_smul]
          have : ν⁻¹ * ν⁻¹ * (ν * ν) = 1 := by field_simp
          rw [this, one_smul]
  refine ⟨⟨s * (A : GL (Fin 2 ⊕ Fin 2) F), hmem⟩, fun k => ?_⟩
  apply Subtype.ext
  rw [coe_conjSp]
  change (A : GL (Fin 2 ⊕ Fin 2) F) * k * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ =
    s * (A : GL (Fin 2 ⊕ Fin 2) F) * k * (s * (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹
  have h1 : s * ((A : GL (Fin 2 ⊕ Fin 2) F) * k * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹) * s⁻¹ =
      (A : GL (Fin 2 ⊕ Fin 2) F) * k * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ := by
    rw [hs, mul_assoc, mul_inv_cancel, mul_one]
  calc (A : GL (Fin 2 ⊕ Fin 2) F) * k * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹
      = s * ((A : GL (Fin 2 ⊕ Fin 2) F) * k * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹) * s⁻¹ := h1.symm
    _ = s * (A : GL (Fin 2 ⊕ Fin 2) F) * k * (s * (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ := by group

theorem sp_involution_good (hF : Odd (Nat.card F)) (α : MulAut ↥(StatedSp 2 F))
    (hα2 : ∀ k, α (α k) = k) (hout : ∀ g : ↥(StatedSp 2 F), ∃ k, α k ≠ g * k * g⁻¹) :
    ∃ H : Subgroup ↥(StatedSp 2 F), (∀ h ∈ H, α h = h) ∧
      (∀ z ∈ Subgroup.center ↥(StatedSp 2 F), z ∈ H) ∧
      GoodSub (ThreeModel ↥(StatedSp 2 F)) H := by
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hF
  obtain ⟨A, σ, hασ⟩ := aut_statedSp2 hF α
  have hτ2 : ∀ k, (conjSp 2 F A * fieldSp 2 F σ) ((conjSp 2 F A * fieldSp 2 F σ) k) = k := by
    intro k
    rw [← hασ]
    exact hα2 k
  obtain ⟨hσ2, c, hc⟩ := sq_one_consequences A σ hτ2
  obtain ⟨μ, hμ⟩ := A.2
  by_cases hσ : σ = 1
  ·
    subst hσ
    rw [map_one_ringEquiv] at hc
    have hμns : ¬ IsSquare (μ : F) := by
      rintro ⟨ν, hν⟩
      obtain ⟨g, hg⟩ := exists_inner_of_square_multiplier A μ hμ ν hν
      obtain ⟨k, hk⟩ := hout g
      apply hk
      have h1 : (conjSp 2 F A * fieldSp 2 F 1) k = conjSp 2 F A k := by
        rw [MulAut.mul_apply, map_one, MulAut.one_apply]
      rw [hασ, h1, hg k]
    have hμμ : (μ : F) * μ = c * c := by
      have hAJ := hμ
      generalize ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = M at hAJ hc
      have e1 : (M * M)ᵀ * sp2Gram F * (M * M) = ((μ : F) * μ) • sp2Gram F := by
        calc (M * M)ᵀ * sp2Gram F * (M * M) = Mᵀ * (Mᵀ * sp2Gram F * M) * M := by
              simp only [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = Mᵀ * ((μ : F) • sp2Gram F) * M := by rw [hAJ]
          _ = (μ : F) • (Mᵀ * sp2Gram F * M) := by
              simp [Matrix.mul_assoc]
          _ = ((μ : F) * μ) • sp2Gram F := by rw [hAJ, smul_smul]
      have e2 : (M * M)ᵀ * sp2Gram F * (M * M) = (c * c) • sp2Gram F := by
        rw [hc]
        simp [Matrix.transpose_smul, smul_smul]
      have e3 := e1.symm.trans e2
      have e4 := congrFun (congrFun e3 (Sum.inl 0)) (Sum.inr 0)
      simpa [sp2Gram] using e4
    have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hμ0 (mul_self_eq_zero.1 (hμμ.trans (mul_zero 0)))
    have hsq : (μ : F) = c ∨ (μ : F) = -c := by
      have h' : ((μ : F) - c) * ((μ : F) + c) = 0 := by linear_combination hμμ
      rcases mul_eq_zero.1 h' with h | h
      · left
        linear_combination h
      · right
        linear_combination h
    have hNF : TensorNF ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      by_cases hcs : IsSquare c
      · obtain ⟨ν, hν⟩ := hcs
        have hν0 : ν ≠ 0 := by
          rintro rfl
          exact hc0 (by simpa using hν)
        have hμneg : (μ : F) = -c := by
          rcases hsq with h | h
          · exact absurd ⟨ν, h.trans hν⟩ hμns
          · exact h
        refine tensorNF_split_minus h2 _ ν hν0 ?_ ?_
        · rw [hc, hν, pow_two]
        · rw [hμ, hμneg, hν, pow_two]
      · rcases hsq with h | h
        · exact tensorNF_nonsplit_plus h2 _ c hcs hc (by rw [hμ, h])
        · exact tensorNF_nonsplit_minus h2 _ c hcs hc (by rw [hμ, h])
    obtain ⟨H, hcomm, hZ, hgood⟩ := exists_good_of_tensorNF hF _ hNF
    refine ⟨H, fun h hh => ?_, hZ, hgood⟩
    rw [hασ]
    exact tau_fix A 1 h (by rw [map_one_ringEquiv]; exact hcomm h hh)
  ·
    obtain ⟨H, hfix, hZ, hgood⟩ := exists_good_fixed_of_field_involution hF σ hσ hσ2 A c hc
    refine ⟨H, fun h hh => ?_, hZ, hgood⟩
    rw [hασ]
    exact hfix h hh

end Involution

theorem spOuterInvolution : SpOuterInvolution := by
  intro F _ _ hF X _ _ K _ he hcent _hgen v hv2 hvK
  obtain ⟨e⟩ := he
  let c : MulAut ↥K := MulAut.conjNormal v
  let α : MulAut ↥(StatedSp 2 F) := MulAut.congr e c
  have hcv : ∀ n : ↥K, ((c n : ↥K) : X) = v * (n : X) * v⁻¹ := fun n => rfl
  have hcc : ∀ n : ↥K, c (c n) = n := by
    intro n
    apply Subtype.ext
    rw [hcv, hcv]
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    rw [hvinv]
    calc v * (v * (n : X) * v) * v = (v * v) * (n : X) * (v * v) := by group
      _ = n := by rw [hv2]; simp
  have hα : ∀ k, α k = e (c (e.symm k)) := fun k => rfl
  have hα2 : ∀ k, α (α k) = k := by
    intro k
    rw [hα, hα, e.symm_apply_apply, hcc, e.apply_symm_apply]
  have hout : ∀ g : ↥(StatedSp 2 F), ∃ k, α k ≠ g * k * g⁻¹ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hcon
    apply hvK
    refine mem_of_conjNormal_inner hcent (k := e.symm g) ?_
    ext n
    have h1 := hg (e n)
    rw [hα, e.symm_apply_apply] at h1
    have h2 : c n = e.symm (g * e n * g⁻¹) := by rw [← h1, e.symm_apply_apply]
    rw [h2]
    simp [MulAut.conj_apply]
  obtain ⟨H, hfix, hZ, hgood⟩ := sp_involution_good hF α hα2 hout
  refine ⟨(H.map e.symm.toMonoidHom).map K.subtype, ?_, ?_, ?_⟩
  · refine le_inf ?_ ?_
    · rintro _ ⟨_, _, rfl⟩
      exact Subtype.mem _
    · rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfix h hh
      rw [hα] at h1
      have h2 : c (e.symm h) = e.symm h := by
        have := congrArg e.symm h1
        simpa using this
      have h3 := congrArg Subtype.val h2
      rw [hcv] at h3
      show ((e.symm h : ↥K) : X) * v = v * ((e.symm h : ↥K) : X)
      calc ((e.symm h : ↥K) : X) * v = (v * ((e.symm h : ↥K) : X) * v⁻¹) * v := by rw [h3]
        _ = v * ((e.symm h : ↥K) : X) := by group
  · intro z hz
    refine ⟨e.symm (e z), ⟨e z, hZ (e z) ((mem_center_iff_of_mulEquiv e z).2 hz), rfl⟩, ?_⟩
    simp
  · have h1 := goodSub_map e.symm.toMonoidHom (hgood.mono (ThreeModel.of_mulEquiv e.symm))
    exact goodSub_map K.subtype h1

end CFSG.GH74.Generic
