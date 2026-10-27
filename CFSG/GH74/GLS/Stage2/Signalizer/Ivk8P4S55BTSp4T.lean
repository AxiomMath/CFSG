module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4P
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (conjAut_mul_fieldAut_eq_one_iff)

variable {F : Type} [Field F]

theorem mulVec_mem_flag_of_conj {N : Submodule F (Fin 2 ⊕ Fin 2 → F)} {d : ℕ}
    {g : StatedSp 2 F} (hg : (flag 2 F d).map (spAct g) = N) {A B : GL (Fin 2 ⊕ Fin 2) F}
    (hA : ∀ v ∈ N, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ N)
    (hB : (g : GL (Fin 2 ⊕ Fin 2) F) * B = A * g) :
    ∀ v ∈ flag 2 F d, (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ flag 2 F d := by
  intro v hv
  have h1 : (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ N := by
    rw [← hg]
    exact ⟨v, hv, rfl⟩
  have h2 := hA _ h1
  rw [← hg] at h2
  obtain ⟨w, hw, hwe⟩ := h2
  have hgB : (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        ((B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) =
      (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w := by
    rw [mulVec_mulVec, ← Units.val_mul, hB, Units.val_mul, ← mulVec_mulVec]
    exact hwe.symm
  have hBv : (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = w := by
    have := congrArg (fun u => ((((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)⁻¹ :
      GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ u) hgB
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left, inv_mul_cancel,
      Units.val_one, one_mulVec] at this
    exact this
  rw [hBv]
  exact hw

theorem toBlocks₂₁_eq_zero_of_flag {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ v ∈ flag 2 F 2, M *ᵥ v ∈ flag 2 F 2) : M.toBlocks₂₁ = 0 := by
  ext i j
  have hv : (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → F) ∈ flag 2 F 2 := by
    rw [flag, ite_eq_left (le_refl 2), mem_isoFlag]
    exact ⟨fun k => by simp, fun k hk => absurd k.isLt (by omega)⟩
  have hm := h _ hv
  rw [flag, ite_eq_left (le_refl 2), mem_isoFlag] at hm
  simpa [mulVec_single_one, Matrix.toBlocks₂₁] using hm.1 i

theorem exists_mulVec_e0 {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ v ∈ flag 2 F 1, M *ᵥ v ∈ flag 2 F 1) : ∃ c : F, M *ᵥ e0 = c • e0 := by
  have hv : (e0 : Fin 2 ⊕ Fin 2 → F) ∈ flag 2 F 1 := by
    rw [flag, ite_eq_left (show 1 ≤ 2 by norm_num), mem_isoFlag]
    refine ⟨fun k => by simp, fun k hk => ?_⟩
    fin_cases k
    · simp at hk
    · simp
  have hm := h _ hv
  rw [flag, ite_eq_left (show 1 ≤ 2 by norm_num), mem_isoFlag] at hm
  refine ⟨(M *ᵥ e0) (Sum.inl 0), ?_⟩
  ext i
  rcases i with i | i
  · fin_cases i
    · simp
    · simpa using hm.2 1 (by simp)
  · simpa using hm.1 i

theorem exists_pair_four {G : Type} [Group G] {Q : Subgroup G} (hQ : IVK.IsFourSubgroup Q) :
    ∃ a ∈ Q, ∃ b ∈ Q, a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b * (a * b) = 1 := by
  classical
  have := hQ.1
  have hsq : ∀ x ∈ Q, x * x = 1 := fun x hx => by
    simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Q) x hx
  have key : ∀ a : G, ∃ b ∈ Q, b ≠ 1 ∧ b ≠ a := by
    intro a
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun x : ↥Q => decide ((x : G) = 1)) := by
      intro x y hxy
      apply Subtype.ext
      by_cases hx : (x : G) = 1
      · have hy : (y : G) = 1 := by simpa [hx] using hxy.symm
        rw [hx, hy]
      · have hy : (y : G) ≠ 1 := by simpa [hx] using hxy.symm
        rw [hcon x x.2 hx, hcon y y.2 hy]
    have h4 := Nat.card_le_card_of_injective _ hinj
    rw [hQ.2, Nat.card_eq_fintype_card, Fintype.card_bool] at h4
    omega
  obtain ⟨a, ha, ha1, -⟩ := key 1
  obtain ⟨b, hb, hb1, hba⟩ := key a
  refine ⟨a, ha, b, hb, ha1, hb1, fun hab => hba ?_, hsq a ha, hsq b hb,
    hsq _ (mul_mem ha hb)⟩
  calc b = a * (a * b) := by rw [← mul_assoc, hsq a ha, one_mul]
    _ = a := by rw [hab, mul_one]

variable [Finite F]

theorem sq_smul_of_conjAut {A : gsp 2 F} (h : conjAut 2 F A * conjAut 2 F A = 1) :
    ∃ l : F, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = l • 1 := by
  have h' := (conjAut_mul_fieldAut_eq_one_iff (K := F) (r := 2) (by norm_num) (A * A) 1).mp
    (by rw [map_one, mul_one, map_mul, h])
  obtain ⟨-, c, hc⟩ := h'
  refine ⟨c, ?_⟩
  rw [← Units.val_mul, ← Subgroup.coe_mul, hc, Matrix.GeneralLinearGroup.coe_scalar,
    smul_one_eq_diagonal]
  rfl

theorem ne_smul_of_conjAut {A : gsp 2 F} (h : conjAut 2 F A ≠ 1) :
    ∀ l : F, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1 := by
  intro l hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    have hu := ((A : GL (Fin 2 ⊕ Fin 2) F)).isUnit
    rw [zero_smul] at hl
    rw [Matrix.isUnit_iff_isUnit_det, hl, det_zero] at hu
    exact not_isUnit_zero hu
  apply h
  have := (conjAut_mul_fieldAut_eq_one_iff (K := F) (r := 2) (by norm_num) A 1).mpr
    ⟨rfl, Units.mk0 l hl0, Units.ext (by
      rw [hl, Matrix.GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
      rfl)⟩
  rwa [map_one, mul_one] at this

omit [Finite F] in
theorem exists_central_of_conjAut {A : gsp 2 F} {y : StatedSp 2 F}
    (h : conjAut 2 F A (proj 2 F y) = proj 2 F y) :
    ∃ s ∈ center (GL (Fin 2 ⊕ Fin 2) F), (A : GL (Fin 2 ⊕ Fin 2) F) *
      ((y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ = s * y := by
  rw [conjAut_proj] at h
  have hk : conjSp 2 F A y * y⁻¹ ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hk :)
  refine ⟨Matrix.GeneralLinearGroup.scalar _ c, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  · rw [hc, Subgroup.coe_mul, coe_conjSp, Subgroup.coe_inv]
    group

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
