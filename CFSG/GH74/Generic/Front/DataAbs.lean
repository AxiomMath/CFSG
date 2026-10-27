module

public import CFSG.GH74.Generic.Front.Defs
public import CFSG.GH74.L5U5.ModelsInvolution

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd
  CFSG.ClassicalInvolution Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def q8q8Diag (ρ : Q8 →* GL (Fin 2) F) : Q8 × Q8 →* GL (Fin 4) F :=
  (diagGLHom F).comp (ρ.prodMap ρ)

theorem q8q8Diag_apply (ρ : Q8 →* GL (Fin 2) F) (g h : Q8) :
    q8q8Diag ρ (g, h) = diagGL (ρ g) (ρ h) := rfl

theorem q8q8Diag_mem (M : ModelData F) {ρ : Q8 →* GL (Fin 2) F} (hρ : ∀ g, ρ g ∈ M.H2)
    (x : Q8 × Q8) : q8q8Diag ρ x ∈ M.K4 := by
  obtain ⟨h1, d1⟩ := (M.mem_H2 _).1 (hρ x.1)
  obtain ⟨h2, d2⟩ := (M.mem_H2 _).1 (hρ x.2)
  change diagGL (ρ x.1) (ρ x.2) ∈ M.K4
  rw [M.diagGL_mem_K4_iff]
  exact ⟨h1, h2, by rw [d1, d2, one_mul]⟩

theorem commutator_sup_eq_of_perfect {G : Type*} [Group G] {A B : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem hg hh) ((A ⊔ B).inv_mem hg))
      ((A ⊔ B).inv_mem hh)
  · refine sup_le ?_ ?_
    · calc A = ⁅A, A⁆ := hA.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc B = ⁅B, B⁆ := hB.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem goodSub_sup_of_perfect (T : Prop) {G : Type*} [Group G] {A B : Subgroup G}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : GoodSub T (A ⊔ B) :=
  Or.inl (commutator_sup_eq_of_perfect hA hB)

theorem commutator_J2_eq_self (M : ModelData F) {F' : Type} [Field F'] [Finite F']
    (h4 : 4 ≤ Nat.card F') (e : SL(2, F') ≃* M.H2) : ⁅M.J2, M.J2⁆ = M.J2 :=
  Subgroup.isPerfect_iff.1 (isPerfect_of_equiv_sl2 h4 (M.J2EquivH2.trans e.symm))

theorem commutator_J4_eq_self (M : ModelData F) {F' : Type} [Field F'] [Finite F']
    (h4 : 4 ≤ Nat.card F') (e : SL(2, F') ≃* M.H2) : ⁅M.J4, M.J4⁆ = M.J4 :=
  Subgroup.isPerfect_iff.1 (isPerfect_of_equiv_sl2 h4 (M.J4EquivH2.trans e.symm))

theorem goodSub_J2_sup_J4 (M : ModelData F) (T : Prop) {F' : Type} [Field F'] [Finite F']
    (h4 : 4 ≤ Nat.card F') (e : SL(2, F') ≃* M.H2) : GoodSub T (M.J2 ⊔ M.J4) :=
  goodSub_sup_of_perfect T (commutator_J2_eq_self M h4 e) (commutator_J4_eq_self M h4 e)

theorem blk4_negOne_one_eq :
    (blk4 (-1) 1 : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock, Matrix.reindex_apply,
      Matrix.submatrix_apply, e0, e1, e2, e3]

theorem yGL_matrix :
    ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  rw [yGL, coe_diagGL, Units.val_neg, Units.val_one]
  exact blk4_negOne_one_eq

theorem exists_conj_yK_of_matrix (M : ModelData F) (t : ↥M.K4) (g : GL (Fin 4) F) (hg : g ∈ M.K4)
    (hTP : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F)) :
    ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK := by
  refine ⟨⟨g⁻¹, M.K4.inv_mem hg⟩, ?_⟩
  apply Subtype.ext
  change g⁻¹ * (t : GL (Fin 4) F) * (g⁻¹)⁻¹ = yGL F
  rw [inv_inv]
  have h1 : (t : GL (Fin 4) F) * g = g * yGL F := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hTP, yGL_matrix]
  calc g⁻¹ * (t : GL (Fin 4) F) * g = g⁻¹ * ((t : GL (Fin 4) F) * g) := mul_assoc _ _ _
    _ = g⁻¹ * (g * yGL F) := by rw [h1]
    _ = yGL F := by rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem hone_of_model (M : ModelData F)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hmat : ∀ t : ↥M.K4,
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((t : GL (Fin 4) F) : Matrix _ _ F) = 1 →
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 1 →
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ -1 →
      ∃ g : GL (Fin 4) F, g ∈ M.K4 ∧
        ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
          (g : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F)) :
    ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK := by
  intro t ht _ hc
  rw [hcenter] at hc
  push Not at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hT : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have := congrArg (fun u : ↥M.K4 => ((u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ht
    simpa using this
  have hT1 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 1 := fun h => hc1 (Units.ext h)
  have hT2 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ -1 := fun h =>
    hc2 (by rw [xGL_eq_neg_one]; exact Units.ext (by simpa using h))
  obtain ⟨g, hg, hTg⟩ := hmat t hT hT1 hT2
  exact exists_conj_yK_of_matrix M t g hg hTg

theorem frontData0_of_model (M : ModelData F) (ρ : Q8 →* GL (Fin 2) F)
    (hρ : ∀ g, ρ g ∈ M.H2) (hinj : Function.Injective ρ) (hz : ρ (QuaternionGroup.a 2) = -1)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK)
    (hgood : GoodSub (ThreeModel ↥M.K4) (M.J2 ⊔ M.J4)) :
    Nonempty (FrontData0 ↥M.K4) := by
  let φ : Q8 × Q8 →* ↥M.K4 := (q8q8Diag ρ).codRestrict M.K4 (q8q8Diag_mem M hρ)
  have hφ : ∀ g h : Q8, ((φ (g, h) : ↥M.K4) : GL (Fin 4) F) = diagGL (ρ g) (ρ h) :=
    fun g h => rfl
  have hφz : φ (QuaternionGroup.a 2, 1) = M.yK := by
    apply Subtype.ext
    rw [hφ, hz, map_one]
    rfl
  refine ⟨⟨φ, M.wK, M.J2 ⊔ M.J4, ?_, ?_, ?_, ?_, ?_, ?_, hgood⟩⟩
  · intro a b hab
    have h := diagGL_inj (congrArg Subtype.val hab)
    exact Prod.ext (hinj h.1) (hinj h.2)
  · exact Subtype.ext swapGL_mul_self
  · intro g h
    apply Subtype.ext
    change swapGL F * diagGL (ρ g) (ρ h) * (swapGL F)⁻¹ = diagGL (ρ h) (ρ g)
    exact swapGL_mul_diagGL_mul_inv _ _
  · intro t ht h1 hc
    rw [hφz]
    exact hone t ht h1 hc
  · rintro _ ⟨⟨g, h⟩, rfl⟩
    have hg : (⟨blkL F (ρ g), M.blkL_mem_K4 (hρ g)⟩ : ↥M.K4) ∈ M.J2 :=
      ModelData.blkL_mem_J2 (hρ g)
    have hh : (⟨blkR F (ρ h), M.blkR_mem_K4 (hρ h)⟩ : ↥M.K4) ∈ M.J4 :=
      ModelData.blkR_mem_J4 (hρ h)
    have hprod : φ (g, h) =
        (⟨blkL F (ρ g), M.blkL_mem_K4 (hρ g)⟩ : ↥M.K4) *
          ⟨blkR F (ρ h), M.blkR_mem_K4 (hρ h)⟩ :=
      Subtype.ext (diagGL_eq_blkL_mul_blkR _ _)
    rw [hprod]
    exact Subgroup.mul_mem_sup hg hh
  · rw [hφz]
    exact sup_le M.J2_le_centralizer M.J4_le_centralizer

end CFSG.GH74.Generic
