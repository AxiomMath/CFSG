module

public import CFSG.GH74.Generic.S3.NbrBase
public import CFSG.GH74.Generic.S3.NbrIv
public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.S3.PumpDiag
public import CFSG.GH74.Generic.S3.L3Sylow
public import CFSG.GH74.Generic.S1.SymComp
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.Sporadic.Th.Max3.Relations
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups commutatorElement

structure NbrData (G : Type) [Group G] [Finite G] (t : StatedLieTag) (p f : ℕ) (x y : G)
    (Iw Iv : Subgroup G) : Prop where
  tag : t = .PSL ∨ t = .PSU
  prime : p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f
  x_inv : orderOf x = 2
  y_inv : orderOf y = 2
  comm : y * x = x * y
  ne : y ≠ x
  comp_w : IsNormCompC Iw x
  odd_w : Odd (Nat.card ↥(center ↥Iw))
  model_w : LieModel (↥Iw ⧸ center ↥Iw) t 3 p f
  Iv_le : Iv ≤ Iw
  y_Iv : y ∈ Iv
  Iv_iso : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ Nonempty (SL(2, F) ≃* Iv)
  Iv_norm : ∀ g ∈ Iw, g * y = y * g → ∀ i ∈ Iv, g * i * g⁻¹ ∈ Iv

@[expose] def LyAt {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
    NbrData G t p f x y Iw Iv → imgBar x Iw = K → IsComponent (S45.barSub y Iv)

@[expose] def LxyAt {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
    NbrData G t p f x y Iw Iv → imgBar x Iw = K →
    ∀ L : Subgroup (CentralizerBar (y * x)), IsComponent L → S45.barSub (y * x) Iv ≤ L →
      ∃ t' : StatedLieTag, (t' = .PSL ∨ t' = .PSU) ∧ LieModel ↥L t' 3 p f ∧ OnlyInvX (y * x) L

section Glue

variable {G : Type} [Group G]

theorem central_of_involution_of_equiv_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {I : Subgroup G} (e : SL(2, F) ≃* I) {y : G} (hyI : y ∈ I) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∀ i ∈ I, i * y = y * i := by
  intro i hi
  have hord : orderOf (⟨y, hyI⟩ : ↥I) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext hy2) (fun h => hy1 (congrArg Subtype.val h))
  have hy' := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e.symm ⟨y, hyI⟩).1 hord
  have hcen : (⟨y, hyI⟩ : ↥I) ∈ center ↥I := by
    rw [CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e.symm, hy']
    have h1 : e.symm (e.symm.symm (-1)) = -1 := by simp
    rw [h1]
    exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).2 (Or.inr rfl)
  have := Subgroup.mem_center_iff.1 hcen ⟨i, hi⟩
  exact congrArg Subtype.val this

end Glue

end CFSG.GH74.Generic.S3
