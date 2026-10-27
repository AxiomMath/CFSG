module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Red

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
open scoped commutatorElement

section Hom

variable {A : Type*} [Group A] [Finite A] {T : Subgroup A} [T.Normal]
  (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
  (hC : Subgroup.centralizer (T : Set A) = ⊥)

include hT hab hC

@[expose] noncomputable def restrictHom : MulAut A →* MulAut ↥T where
  toFun φ := restrictAut hT hab hC φ
  map_one' := by
    ext x
    rfl
  map_mul' φ ψ := by
    ext x
    rfl

theorem restrictHom_apply (φ : MulAut A) (x : ↥T) :
    ((restrictHom hT hab hC φ x : ↥T) : A) = φ x := rfl

theorem restrictHom_conj (φ : MulAut A) (s : A) :
    restrictHom hT hab hC φ * MulAut.conjNormal s * (restrictHom hT hab hC φ)⁻¹ =
      MulAut.conjNormal (φ s) := by
  ext x
  have h1 : ((restrictHom hT hab hC φ)⁻¹ x : ↥T) = ⟨φ.symm x, by
      rw [mem_iff_apply_mem hT hab hC φ, MulEquiv.apply_symm_apply]
      exact x.2⟩ := rfl
  simp only [MulAut.mul_apply, MulAut.conjNormal_apply, restrictHom_apply]
  rw [h1]
  simp

theorem restrictHom_conj_self (a : A) :
    restrictHom hT hab hC (MulAut.conj a) = MulAut.conjNormal a := by
  ext x
  rw [restrictHom_apply, MulAut.conj_apply, MulAut.conjNormal_apply]

end Hom

section QC

variable {Q : Type*} [Group Q]

@[expose] def qcHom : MulAut Q →* MulAut (Q ⧸ Subgroup.center Q) where
  toFun φ := quotCenterAut φ
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x => simp
  map_mul' φ ψ := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x => simp

theorem qcHom_conj (q : Q) :
    qcHom (MulAut.conj q) = MulAut.conj (QuotientGroup.mk q : Q ⧸ Subgroup.center Q) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x => simp [qcHom, MulAut.conj_apply]

theorem qcHom_apply_mk (φ : MulAut Q) (x : Q) :
    qcHom φ (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) = QuotientGroup.mk (φ x) := by
  simp [qcHom]

end QC

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
