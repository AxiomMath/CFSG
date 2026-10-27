module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Frame
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups commutatorElement

namespace U3Frame

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal] {R : Subgroup A} {S : Sylow 2 R} {z : A}
  {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} (F : U3Frame T z p f h)

theorem J_le : F.J ≤ T ⊓ Subgroup.centralizer ({z} : Set A) := by
  rw [← F.hrange]
  exact Subgroup.map_le_range _ _

theorem comm_le :
    ⁅T ⊓ Subgroup.centralizer ({z} : Set A), T ⊓ Subgroup.centralizer ({z} : Set A)⁆ ≤ F.J := by
  rw [← F.hrange]
  exact commutator_range_le F.π

theorem J_perfect {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀)
    (eJ : ↥(slPart (GU2Stated (p ^ f) K)) ≃* SL(2, F₀)) : Group.IsPerfect ↥F.J := by
  haveI : Group.IsPerfect ↥(slPart (GU2Stated (p ^ f) K)) := isPerfect_of_equiv_sl2 h4 eJ
  exact Group.IsPerfect.map F.π

@[expose] noncomputable def Φ {F₀ : Type} [Field F₀] (eJ : ↥(slPart (GU2Stated (p ^ f) K)) ≃* SL(2, F₀)) :
    SL(2, F₀) →* MulAut ↥T :=
  (MulAut.conjNormal (H := T)).comp
    ((F.π.comp (slPart (GU2Stated (p ^ f) K)).subtype).comp eJ.symm.toMonoidHom)

theorem Φ_injective {F₀ : Type} [Field F₀] (eJ : ↥(slPart (GU2Stated (p ^ f) K)) ≃* SL(2, F₀))
    (hC : Subgroup.centralizer (T : Set A) = ⊥) : Function.Injective (F.Φ eJ) :=
  (conjNormal_injective hC).comp ((injective_slPart F.hk).comp eJ.symm.injective)

theorem Φ_range {F₀ : Type} [Field F₀] (eJ : ↥(slPart (GU2Stated (p ^ f) K)) ≃* SL(2, F₀)) :
    (F.Φ eJ).range = F.J.map (MulAut.conjNormal (H := T)) := by
  ext x
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨F.π (eJ.symm B : ↥(slPart (GU2Stated (p ^ f) K))), ⟨_, (eJ.symm B).2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨eJ ⟨c, hc⟩, ?_⟩
    show MulAut.conjNormal (F.π ((eJ.symm (eJ ⟨c, hc⟩) : ↥(slPart (GU2Stated (p ^ f) K))) :
      ↥(GU2Stated (p ^ f) K))) = _
    rw [MulEquiv.symm_apply_apply]

theorem J_centralizes (hRJ : R ≤ Subgroup.centralizer ((F.J : Subgroup A) : Set A)) :
    ∀ y ∈ F.J, ∀ s ∈ sylowSet S, y * s = s * y := by
  intro y hy s hs
  exact Subgroup.mem_centralizer_iff.mp (hRJ (mem_sylowSet_le S hs)) y hy

end U3Frame

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3
