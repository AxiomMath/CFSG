module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Bridge
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Signs
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdKer

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
open CFSG.TauCetiBridge.Minuscule

variable (L : Type) [Field L]

theorem d4_points_isZero
    (z : Matrix.GeneralLinearGroup (Fin 24) L) (hz : z ∈ D4Tripled.points L) :
    IsZeroOfIdentities d4tData_valid d4Match.lab (z : Matrix (Fin 24) (Fin 24) L) :=
  fun P hP => d4_evalMat_eq_zero P hP L z hz

abbrev d4Ad :
    ↥(D4Tripled.points L) →* ModGL .D4 L :=
  adCarrier d4tData_valid posDef_cartan_D4 d4tSigns_check d4Match.lab L (D4Tripled.points L)
    (d4_points_isZero L)

theorem d4Ad_inl
    (i : Fin 4) (c : L) :
    d4Ad L (D4Tripled.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c)) =
      xUnit .D4 L (d4Node i) c := by
  have hmem : toMat d4Match.lab L (rootUnit d4tData_valid L (Pi.single (d4Match.node i) 1) c) ∈
      D4Tripled.points L := by
    rw [← d4_rootSubgroupPoints_inl]
    exact (D4Tripled.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c)).2
  have e : D4Tripled.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c) = ⟨_, hmem⟩ :=
    Subtype.ext (d4_rootSubgroupPoints_inl L i c)
  rw [e]
  exact adCarrier_rootUnit_single d4tData_valid posDef_cartan_D4 d4tSigns_check d4Match.lab L
    (D4Tripled.points L) (d4_points_isZero L) (d4Match.node i) c hmem

theorem d4Ad_inr
    (i : Fin 4) (c : L) :
    d4Ad L (D4Tripled.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c)) =
      yUnit .D4 L (d4Node i) c := by
  have hmem : toMat d4Match.lab L (rootUnit d4tData_valid L (-Pi.single (d4Match.node i) 1) c) ∈
      D4Tripled.points L := by
    rw [← d4_rootSubgroupPoints_inr]
    exact (D4Tripled.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c)).2
  have e : D4Tripled.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c) = ⟨_, hmem⟩ :=
    Subtype.ext (d4_rootSubgroupPoints_inr L i c)
  rw [e]
  exact adCarrier_rootUnit_neg_single d4tData_valid posDef_cartan_D4 d4tSigns_check d4Match.lab L
    (D4Tripled.points L) (d4_points_isZero L) (d4Match.node i) c hmem

theorem d4Ad_zeros
    (z : ↥(D4Tripled.points L))
    (P : MvPolynomial (Fin (BigCell.nLab .D4) × Fin (BigCell.nLab .D4)) ℤ)
    (hP : BigCell.VanishesOnRat .D4 P) :
    BigCell.evalMat (BigCell.natMat .D4 L (d4Ad L z : Module.End L (RootModule .D4 L))) P = 0 :=
  vanishes_adCarrier d4tData_valid posDef_cartan_D4 d4tSigns_check d4Match.lab L
    (D4Tripled.points L) (d4_points_isZero L) z P hP

theorem toMat_rootUnit_single_eq
    (i : Fin (Tag.rank .D4)) :
    ((toMat d4Match.lab L (rootUnit d4tData_valid L (Pi.single i 1) 1) :
      Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) = 1 + d4E L i := by
  have h := d4_rootSubgroupPoints_inl L (d4Node.symm i) 1
  have hn : d4Match.node (d4Node.symm i) = i := Equiv.apply_symm_apply _ _
  rw [hn] at h
  rw [← h]
  have hc := D4PushDown.coe_u (L := L) i 1
  rw [one_smul] at hc
  exact hc

theorem toMat_rootUnit_neg_single_eq
    (i : Fin (Tag.rank .D4)) :
    ((toMat d4Match.lab L (rootUnit d4tData_valid L (-Pi.single i 1) 1) :
      Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) = 1 + d4F L i := by
  have h := d4_rootSubgroupPoints_inr L (d4Node.symm i) 1
  have hn : d4Match.node (d4Node.symm i) = i := Equiv.apply_symm_apply _ _
  rw [hn] at h
  rw [← h]
  have hc := D4PushDown.coe_v (L := L) i 1
  rw [one_smul] at hc
  exact hc

@[expose] def d4PushDown :
    D4PushDown L where
  π := d4Ad L
  π_u := d4Ad_inl L
  π_v := d4Ad_inr L
  zeros := d4Ad_zeros L
  ker_iff z := by
    rw [adCarrier_eq_one_iff' d4tData_valid d4Match.lab L posDef_cartan_D4 d4tSigns_check
      (D4Tripled.points L) (d4_points_isZero L) z]
    refine forall_congr' fun i => ?_
    rw [toMat_rootUnit_single_eq, toMat_rootUnit_neg_single_eq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj]

theorem twistedBridge_trialityD4
    : TwistedBridge .D4 LieTypeIndex.trialityD4 :=
  twistedBridge_trialityD4_of fun q hv _ => d4PushDown (d4Closure q hv)

end CFSG.TauCetiBridge.Twisted
