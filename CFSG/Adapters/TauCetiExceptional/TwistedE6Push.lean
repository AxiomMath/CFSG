module

public import CFSG.Adapters.TauCetiExceptional.TwistedE6Bridge
public import CFSG.Adapters.TauCetiExceptional.TwistedE6Dual
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdKer
public import CFSG.Adapters.TauCetiExceptional.MinusculeSignsE

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
open CFSG.TauCetiBridge.Minuscule

variable {S : AdjSigns .E6} (hS : S.check e6Data = true) (L : Type) [Field L]

theorem ulRange_isZeroOfIdentities
    (z : Matrix.GeneralLinearGroup (Fin 27) L)
    (hz : z ∈ ulRange L) :
    IsZeroOfIdentities e6Data_valid e6Match.lab (z : Matrix (Fin 27) (Fin 27) L) :=
  fun P hP => ulRange_isZero L hz P hP

abbrev e6Ad :
    ↥(TauCeti.E6DoubledMinuscule.points L) →* ModGL .E6 L :=
  (adCarrier e6Data_valid posDef_cartan_E6 hS e6Match.lab L (ulRange L)
    (ulRange_isZeroOfIdentities L)).comp (ulHom L).rangeRestrict

theorem e6Ad_inl
    (i : Fin 6) (c : L) :
    e6Ad hS L (TauCeti.E6DoubledMinuscule.rootSubgroupPoints (.inl i) L
      (Multiplicative.ofAdd c)) = xUnit .E6 L i c := by
  have hmem : toMat e6Match.lab L (rootUnit e6Data_valid L (Pi.single (e6Match.node i) 1) c) ∈
      ulRange L := by
    rw [← e6_rootSubgroupPoints_inl, ← ulHom_rootSubgroupPoints]
    exact ⟨_, rfl⟩
  have e : (ulHom L).rangeRestrict (TauCeti.E6DoubledMinuscule.rootSubgroupPoints (.inl i) L
      (Multiplicative.ofAdd c)) = ⟨_, hmem⟩ :=
    Subtype.ext ((ulHom_rootSubgroupPoints L _ _).trans (e6_rootSubgroupPoints_inl L i c))
  rw [MonoidHom.comp_apply, e, adCarrier_rootUnit_single e6Data_valid posDef_cartan_E6 hS
    e6Match.lab L (ulRange L) (ulRange_isZeroOfIdentities L) (e6Match.node i) c hmem,
    e6Match_node]

theorem e6Ad_inr
    (i : Fin 6) (c : L) :
    e6Ad hS L (TauCeti.E6DoubledMinuscule.rootSubgroupPoints (.inr i) L
      (Multiplicative.ofAdd c)) = yUnit .E6 L i c := by
  have hmem : toMat e6Match.lab L (rootUnit e6Data_valid L (-Pi.single (e6Match.node i) 1) c) ∈
      ulRange L := by
    rw [← e6_rootSubgroupPoints_inr, ← ulHom_rootSubgroupPoints]
    exact ⟨_, rfl⟩
  have e : (ulHom L).rangeRestrict (TauCeti.E6DoubledMinuscule.rootSubgroupPoints (.inr i) L
      (Multiplicative.ofAdd c)) = ⟨_, hmem⟩ :=
    Subtype.ext ((ulHom_rootSubgroupPoints L _ _).trans (e6_rootSubgroupPoints_inr L i c))
  rw [MonoidHom.comp_apply, e, adCarrier_rootUnit_neg_single e6Data_valid posDef_cartan_E6 hS
    e6Match.lab L (ulRange L) (ulRange_isZeroOfIdentities L) (e6Match.node i) c hmem,
    e6Match_node]

theorem e6Ad_zeros
    (z : ↥(TauCeti.E6DoubledMinuscule.points L))
    (P : MvPolynomial (Fin (BigCell.nLab .E6) × Fin (BigCell.nLab .E6)) ℤ)
    (hP : BigCell.VanishesOnRat .E6 P) :
    BigCell.evalMat (BigCell.natMat .E6 L (e6Ad hS L z : Module.End L (RootModule .E6 L))) P =
      0 :=
  vanishes_adCarrier e6Data_valid posDef_cartan_E6 hS e6Match.lab L (ulRange L)
    (ulRange_isZeroOfIdentities L) _ P hP

theorem toMat_e6_rootUnit_single_eq
    (i : Fin (Tag.rank .E6)) :
    ((toMat e6Match.lab L (rootUnit e6Data_valid L (Pi.single i 1) 1) :
      Matrix.GeneralLinearGroup (Fin 27) L) : Matrix (Fin 27) (Fin 27) L) =
        1 + (E6Minuscule.raisingMatrix i).map (Int.cast : ℤ → L) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 6, j = i := ⟨i, rfl⟩
  have h := e6_rootSubgroupPoints_inl L j 1
  rw [e6Match_node] at h
  rw [← h, E6Minuscule.coe_rootSubgroupPoints_inl, toAdd_ofAdd, one_smul,
    raisingMatrix_eq_weightTable]

theorem toMat_e6_rootUnit_neg_single_eq
    (i : Fin (Tag.rank .E6)) :
    ((toMat e6Match.lab L (rootUnit e6Data_valid L (-Pi.single i 1) 1) :
      Matrix.GeneralLinearGroup (Fin 27) L) : Matrix (Fin 27) (Fin 27) L) =
        1 + (E6Minuscule.loweringMatrix i).map (Int.cast : ℤ → L) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 6, j = i := ⟨i, rfl⟩
  have h := e6_rootSubgroupPoints_inr L j 1
  rw [e6Match_node] at h
  rw [← h, E6Minuscule.coe_rootSubgroupPoints_inr, toAdd_ofAdd, one_smul,
    loweringMatrix_eq_weightTable]

@[expose] def e6PushDown :
    E6PushDown L where
  π := e6Ad e6Signs_check L
  π_u := e6Ad_inl e6Signs_check L
  π_v := e6Ad_inr e6Signs_check L
  zeros := e6Ad_zeros e6Signs_check L
  ker_iff z := by
    rw [commute_iff_ulBlock]
    refine (adCarrier_eq_one_iff' e6Data_valid e6Match.lab L posDef_cartan_E6 e6Signs_check
      (ulRange L) (ulRange_isZeroOfIdentities L) ((ulHom L).rangeRestrict z)).trans
        (forall_congr' fun i => ?_)
    rw [toMat_e6_rootUnit_single_eq, toMat_e6_rootUnit_neg_single_eq, MonoidHom.coe_rangeRestrict,
      coe_ulHom]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj]

theorem twistedBridge_twistedE6
    : TwistedBridge .E6 LieTypeIndex.twistedE6 :=
  twistedBridge_twistedE6_of fun q hv _ => e6PushDown (e6Closure q hv)

end CFSG.TauCetiBridge.Twisted
