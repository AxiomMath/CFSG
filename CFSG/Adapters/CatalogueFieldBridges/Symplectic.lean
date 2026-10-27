module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.Adapters.CatalogueFieldBridges

open CFSG.Open

theorem nonempty_mulEquiv_lie_of_statedProj {r : ℕ} (d : TauCeti.ValidLieTypeIndex)
    (eT : d.Group ≃* StatedProj (StatedSp r ↥d.fixedField))
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = d.fieldOrder) :
    Nonempty (StatedProj (StatedSp r k) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  classical
  let Fd := ↥d.fixedField
  haveI : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype k := Fintype.ofFinite k
  let _ : Fintype Fd := Fintype.ofFinite Fd
  have hFd : Nat.card Fd = d.fieldOrder := TauCeti.ValidLieTypeIndex.card_fixedField d
  have hcard : Fintype.card k = Fintype.card Fd := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hFd]
  let φ : k ≃+* Fd := FiniteField.ringEquivOfCardEq hcard
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin r ⊕ Fin r) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ r)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨e1.trans eT.symm⟩

theorem nonempty_mulEquiv_lie_C_of_statedProj {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = q.card) :
    Nonempty (StatedProj (StatedSp r k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.C r q, hv⟩).Group) := by
  refine nonempty_mulEquiv_lie_of_statedProj (r := r) ⟨TauCeti.LieTypeIndex.C r q, hv⟩
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv) ?_
  have hd : TauCeti.ValidLieTypeIndex.fieldOrder ⟨TauCeti.LieTypeIndex.C r q, hv⟩ = q.card := by
    rw [TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_C, TauCeti.LieTypeIndex.fieldExponent_C]
    exact (TauCeti.PrimePower.card_def q).symm
  rw [hd]
  exact hk

theorem nonempty_mulEquiv_lie_B2_of_statedProj {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = q.card) :
    Nonempty (StatedProj (StatedSp 2 k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group) := by
  refine nonempty_mulEquiv_lie_of_statedProj (r := 2) ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩
    (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) ?_
  have hd : TauCeti.ValidLieTypeIndex.fieldOrder ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩ = q.card := by
    rw [TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_B, TauCeti.LieTypeIndex.fieldExponent_B]
    exact (TauCeti.PrimePower.card_def q).symm
  rw [hd]
  exact hk

theorem nonempty_mulEquiv_lie_B_of_statedProj {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p = 2) (hr3 : 3 ≤ r)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = q.card) :
    Nonempty (StatedProj (StatedSp r k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B r q, hv⟩).Group) := by
  refine nonempty_mulEquiv_lie_of_statedProj (r := r) ⟨TauCeti.LieTypeIndex.B r q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3) ?_
  have hd : TauCeti.ValidLieTypeIndex.fieldOrder ⟨TauCeti.LieTypeIndex.B r q, hv⟩ = q.card := by
    rw [TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_B, TauCeti.LieTypeIndex.fieldExponent_B]
    exact (TauCeti.PrimePower.card_def q).symm
  rw [hd]
  exact hk

abbrev u42q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩

theorem u42q_valid : (TauCeti.LieTypeIndex.twistedA 3 u42q).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [u42q, TauCeti.PrimePower.card_def]

abbrev u42Index : TauCeti.ValidLieTypeIndex := ⟨.twistedA 3 u42q, u42q_valid⟩

theorem nonempty_mulEquiv_lie_u42 {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 3) :
    Nonempty (StatedProj (StatedSp 2 k) ≃*
      (TauCeti.CFSGIndex.lie u42Index).Group) := by
  classical
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  change Nonempty (StatedProj (StatedSp 2 k) ≃*
    (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩).Group)
  let _ : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk]
    simp [ZMod.card]
  let φ : k ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 2 ⊕ Fin 2) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv
  exact ⟨(e1.trans CFSG.GH74.Exceptional.psp43EquivU2).trans
    (CFSG.GH74.Exceptional.u2FourEquiv.trans eT.symm)⟩

theorem nonempty_commutator_statedSp_two_mulEquiv_alternating_six {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2) :
    Nonempty (↥(commutator (StatedSp 2 k)) ≃* alternatingGroup (Fin 6)) :=
  ⟨CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hk⟩

end CFSG.Adapters.CatalogueFieldBridges

end
