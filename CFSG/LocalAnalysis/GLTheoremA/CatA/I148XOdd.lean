module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)

theorem td4_index {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
  | _ => exact hP.elim

theorem td4_blueprint_model {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    CFSG.Blueprint.LieModel S .trialityD4 0 q.p q.exponent := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order)) =
      (q.p ^ q.exponent) ^ (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv
    (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order))
    (by rw [hKc, TauCeti.PrimePower.card_def]) (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order), inferInstance,
      inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  exact Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hC⟩)

theorem td4_order {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    Finite S ∧ (Nat.card S).factorization q.p = 12 * q.exponent := by
  have hL := td4_blueprint_model hv e
  obtain ⟨hfin, -, hfac⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
    .trialityD4 0 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hL) hL
  exact ⟨hfin, hfac⟩

theorem td4_card_of_odd {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) : 3 ^ 12 ≤ Nat.card S := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hodd := td4_blueprint_model hv e
  have hadm := CFSG.Blueprint.LieModel.admissible hodd
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hcard := (hO S .trialityD4 0 q.p q.exponent hadm hodd).2.1
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hQ : 3 ≤ q.p ^ q.exponent := le_trans hp3 (Nat.le_self_pow q.exponent_pos.ne' _)
  have hNS : Nat.card S = (q.p ^ q.exponent) ^ 12 * ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
      ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) := by
    simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hcard
  rw [hNS]
  have h6 : 2 ≤ (q.p ^ q.exponent) ^ 6 := le_trans (by omega) (Nat.pow_le_pow_left hQ 6)
  have h2 : 2 ≤ (q.p ^ q.exponent) ^ 2 := le_trans (by omega) (Nat.pow_le_pow_left hQ 2)
  have hX : 0 < ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
      ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have h12 : 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := Nat.pow_le_pow_left hQ 12
  calc 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := h12
    _ ≤ (q.p ^ q.exponent) ^ 12 * (((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
        ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1)) :=
      Nat.le_mul_of_pos_right _ hX
    _ = _ := by ring

theorem td4_odd_false {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hchev : IsChevSimple 2 S) :
    False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hbig := td4_card_of_odd hv hp e
  have hodd := td4_blueprint_model hv e
  have hadm := CFSG.Blueprint.LieModel.admissible hodd
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases hchev with ⟨t', n', f', hX⟩ | ⟨e6⟩ | hPSU
  · have hodd' : CFSG.Blueprint.OddLieType S :=
      ⟨.trialityD4, 0, q.p, q.exponent, q.prime_p, hp, hadm, hodd⟩
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hX hodd' with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
  · obtain ⟨e6'⟩ := e6
    have h6 : Nat.card S = 360 := by
      rw [Nat.card_congr e6'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
    have h := (hO S .PSU 3 3 1 (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 from by decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) = 1 from rfl] at h
    norm_num at hbig
    omega

theorem td4_two_of_centQ {R : Type} [Group R] (hC : CentQIndexCases R) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : R ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) : q.p = 2 := by
  by_contra hq
  have hbig := td4_card_of_odd hv hq e
  rcases hC with ⟨d, hd, ⟨ed⟩⟩ | ⟨e5⟩ | ⟨e6⟩ | ⟨e8⟩ | h168 | ⟨-, h6048⟩
  · exact td4_odd_false hv hq e (Or.inl ⟨TauCeti.CFSGIndex.lie d, hd, ⟨ed⟩⟩)
  · obtain ⟨e5'⟩ := e5
    have h : Nat.card R = 60 := by
      rw [Nat.card_congr e5'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · obtain ⟨e6'⟩ := e6
    have h : Nat.card R = 360 := by
      rw [Nat.card_congr e6'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · obtain ⟨e8'⟩ := e8
    have h : Nat.card R = 20160 := by
      rw [Nat.card_congr e8'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · norm_num at hbig
    omega
  · norm_num at hbig
    omega

end CFSG.LocalAnalysis.GLTheoremA

end
