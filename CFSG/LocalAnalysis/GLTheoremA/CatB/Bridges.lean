module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmega
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Models.Blueprint
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

theorem exists_lieIndex {S : Type} [Group S] {P : LieTypeIndex → Prop}
    (h : catalogIs S (onLie P)) :
    ∃ (d : LieTypeIndex) (hv : d.Valid), P d ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨d, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j => exact ⟨j.1, j.2, hi, ⟨e⟩⟩

theorem lieIndex_isSp6two {S : Type} [Group S] (h : catalogIs S S9.isSp6two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem lieIndex_isU4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem lieIndex_isU5two {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 4 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem lieIndex_isU3eight {S : Type} [Group S] (h : catalogIs S S9.isU3eight) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid), q.card = 8 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem lieIndex_isD4two {S : Type} [Group S] (h : catalogIs S S9.isD4two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem exists_ringEquiv_zmod_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nonempty (K ≃+* ZMod 2) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, ZMod.card])⟩

@[expose] noncomputable def statedProjZMod2Equiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

@[expose] noncomputable def statedProjEquivZMod2 {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (φ : K ≃+* ZMod 2) {H : Subgroup (GL ι K)} {H' : Subgroup (GL ι (ZMod 2))}
    (hH : H.map (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) φ).toMonoidHom = H') :
    StatedProj H ≃* H' :=
  (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) φ) hH
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
    (statedProjZMod2Equiv H')

theorem bridge_sp6two {S : Type} [Group S] (h : catalogIs S S9.isSp6two) :
    Nonempty (S ≃* CFSG.Sporadic.Co2Smith.Sp62) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isSp6two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
  · rw [h1, h2] at hm
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
    obtain ⟨φ⟩ := exists_ringEquiv_zmod_two (K := K) (by rw [hK]; norm_num)
    exact ⟨e'.trans (statedProjEquivZMod2 φ
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 3))⟩
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem bridge_u4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    Nonempty (S ≃* CFSG.GH74.Exceptional.PSp43) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype CFSG.Blueprint.Fischer.K := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card CFSG.Blueprint.Fischer.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Fischer.Classification.Unitary.card_K]
  exact ⟨(e'.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 1))).trans
    (CFSG.GH74.Exceptional.u2FourEquiv.symm.trans
      CFSG.GH74.Exceptional.psp43EquivU2.symm)⟩

theorem bridge_u5two {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    Nonempty (S ≃* CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.SU52) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 4 q hv e
  rw [h1, h2] at hm
  exact CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.modelEquiv (hm.toBlueprint (by decide))

theorem bridge_u3eight {S : Type} [Group S] (h : catalogIs S S9.isU3eight) :
    Nonempty (S ≃* StatedProj (StatedSU 3 (2 ^ 3) (GaloisField 2 6))) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU3eight h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 2 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 6) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 6) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 6 (by norm_num)]
    norm_num
  exact ⟨e'.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 3 (2 ^ 3))⟩

section Omega

open Matrix CFSG.Adapters.RankTwoModelTransports CFSG.Blueprint.EvenSource

variable {K L : Type} [Field K] [Field L]

theorem statedQuadPlus_map (φ : K ≃+* L) (n : ℕ) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n L (φ ∘ v) = φ (StatedQuadPlus n K v) := by
  unfold StatedQuadPlus
  simp [CFSG.MatrixModel.plusQuadCore, map_sum, map_mul]

theorem map_matrixOrthogonal_plus (φ : K ≃+* L) (n : ℕ) :
    (matrixOrthogonal (StatedQuadPlus n K)).map
        (glCongr (ι := Fin n ⊕ Fin n) φ).toMonoidHom =
      matrixOrthogonal (StatedQuadPlus n L) := by
  ext B
  rw [Subgroup.mem_map_equiv]
  change (∀ v, StatedQuadPlus n K ((((glCongr (ι := Fin n ⊕ Fin n) φ).symm B : GL _ K) :
      Matrix _ _ K) *ᵥ v) = StatedQuadPlus n K v) ↔
    ∀ w, StatedQuadPlus n L ((B : Matrix _ _ L) *ᵥ w) = StatedQuadPlus n L w
  rw [glCongr_symm_coe]
  have hmul : ∀ v : Fin n ⊕ Fin n → K,
      (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) *ᵥ (φ ∘ v) =
        φ ∘ (((B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L).map φ.symm) *ᵥ v) := by
    intro v
    funext i
    have := RingHom.map_mulVec φ.toRingHom ((B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L).map φ.symm)
      v i
    rw [Matrix.map_map] at this
    have hid : (⇑φ.toRingHom ∘ ⇑φ.symm) = id := by funext x; simp
    rw [hid, Matrix.map_id] at this
    simpa using this.symm
  constructor
  · intro H w
    have := H (φ.symm ∘ w)
    have hw : φ ∘ (φ.symm ∘ w) = w := by funext x; simp
    have h1 := hmul (φ.symm ∘ w)
    rw [hw] at h1
    rw [h1, statedQuadPlus_map, this, ← statedQuadPlus_map, hw]
  · intro H v
    have := H (φ ∘ v)
    rw [hmul v, statedQuadPlus_map, statedQuadPlus_map] at this
    exact φ.injective this

theorem glCongr_statedOmega_plus (φ : K ≃+* L) (n : ℕ) :
    (StatedOmega (StatedQuadPlus n K)).map (glCongr (ι := Fin n ⊕ Fin n) φ).toMonoidHom =
      StatedOmega (StatedQuadPlus n L) := by
  rw [statedOmega_eq_commutator, statedOmega_eq_commutator, Subgroup.map_commutator,
    map_matrixOrthogonal_plus]

end Omega

theorem bridge_d4two {S : Type} [Group S] (h : catalogIs S S9.isD4two) :
    Nonempty (S ≃* CFSG.AGLEmbedding.Om8) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isD4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two (K := K) (by rw [hK]; norm_num)
  exact ⟨e'.trans (statedProjEquivZMod2 φ (glCongr_statedOmega_plus φ 4))⟩

def pp2 : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

theorem valid_twistedA_three : (LieTypeIndex.twistedA 3 pp2).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

theorem catalogIs_u4two_of_statedProj {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (e : X ≃* StatedProj (StatedSU 4 (2 ^ 1) K)) :
    catalogIs X S9.isU4two := by
  have hc2 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 2 :=
    LieTypeIndex.characteristic_twistedA 3 pp2
  have hf2 : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 1 :=
    LieTypeIndex.fieldExponent_twistedA 3 pp2
  have eq := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 pp2 valid_twistedA_three
  have hq : ValidLieTypeIndex.characteristic ⟨.twistedA 3 pp2, valid_twistedA_three⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 2 ^ 1 := by
    rw [hc2, hf2]
  rw [← hq] at e
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField (ValidLieTypeIndex.characteristic
    ⟨.twistedA 3 pp2, valid_twistedA_three⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩)) :=
    Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField (ValidLieTypeIndex.characteristic
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩)
        (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card _ _ (by rw [hf2]; norm_num), hc2, hf2]
    norm_num
  refine ⟨.lie ⟨.twistedA 3 pp2, valid_twistedA_three⟩, ?_, ⟨?_⟩⟩
  · show pp2.card = 2
    rw [PrimePower.card_def]
    norm_num [pp2]
  · exact (e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 4 _)).trans eq.symm


end CFSG.LocalAnalysis.GLTheoremA.CatB
