module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped Matrix

theorem catalogIs_u5two_of_statedSU5 {X : Type} [Group X] (e : X ≃* StatedSU 5 (2 ^ 1) F4) :
    catalogIs X S9.isU5two := by
  have hvalid : (TauCeti.LieTypeIndex.twistedA 4 ppTwo).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [ppTwo]
  let projM5 : StatedProj (StatedSU 5 (2 ^ 1) F4) ≃* StatedSU 5 (2 ^ 1) F4 :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot hF4card)).trans
      QuotientGroup.quotientBot
  have hc2 : TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 4 ppTwo, hvalid⟩ = 2 :=
    TauCeti.LieTypeIndex.characteristic_twistedA 4 _
  have hf2 : TauCeti.ValidLieTypeIndex.fieldExponent
      ⟨.twistedA 4 ppTwo, hvalid⟩ = 1 :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 4 _
  have eq := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4
    ppTwo hvalid
  have hq : TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 4 ppTwo, hvalid⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent
      ⟨.twistedA 4 ppTwo, hvalid⟩ = 2 ^ 1 := by
    rw [hc2, hf2]
  haveI : Fintype (GaloisField (TauCeti.ValidLieTypeIndex.characteristic
    ⟨.twistedA 4 ppTwo, hvalid⟩)
      (2 * TauCeti.ValidLieTypeIndex.fieldExponent
        ⟨.twistedA 4 ppTwo, hvalid⟩)) := Fintype.ofFinite _
  have hc : Fintype.card F4 = Fintype.card (GaloisField (TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 4 ppTwo, hvalid⟩)
        (2 * TauCeti.ValidLieTypeIndex.fieldExponent
          ⟨.twistedA 4 ppTwo, hvalid⟩)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF4card,
      GaloisField.card _ _ (by rw [hf2]; norm_num), hc2, hf2]
    norm_num
  have e1 : X ≃* StatedProj (StatedSU 5 (2 ^ 1) F4) := e.trans projM5.symm
  rw [← hq] at e1
  refine ⟨.lie ⟨.twistedA 4 ppTwo, hvalid⟩, ?_, ⟨?_⟩⟩
  · show ppTwo.card = 2
    rw [TauCeti.PrimePower.card_def]
    norm_num [ppTwo]
  · exact (e1.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 5 _)).trans eq.symm

theorem catalogIs_statedSU_U45 (a : ℕ) (ha : a = 4 ∨ a = 5) :
    catalogIs ↥(StatedSU a (2 ^ 1) F4) (fun i => S9.isU4two i ∨ S9.isU5two i) := by
  rcases ha with rfl | rfl
  · exact KSubT.catalogIs_mono (fun i hi => Or.inl hi)
      (CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj (K := F4)
        (by simpa using hF4card) equivM4.symm)
  · exact KSubT.catalogIs_mono (fun i hi => Or.inr hi)
      (catalogIs_u5two_of_statedSU5 (MulEquiv.refl _))

theorem typed_big (d : Fin 6 → F4) (c : F4) {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (hc4 : 4 ≤ Fintype.card (Blk d c)) (hc5 : Fintype.card (Blk d c) ≤ 5)
    (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD D) J) :
    catalogIs (PSimple 3 J) (fun i => S9.isU4two i ∨ S9.isU5two i) := by
  have hperf := glaPComponent_perfect hJ
  have hle : J ≤ CenD D := hJ.1
  have hJK : J ≤ (embSU d c).range := le_range_embSU d c hD hsmall hle hperf
  have hKC : (embSU d c).range ≤ CenD D := by
    rintro _ ⟨A, rfl⟩
    exact embSU_mem_CenD d c hD A
  have ha : Fintype.card (Blk d c) = 4 ∨ Fintype.card (Blk d c) = 5 := by omega
  let eK := MonoidHom.ofInjective (embSU_injective d c)

  haveI := isSimple_statedSU _ ha
  haveI hs : IsSimpleGroup ↥(embSU d c).range := eK.symm.isSimpleGroup
  have hsub : CFSG.Open.IsSubnormal J (embSU d c).range := by
    have h := hJ.2.1.inf_of_le hKC
    rwa [inf_eq_left.2 hJK] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hs with h | h
  · exact absurd h (glaPComponent_ne_bot' hJ)
  · subst h
    obtain ⟨e⟩ := nonempty_pSimple_equiv_of_simple hJ
    exact catalogIs_of_mulEquiv (e.trans eK.symm).symm (catalogIs_statedSU_U45 _ ha)

theorem typed_cube_one (B : primeFormUnitary hF4 (idGram F4 6)) (hB3 : B ^ 3 = 1)
    (hns : ¬ ∃ c : F4ˣ, (B : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD (B : GL (Fin 6) F4)) J) :
    catalogIs (PSimple 3 J) (fun i => S9.isU4two i ∨ S9.isU5two i) := by
  obtain ⟨P, d, hd⟩ := exists_diag6 B hB3
  set D : GL (Fin 6) F4 :=
    ((P⁻¹ * B * P : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) with hDdef
  have hDeq : D = (P : GL (Fin 6) F4)⁻¹ * (B : GL (Fin 6) F4) * (P : GL (Fin 6) F4) := rfl
  have hmap := glaPComponent_map_mulEquiv Nat.prime_three (conjM6 P⁻¹) hJ
  rw [map_CenD_conj] at hmap
  have hCen : ((P⁻¹ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) *
      (B : GL (Fin 6) F4) * ((P⁻¹ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)⁻¹ = D := by
    rw [hDeq]
    simp
  rw [hCen] at hmap
  obtain ⟨e⟩ := pSimple_map_equiv 3 (conjM6 P⁻¹) J
  refine catalogIs_of_mulEquiv e ?_
  have hperf := glaPComponent_perfect hmap
  have hDd : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hd
  have hnc : ¬ ∀ i, d i = d 0 := by
    intro hconst
    apply hns
    have hd0 : d 0 ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun (D.val_inv) 0) 0
      rw [hDd, Matrix.diagonal_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨Units.mk0 (d 0) hd0, ?_⟩
    have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) hd0) := by
      apply Units.ext
      rw [hDd, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hconst i]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hB : (B : GL (Fin 6) F4) = (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ := by
      rw [hDeq]
      group
    rw [hB, hDs, (commute_scalar (Units.mk0 (d 0) hd0) (P : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  by_cases hbig : ∃ c : F4, 4 ≤ Fintype.card (Blk d c)
  · obtain ⟨c, hc4⟩ := hbig
    have hc5 := card_blk_le_five d hnc c
    refine typed_big d c hDd hc4 hc5 (fun c' hc' => ?_) hmap
    have := card_blk_add_le d (c := c) (c' := c') (Ne.symm hc')
    omega
  · push Not at hbig
    exfalso
    exact glaPComponent_ne_bot' hmap
      (eq_bot_of_perfect_of_small hDd (fun c => by have := hbig c; omega) hmap.1 hperf)

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
