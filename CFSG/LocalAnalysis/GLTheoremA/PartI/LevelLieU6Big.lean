module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Blk
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

@[expose] def extMat (d : Fin 6 → F4) (c : F4) (A : Matrix (Blk d c) (Blk d c) F4) :
    Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.reindex (Equiv.sumCompl (fun i => d i = c)) (Equiv.sumCompl (fun i => d i = c))
    (Matrix.fromBlocks A 0 0 1)

variable (d : Fin 6 → F4) (c : F4)

theorem extMat_apply (A : Matrix (Blk d c) (Blk d c) F4) (i j : Fin 6) :
    extMat d c A i j =
      if h : d i = c ∧ d j = c then A ⟨i, h.1⟩ ⟨j, h.2⟩ else (1 : Matrix (Fin 6) (Fin 6) F4) i j := by
  by_cases hi : d i = c <;> by_cases hj : d j = c
  · simp [extMat, hi, hj, Equiv.sumCompl_symm_apply_of_pos]
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [extMat, hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg,
      Matrix.one_apply_ne hij]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [extMat, hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg,
      Matrix.one_apply_ne hij]
  · simp [extMat, hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg,
      Matrix.one_apply, Subtype.ext_iff]

theorem extMat_one : extMat d c 1 = 1 := by
  unfold extMat
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem extMat_mul (A B : Matrix (Blk d c) (Blk d c) F4) :
    extMat d c (A * B) = extMat d c A * extMat d c B := by
  have h : Matrix.fromBlocks (A * B) 0 0 (1 : Matrix {i // ¬ d i = c} {i // ¬ d i = c} F4) =
      Matrix.fromBlocks A 0 0 1 * Matrix.fromBlocks B 0 0 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have := map_mul (Matrix.reindexAlgEquiv F4 F4 (Equiv.sumCompl (fun i => d i = c)))
    (Matrix.fromBlocks A 0 0 1) (Matrix.fromBlocks B 0 0 1)
  simp only [Matrix.reindexAlgEquiv_apply] at this
  unfold extMat
  rw [h]
  exact this

theorem det_extMat (A : Matrix (Blk d c) (Blk d c) F4) : (extMat d c A).det = A.det := by
  unfold extMat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem extMat_map (A : Matrix (Blk d c) (Blk d c) F4) :
    (extMat d c A).map bar = extMat d c (A.map bar) := by
  ext i j
  rw [Matrix.map_apply, extMat_apply, extMat_apply]
  by_cases h : d i = c ∧ d j = c
  · simp [h]
  · simp only [h, dif_neg, not_false_eq_true]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem extMat_transpose (A : Matrix (Blk d c) (Blk d c) F4) :
    (extMat d c A)ᵀ = extMat d c Aᵀ := by
  ext i j
  rw [Matrix.transpose_apply, extMat_apply, extMat_apply]
  by_cases h : d j = c ∧ d i = c
  · simp [h, and_comm]
  · have h' : ¬ (d i = c ∧ d j = c) := fun h2 => h ⟨h2.2, h2.1⟩
    simp only [h, h', dif_neg, not_false_eq_true]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]

theorem extMat_unitary (A : Matrix (Blk d c) (Blk d c) F4) (hA : (A.map bar)ᵀ * A = 1) :
    ((extMat d c A).map bar)ᵀ * extMat d c A = 1 := by
  rw [extMat_map, extMat_transpose, ← extMat_mul, hA, extMat_one]

theorem blkM_extMat (A : Matrix (Blk d c) (Blk d c) F4) : blkM d c (extMat d c A) = A := by
  ext i j
  simp [blkM, extMat_apply, i.2, j.2]

theorem extMat_blkM {M : Matrix (Fin 6) (Fin 6) F4}
    (hM : ∀ i j, ¬ (d i = c ∧ d j = c) → M i j = (1 : Matrix (Fin 6) (Fin 6) F4) i j) :
    extMat d c (blkM d c M) = M := by
  ext i j
  rw [extMat_apply]
  split_ifs with h
  · rfl
  · exact (hM i j h).symm

theorem det_eq_one_of_mem_statedSU' (k : ℕ) {A : GL (Fin k) F4}
    (h : A ∈ StatedSU k (2 ^ 1) F4) : (A : Matrix (Fin k) (Fin k) F4).det = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Matrix.det_isEmpty
  · exact det_one_of_mem_statedSU hk A h

theorem unitary_of_mem_statedSU' (k : ℕ) {A : GL (Fin k) F4}
    (h : A ∈ StatedSU k (2 ^ 1) F4) :
    ((A : Matrix (Fin k) (Fin k) F4).map bar)ᵀ * (A : Matrix (Fin k) (Fin k) F4) = 1 := by
  have h2 := ((mem_unitarySU_iff hF4).1 h).2
  rwa [hF4_bar] at h2

@[expose] def extHom : Matrix (Blk d c) (Blk d c) F4 →* Matrix (Fin 6) (Fin 6) F4 where
  toFun := extMat d c
  map_one' := extMat_one d c
  map_mul' := extMat_mul d c

@[expose] def embGL : GL (Blk d c) F4 →* GL (Fin 6) F4 := Units.map (extHom d c)

theorem coe_embGL (A : GL (Blk d c) F4) :
    ((embGL d c A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      extMat d c (A : Matrix (Blk d c) (Blk d c) F4) := rfl

theorem embGL_reindex_mem (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) :
    embGL d c (reindexGL (Fintype.equivFin (Blk d c)).symm (A : GL _ F4)) ∈
      StatedSU 6 (2 ^ 1) F4 := by
  apply mem_statedSU_of
  · rw [coe_embGL, det_extMat, reindexGL_val, Matrix.det_reindex_self]
    exact det_eq_one_of_mem_statedSU' _ A.2
  · rw [coe_embGL, reindexGL_val]
    apply extMat_unitary
    exact reindex_unitary _ _ (unitary_of_mem_statedSU' _ A.2)

@[expose] noncomputable def embSU :
    ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) →* M6 :=
  MonoidHom.codRestrict ((embGL d c).comp ((reindexGL (Fintype.equivFin (Blk d c)).symm).comp
    (StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4).subtype)) (StatedSU 6 (2 ^ 1) F4)
    (fun A => embGL_reindex_mem d c A)

theorem mM6_embSU (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) :
    mM6 (embSU d c A) =
      extMat d c (Matrix.reindex (Fintype.equivFin (Blk d c)).symm (Fintype.equivFin (Blk d c)).symm
        (((A : GL (Fin (Fintype.card (Blk d c))) F4) :
          Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4))) := rfl

theorem embSU_injective : Function.Injective (embSU d c) := by
  intro A B h
  have h1 : mM6 (embSU d c A) = mM6 (embSU d c B) := congrArg mM6 h
  rw [mM6_embSU, mM6_embSU] at h1
  have h2 := congrArg (blkM d c) h1
  rw [blkM_extMat, blkM_extMat] at h2
  have h3 := (Matrix.reindex (Fintype.equivFin (Blk d c)).symm
    (Fintype.equivFin (Blk d c)).symm).injective h2
  exact Subtype.ext (Units.ext h3)

theorem embSU_mem_CenD {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) : embSU d c A ∈ CenD D := by
  rw [mem_CenD]
  apply Units.ext
  show mM6 (embSU d c A) * (D : Matrix (Fin 6) (Fin 6) F4) =
    (D : Matrix (Fin 6) (Fin 6) F4) * mM6 (embSU d c A)
  rw [hD]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mM6_embSU, extMat_apply]
  by_cases h : d i = c ∧ d j = c
  · rw [dif_pos h]
    have e : d j = d i := h.2.trans h.1.symm
    exact (congrArg (fun t => _ * t) e).trans (mul_comm _ _)
  · rw [dif_neg h]
    by_cases hij : i = j
    · subst hij
      rw [mul_comm]
    · simp [Matrix.one_apply_ne hij]

theorem le_range_embSU {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3)
    {J : Subgroup M6} (hJ : J ≤ CenD D) (hperf : ⁅J, J⁆ = J) : J ≤ (embSU d c).range := by
  intro u hu
  let e := Fintype.equivFin (Blk d c)
  have hmem : reindexGL e (blkHom hD c ⟨u, hJ hu⟩) ∈
      StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4 := by
    apply mem_statedSU_of
    · rw [reindexGL_val, Matrix.det_reindex_self]
      exact det_blk_of_perfect hD hJ hperf c hu
    · rw [reindexGL_val]
      exact reindex_unitary _ _ (blkM_unitary d c (fun i j hij => CenD_zero hD ⟨u, hJ hu⟩ hij)
        (M6_unitary u))
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change mM6 (embSU d c ⟨_, hmem⟩) = mM6 u
  rw [mM6_embSU]
  have hround : Matrix.reindex e.symm e.symm
      ((((reindexGL e (blkHom hD c ⟨u, hJ hu⟩) : GL (Fin (Fintype.card (Blk d c))) F4)) :
        Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4)) =
      blkM d c (mM6 u) := by
    rw [reindexGL_val]
    ext i j
    simp [Matrix.reindex_apply, blkHom_val]
  rw [hround]
  apply extMat_blkM
  intro i j hij
  by_cases hdij : d i = d j
  · have hne : d i ≠ c := fun h => hij ⟨h, hdij ▸ h⟩
    have h1 := blk_eq_one_of_small hD hJ hperf (d i) (hsmall _ hne) hu
    have h2 := congrArg (fun g : GL (Blk d (d i)) F4 =>
      (g : Matrix (Blk d (d i)) (Blk d (d i)) F4) ⟨i, rfl⟩ ⟨j, hdij.symm⟩) h1
    simp only [blkHom_val, blkM, Units.val_one, Matrix.one_apply, Subtype.mk.injEq] at h2
    rw [Matrix.one_apply]
    exact h2
  · rw [CenD_zero hD ⟨u, hJ hu⟩ hdij, Matrix.one_apply_ne (fun h => hdij (by rw [h]))]

theorem isSimple_statedSU (a : ℕ) (ha : a = 4 ∨ a = 5) : IsSimpleGroup ↥(StatedSU a (2 ^ 1) F4) := by
  rcases ha with rfl | rfl
  · exact isSimple_M4
  · exact isSimpleGroup_M5

@[expose] def ppTwo : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

theorem catalogIs_k2_of_statedSU5 {X : Type} [Group X] (e : X ≃* StatedSU 5 (2 ^ 1) F4) :
    catalogIs X (k2 3) := by
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
  · show 3 = 3 ∧ ppTwo.card = 2
    refine ⟨rfl, ?_⟩
    rw [TauCeti.PrimePower.card_def]
    norm_num [ppTwo]
  · exact (e1.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 5 _)).trans eq.symm

theorem kLevel_statedSU_le_two (a : ℕ) (ha : a = 4 ∨ a = 5) :
    kLevel 3 ↥(StatedSU a (2 ^ 1) F4) ≤ 2 := by
  rcases ha with rfl | rfl
  · have hcat : catalogIs ↥(StatedSU 4 (2 ^ 1) F4) CFSG.LocalAnalysis.GLTheoremA.S9.isU4two :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj (K := F4)
        (by simpa using hF4card) equivM4.symm
    exact kLevel_le_two_of_chev (Or.inr (catalog_ambiguous_of_u4two hcat))
  · exact kLevel_le_two_of_k2 (catalogIs_k2_of_statedSU5 (MulEquiv.refl _))

theorem nonempty_pSimple_equiv_of_simple {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    [IsSimpleGroup K] (hK : GLAPComponent 3 X K) : Nonempty (PSimple 3 K ≃* K) := by
  haveI : IsSimpleGroup (PSimple 3 K) := (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK).2
  have hsub : ∀ (N : Subgroup (PQuot 3 K)), N = ⊤ → Subsingleton (PQuot 3 K ⧸ N) := fun N h =>
    h ▸ QuotientGroup.subsingleton_quotient_top
  have hO : GLAPPrimeCore 3 ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥K) with h | h
    · exact h
    · exfalso
      haveI : Subsingleton (PQuot 3 K) := by
        show Subsingleton (↥K ⧸ GLAPPrimeCore 3 ↥K)
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton (PSimple 3 K) := ⟨fun a b => by
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        exact congrArg _ (Subsingleton.elim a' b')⟩
      exact not_subsingleton_iff_nontrivial.2 (inferInstance : Nontrivial (PSimple 3 K)) ‹_›
  let pq0 : PQuot 3 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (PQuot 3 K) := pq0.isSimpleGroup
  have hZP : Subgroup.center (PQuot 3 K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 K)) with h | h
    · exact h
    · exfalso
      haveI := hsub _ h
      haveI : Subsingleton (PSimple 3 K) := inferInstance
      exact not_subsingleton_iff_nontrivial.2 (inferInstance : Nontrivial (PSimple 3 K)) ‹_›
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZP).trans (QuotientGroup.quotientBot.trans pq0)⟩

theorem level_of_big {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (hc4 : 4 ≤ Fintype.card (Blk d c)) (hc5 : Fintype.card (Blk d c) ≤ 5)
    (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD D) J) : kLevel 3 (PSimple 3 J) ≤ 2 := by
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
    rw [kLevel_congr 3 e, ← kLevel_congr 3 eK]
    exact kLevel_statedSU_le_two _ ha

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
