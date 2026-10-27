module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6EdgeData
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RelayOut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (antidiag)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)
open CFSG.SeitzReduction.SymplecticPilot (kOmegaVec kOmegaEmb q2OmIota nsElt mat_nsElt)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL mat_leviEmbedSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)

section Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

@[expose] noncomputable def twEdgeTheta : F ≃+* TwF4 :=
  haveI := Fintype.ofFinite F
  FiniteField.ringEquivOfCardEq (by
    rw [CFSG.LieType.Chevalley.C2E6Overlap.card_K, Fintype.card_eq_nat_card, h.card]
    norm_num)

theorem twEdgeTheta_bar (c : F) :
    twEdgeTheta h (h.bar c) = CFSG.LieType.Chevalley.C2E6Overlap.bar (twEdgeTheta h c) := by
  rw [UnitaryFieldData.bar_apply, pow_one, map_pow]
  rfl

theorem twEdgeTheta_comp_castHom :
    (twEdgeTheta h).toRingHom.comp (ZMod.castHom (dvd_refl 2) F) = twCast :=
  RingHom.ext_zmod _ _

theorem antidiag_map_twEdgeTheta :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) F).map (twEdgeTheta h) =
      CFSG.LieType.Chevalley.C2E6Overlap.hermJ := by
  have key : ∀ i j : Fin 4, (j = Fin.rev i) ↔ ((i : ℕ) + j = 3) := by decide
  ext i j
  simp only [Matrix.map_apply, antidiag, Matrix.of_apply, CFSG.LieType.Chevalley.C2E6Overlap.hermJ]
  split_ifs with h1 h2 h2
  · exact map_one _
  · exact absurd ((key i j).1 h1) h2
  · exact absurd ((key i j).2 h2) h1
  · exact map_zero _

theorem twHerm_mulVec {M : Matrix (Fin 4) (Fin 4) TwF4}
    (hM : Mᵀ * CFSG.LieType.Chevalley.C2E6Overlap.hermJ *
      M.map CFSG.LieType.Chevalley.C2E6Overlap.bar = CFSG.LieType.Chevalley.C2E6Overlap.hermJ)
    (v w : Fin 4 → TwF4) :
    CFSG.LieType.Chevalley.C2E6Overlap.herm (M *ᵥ v) (M *ᵥ w) =
      CFSG.LieType.Chevalley.C2E6Overlap.herm v w := by
  have hbar : (fun i => CFSG.LieType.Chevalley.C2E6Overlap.bar ((M *ᵥ w) i)) =
      M.map CFSG.LieType.Chevalley.C2E6Overlap.bar *ᵥ
        fun i => CFSG.LieType.Chevalley.C2E6Overlap.bar (w i) :=
    funext fun i => RingHom.map_mulVec CFSG.LieType.Chevalley.C2E6Overlap.barHom M w i
  rw [CFSG.LieType.Chevalley.C2E6Overlap.herm_eq_dotProduct,
    CFSG.LieType.Chevalley.C2E6Overlap.herm_eq_dotProduct, hbar]
  set u := CFSG.LieType.Chevalley.C2E6Overlap.hermJ *ᵥ
    (M.map CFSG.LieType.Chevalley.C2E6Overlap.bar *ᵥ
      fun i => CFSG.LieType.Chevalley.C2E6Overlap.bar (w i)) with hu
  have h1 : (M *ᵥ v) ⬝ᵥ u = v ⬝ᵥ (Mᵀ *ᵥ u) := by
    rw [Matrix.mulVec_transpose, dotProduct_comm v, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [h1, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem twGram_bar {M : Matrix (Fin 4) (Fin 4) TwF4}
    (hM : (M.map CFSG.LieType.Chevalley.C2E6Overlap.bar)ᵀ *
      CFSG.LieType.Chevalley.C2E6Overlap.hermJ * M = CFSG.LieType.Chevalley.C2E6Overlap.hermJ) :
    Mᵀ * CFSG.LieType.Chevalley.C2E6Overlap.hermJ *
      M.map CFSG.LieType.Chevalley.C2E6Overlap.bar = CFSG.LieType.Chevalley.C2E6Overlap.hermJ := by
  have hJ : CFSG.LieType.Chevalley.C2E6Overlap.hermJ.map CFSG.LieType.Chevalley.C2E6Overlap.bar =
      CFSG.LieType.Chevalley.C2E6Overlap.hermJ := by
    ext i j
    simp only [Matrix.map_apply, CFSG.LieType.Chevalley.C2E6Overlap.hermJ, Matrix.of_apply]
    split_ifs
    · exact CFSG.LieType.Chevalley.C2E6Overlap.bar_one
    · exact CFSG.LieType.Chevalley.C2E6Overlap.bar_zero
  have hMM : (M.map CFSG.LieType.Chevalley.C2E6Overlap.bar).map
      CFSG.LieType.Chevalley.C2E6Overlap.bar = M := by
    ext i j
    exact CFSG.LieType.Chevalley.C2E6Overlap.bar_bar _
  have h2 := congrArg (fun X => X.map CFSG.LieType.Chevalley.C2E6Overlap.barHom) hM
  simp only [Matrix.map_mul, Matrix.transpose_map] at h2
  change (((M.map CFSG.LieType.Chevalley.C2E6Overlap.bar).map
      CFSG.LieType.Chevalley.C2E6Overlap.bar)ᵀ *
      CFSG.LieType.Chevalley.C2E6Overlap.hermJ.map CFSG.LieType.Chevalley.C2E6Overlap.bar *
      M.map CFSG.LieType.Chevalley.C2E6Overlap.bar =
    CFSG.LieType.Chevalley.C2E6Overlap.hermJ.map CFSG.LieType.Chevalley.C2E6Overlap.bar) at h2
  rwa [hMM, hJ] at h2

@[expose] noncomputable def twTauGL :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) →* GL (Fin 4) TwF4 :=
  (Units.map (twEdgeTheta h).toRingHom.mapMatrix.toMonoidHom).comp
    (gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)).subtype

theorem coe_twTauGL (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
    ((twTauGL h g : GL (Fin 4) TwF4) : Matrix (Fin 4) (Fin 4) TwF4) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (twEdgeTheta h) :=
  rfl

theorem twTauGL_mem (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
    twTauGL h g ∈ CFSG.LieType.Chevalley.C2E6Overlap.SU := by
  have hg := (mem_gramSU.1 g.2)
  set M : Matrix (Fin 4) (Fin 4) TwF4 := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map
    (twEdgeTheta h) with hMdef
  have hbarM : (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map h.bar).map (twEdgeTheta h) =
      M.map CFSG.LieType.Chevalley.C2E6Overlap.bar := by
    ext i j
    simp only [Matrix.map_apply, hMdef]
    exact twEdgeTheta_bar h _
  have hgram : (M.map CFSG.LieType.Chevalley.C2E6Overlap.bar)ᵀ *
      CFSG.LieType.Chevalley.C2E6Overlap.hermJ * M = CFSG.LieType.Chevalley.C2E6Overlap.hermJ := by
    have h1 := congrArg (fun X => X.map (twEdgeTheta h).toRingHom) hg.1
    simp only [Matrix.map_mul, Matrix.transpose_map] at h1
    change ((((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map h.bar).map (twEdgeTheta h))ᵀ *
      (antidiag 4 : Matrix (Fin 4) (Fin 4) F).map (twEdgeTheta h) * M =
        (antidiag 4 : Matrix (Fin 4) (Fin 4) F).map (twEdgeTheta h) at h1
    rwa [hbarM, antidiag_map_twEdgeTheta] at h1
  have hdet : M.det = 1 := by
    have h2 := RingHom.map_det (twEdgeTheta h).toRingHom
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [hg.2, map_one] at h2
    exact h2.symm
  rw [CFSG.LieType.Chevalley.C2E6Overlap.mem_SU, coe_twTauGL]
  exact ⟨hdet, twHerm_mulVec (twGram_bar hgram)⟩

@[expose] noncomputable def twTau :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) →* CFSG.LieType.Chevalley.C2E6Overlap.SU :=
  (twTauGL h).codRestrict _ (twTauGL_mem h)

theorem coe_twTau (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
    (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
      Matrix (Fin 4) (Fin 4) TwF4) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (twEdgeTheta h) :=
  rfl

end Transport

section Simple

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

theorem isSimpleGroup_gramSU_antidiag_four :
    IsSimpleGroup (gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv h
    (SymplecticPilot.isPrimeFormGram_ctuaAntidiagGL (r := 4) (F := F))
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 1 h.card_eq_sq 4
    (by norm_num) (by decide)
  exact ((relayTwPEquiv h).trans (e.trans (unitaryPSUEquiv h (by norm_num)))).isSimpleGroup

end Simple

section Mu

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
  {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

variable (K) in
@[expose] noncomputable def twMu6Mon :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) →* Matrix omMI6 omMI6 K where
  toFun g := omMat K (omMMat6 (twKappaHom (twTau h g)))
  map_one' := by rw [map_one, map_one, omMMat6_one, omMat_one]
  map_mul' g g' := by rw [map_mul, map_mul, omMMat6_mul, omMat_mul]

variable (K) in
@[expose] noncomputable def twMu6GL :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) →* GL omMI6 K :=
  (twMu6Mon h K).toHomUnits

theorem coe_twMu6GL (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
    ((twMu6GL h K g : GL omMI6 K) : Matrix omMI6 omMI6 K) =
      omMat K (omMMat6 (twKappa (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) :
        GL (Fin 4) TwF4) : Matrix (Fin 4) (Fin 4) TwF4))) :=
  rfl

include hK in
theorem twMu6GL_isom (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) (w : omMI6 → K) :
    StatedQuadMinus 3 K 1 1 (((twMu6GL h K g : GL omMI6 K) : Matrix omMI6 omMI6 K) *ᵥ w) =
      StatedQuadMinus 3 K 1 1 w := by
  rw [coe_twMu6GL]
  exact omIsom hK (statedQuadMinus_omCast 3)
    (statedQuadMinus_omMMat6_twKappa_mulVec (twTau h g).2) w

include hK in
theorem range_twMu6GL_le : (twMu6GL h K).range ≤ StatedOmega (StatedQuadMinus 3 K 1 1) := by
  have hperf : ⁅(⊤ : Subgroup (gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F))), ⊤⁆ = ⊤ :=
    (isPerfect_gramSU_antidiag_four h).commutator_eq_top
  have hle : Subgroup.map (twMu6GL h K) ⊤ ≤
      Subgroup.closure {A : GL omMI6 K | ∀ v, StatedQuadMinus 3 K 1 1
        ((A : Matrix omMI6 omMI6 K) *ᵥ v) = StatedQuadMinus 3 K 1 1 v} := by
    rintro _ ⟨g, -, rfl⟩
    exact Subgroup.subset_closure (twMu6GL_isom h hK g)
  rw [MonoidHom.range_eq_map, ← hperf, Subgroup.map_commutator, StatedOmega]
  exact Subgroup.commutator_mono hle hle

@[expose] noncomputable def twMu6 :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) →* StatedOmega (StatedQuadMinus 3 K 1 1) :=
  (twMu6GL h K).codRestrict _ fun g => range_twMu6GL_le h hK ⟨g, rfl⟩

@[expose] noncomputable def twMu :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) →* StatedOmega (StatedQuadPlus (3 + 1) K) :=
  (omEps0 (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP) (Q₆ := StatedQuadMinus 3 K 1 1)
    omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK)).comp (twMu6 h hK)

theorem coe_twMu (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
    (((twMu h hK g : StatedOmega (StatedQuadPlus (3 + 1) K)) : GL omPI K) :
      Matrix omPI omPI K) =
      omMat K (twMu0 (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
        Matrix (Fin 4) (Fin 4) TwF4)) := by
  rw [twMu, MonoidHom.comp_apply, coe_omEps0, coe_omEps]
  change omMat K omPT * fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0
    (omMat K (omMMat6 (twKappa _))) * omMat K omPTi = _
  rw [← omMat_fromBlocks_one, ← omMat_mul, ← omMat_mul]
  rfl

theorem commute_omPXhK_twMu (g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
    Commute (omPXhK hK) (twMu h hK g) := by
  have h1 := range_omEps0_le_centralizer (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP)
    (Q₆ := StatedQuadMinus 3 K 1 1) omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK) (omPTi_xh_TK hK)
    ⟨twMu6 h hK g, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at h1
  exact h1.symm

theorem twMu_injective_of_ne_one {g₀ : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)}
    (hg₀ : twMu h hK g₀ ≠ 1) : Function.Injective (twMu h hK) := by
  have := isSimpleGroup_gramSU_antidiag_four h
  rcases (twMu h hK).normal_ker.eq_bot_or_eq_top with hb | ht
  · exact (MonoidHom.ker_eq_bot_iff _).1 hb
  · exact absurd (MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top g₀)) hg₀

end Mu

section Rational

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

omit [Finite F] in
theorem bar_castHom_zmod (a : ZMod 2) :
    h.bar (ZMod.castHom (dvd_refl 2) F a) = ZMod.castHom (dvd_refl 2) F a := by
  have ha : a ^ 2 = a := by revert a; decide
  rw [UnitaryFieldData.bar_apply, pow_one, ← map_pow, ha]

omit [Finite F] in
theorem antidiag_map_castHom :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) F) =
      antidiag 4 := by
  ext i j
  simp only [Matrix.map_apply, antidiag, Matrix.of_apply]
  split_ifs <;> simp

omit [Finite F] in
theorem det_map_castHom_ne_zero {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hd : A₀.det = 1) :
    (A₀.map (ZMod.castHom (dvd_refl 2) F)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_one]
  exact one_ne_zero

omit [Finite F] in
theorem twSUOfZ2_mem {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hA : A₀ᵀ * antidiag 4 * A₀ = antidiag 4) (hd : A₀.det = 1) :
    GeneralLinearGroup.mkOfDetNeZero (A₀.map (ZMod.castHom (dvd_refl 2) F))
      (det_map_castHom_ne_zero hd) ∈ gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) := by
  rw [mem_gramSU]
  change ((A₀.map (ZMod.castHom (dvd_refl 2) F)).map h.bar)ᵀ * antidiag 4 *
      A₀.map (ZMod.castHom (dvd_refl 2) F) = antidiag 4 ∧
    (A₀.map (ZMod.castHom (dvd_refl 2) F)).det = 1
  have hbar : (A₀.map (ZMod.castHom (dvd_refl 2) F)).map h.bar =
      A₀.map (ZMod.castHom (dvd_refl 2) F) := by
    ext i j
    exact bar_castHom_zmod h _
  refine ⟨?_, ?_⟩
  · rw [hbar, ← antidiag_map_castHom, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      hA]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_one]

@[expose] noncomputable def twSUOfZ2 (A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hA : A₀ᵀ * antidiag 4 * A₀ = antidiag 4) (hd : A₀.det = 1) :
    gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) :=
  ⟨_, twSUOfZ2_mem h hA hd⟩

theorem coe_twSUOfZ2 {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hA : A₀ᵀ * antidiag 4 * A₀ = antidiag 4) (hd : A₀.det = 1) :
    (((twSUOfZ2 h A₀ hA hd : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = A₀.map (ZMod.castHom (dvd_refl 2) F) :=
  rfl

theorem coe_twTau_twSUOfZ2 {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hA : A₀ᵀ * antidiag 4 * A₀ = antidiag 4) (hd : A₀.det = 1) :
    (((twTau h (twSUOfZ2 h A₀ hA hd) : CFSG.LieType.Chevalley.C2E6Overlap.SU) :
      GL (Fin 4) TwF4) : Matrix (Fin 4) (Fin 4) TwF4) = A₀.map twCast := by
  rw [coe_twTau, coe_twSUOfZ2, Matrix.map_map]
  have h1 := congrArg DFunLike.coe (twEdgeTheta_comp_castHom h)
  rw [RingHom.coe_comp] at h1
  exact congrArg (fun φ => A₀.map φ) h1

theorem twA03_gram : twA03ᵀ * antidiag 4 * twA03 = antidiag 4 := by decide +kernel
theorem twA03_det : twA03.det = 1 := by decide +kernel
theorem twA30_gram : twA30ᵀ * antidiag 4 * twA30 = antidiag 4 := by decide +kernel
theorem twA30_det : twA30.det = 1 := by decide +kernel
theorem twA12_gram : twA12ᵀ * antidiag 4 * twA12 = antidiag 4 := by decide +kernel
theorem twA12_det : twA12.det = 1 := by decide +kernel
theorem twA21_gram : twA21ᵀ * antidiag 4 * twA21 = antidiag 4 := by decide +kernel
theorem twA21_det : twA21.det = 1 := by decide +kernel
theorem twA0123_gram : twA0123ᵀ * antidiag 4 * twA0123 = antidiag 4 := by decide +kernel
theorem twA0123_det : twA0123.det = 1 := by decide +kernel

end Rational

section Iota

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
  {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

noncomputable abbrev twG03 : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) :=
  twSUOfZ2 h twA03 twA03_gram twA03_det

noncomputable abbrev twG30 : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) :=
  twSUOfZ2 h twA30 twA30_gram twA30_det

noncomputable abbrev twG12 : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) :=
  twSUOfZ2 h twA12 twA12_gram twA12_det

noncomputable abbrev twG21 : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) :=
  twSUOfZ2 h twA21 twA21_gram twA21_det

noncomputable abbrev twG0123 : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F) :=
  twSUOfZ2 h twA0123 twA0123_gram twA0123_det

include hK in
theorem twIota_eq_twMu {r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3}
    {g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)} {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    {T₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hg : (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
      Matrix (Fin 4) (Fin 4) TwF4) = A₀.map twCast)
    (hT : twMu0 (A₀.map twCast) = omPMat T₀)
    (hv : omPMat T₀ *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3)
    (hs : (omPMat T₀).submatrix (kOmegaEmb 3) (kOmegaEmb 3) = edgeSp r) :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt r 1) = twMu h hK g := by
  refine q2OmIota_eq_of_res hK _ _ ?_ ?_
  · rw [coe_twMu, hg, hT, kOmegaVec_omCast, omMat_mulVec, hv]
  · rw [coe_twMu, hg, hT, Matrix.submatrix_map, hs, mat_elt_one]
    rfl

include hK in
theorem q2OmIota_P12_twMu :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt (.positiveSum 1 2 (by decide)) 1) =
      twMu h hK (twG03 h) :=
  twIota_eq_twMu h hK (coe_twTau_twSUOfZ2 h _ _) twMu0_A03 twMuA03_vec twMuA03_hyp

include hK in
theorem q2OmIota_M12_twMu :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt (.negativeSum 1 2 (by decide)) 1) =
      twMu h hK (twG30 h) :=
  twIota_eq_twMu h hK (coe_twTau_twSUOfZ2 h _ _) twMu0_A30 twMuA30_vec twMuA30_hyp

include hK in
theorem q2OmIota_D12_twMu :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt (.difference 1 2 (by decide)) 1) =
      twMu h hK (twG12 h) :=
  twIota_eq_twMu h hK (coe_twTau_twSUOfZ2 h _ _) twMu0_A12 twMuA12_vec twMuA12_hyp

include hK in
theorem q2OmIota_D21_twMu :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt (.difference 2 1 (by decide)) 1) =
      twMu h hK (twG21 h) :=
  twIota_eq_twMu h hK (coe_twTau_twSUOfZ2 h _ _) twMu0_A21 twMuA21_vec twMuA21_hyp

include hK in
theorem q2OmIota_L2_twMu :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt (.positiveLong 2) 1) =
      twMu h hK (twG0123 h) :=
  twIota_eq_twMu h hK (coe_twTau_twSUOfZ2 h _ _) twMu0_A0123 twMuA0123_vec twMuA0123_hyp

theorem twMu_injective : Function.Injective (twMu h hK) := by
  refine twMu_injective_of_ne_one h hK (g₀ := twG03 h) fun h1 => twMuA03Tab_ne_one ?_
  have h2 := congrArg (fun A : StatedOmega (StatedQuadPlus (3 + 1) K) =>
    ((A : GL omPI K) : Matrix omPI omPI K)) h1
  simp only [OneMemClass.coe_one, Units.val_one] at h2
  rw [coe_twMu, coe_twTau_twSUOfZ2, twMu0_A03] at h2
  apply omMat_injective (K := K)
  rw [h2, omMat_one]

end Iota

section Relay

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

variable (K) in
@[expose] noncomputable def twS02SL : SpecialLinearGroup (Fin (3 + 1)) K :=
  ⟨twS02.map (omCast K), by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, twS02_det, map_one]⟩

theorem twS02SL_mem :
    twS02SL K ∈ blockSpecialLinear (K := K) ({0, 1, 2} : Finset (Fin (3 + 1))) := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  have key : ∀ k : Fin (3 + 1), k ∉ ({0, 1, 2} : Finset (Fin (3 + 1))) → k = 3 := by
    intro k hk
    fin_cases k <;> simp_all
  change (twS02.map (omCast K)) i j = (1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) i j
  rw [← omMat_one (K := K), Matrix.map_apply]
  change omCast K (twS02 i j) = omCast K ((1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j)
  congr 1
  rcases hij with hi | hj
  · rw [key i hi]
    exact (twS02_three j).1
  · rw [key j hj]
    exact (twS02_three i).2

theorem coe_twS02SL_inv :
    (((twS02SL K)⁻¹ : SpecialLinearGroup (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) =
      (twS02.map (omCast K))ᵀ := by
  set A := twS02SL K with hA
  have h1 : (A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) * (twS02.map (omCast K))ᵀ = 1 := by
    change twS02.map (omCast K) * (twS02.map (omCast K))ᵀ = 1
    rw [← Matrix.transpose_map, ← Matrix.map_mul, twS02_mul_transpose]
    exact omMat_one
  have h2 : ((A⁻¹ : SpecialLinearGroup (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) *
      (A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul, A.2, one_smul]
  calc ((A⁻¹ : SpecialLinearGroup (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K)
      = ((A⁻¹ : SpecialLinearGroup (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) *
          ((A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) * (twS02.map (omCast K))ᵀ) := by
        rw [h1, Matrix.mul_one]
    _ = (twS02.map (omCast K))ᵀ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem twPi_mem : ((leviEmbedSL K (3 + 1) (twS02SL K) : StatedSp (3 + 1) K) :
    GL (Fin (3 + 1) ⊕ Fin (3 + 1)) K) ∈ StatedOmega (StatedQuadPlus (3 + 1) K) :=
  SymplecticPilot.siegelBlockGL_le_statedOmega_of_three_le (F := K)
    (B := ({0, 1, 2} : Finset (Fin (3 + 1)))) (by decide)
    ⟨_, ⟨twS02SL K, twS02SL_mem, rfl⟩, rfl⟩

variable (K) in
@[expose] noncomputable def twPiK : StatedOmega (StatedQuadPlus (3 + 1) K) :=
  ⟨_, twPi_mem⟩

theorem coe_twPiK :
    (((twPiK K : StatedOmega (StatedQuadPlus (3 + 1) K)) : GL omPI K) : Matrix omPI omPI K) =
      omMat K twPiMat := by
  change mat (3 + 1) K (leviEmbedSL K (3 + 1) (twS02SL K)) = _
  rw [mat_leviEmbedSL, coe_twS02SL_inv, Matrix.transpose_transpose, twPiMat, omMat_fromBlocks]
  simp only [omMat, Matrix.map_zero (omCast K) (map_zero _)]
  rfl

include hK in
theorem q2OmIota_edgePi' :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (edgePi' K) = twPiK K := by
  refine q2OmIota_eq_of_res hK _ _ ?_ ?_
  · rw [coe_twPiK, kOmegaVec_omCast, omMat_mulVec, twPiMat_vec]
  · rw [coe_twPiK, Matrix.submatrix_map, twPiMat_hyp,
      mat_leviEmbedSL_edgeSL3 det_edgeS02 edgeS02_mul_transpose]
    rfl

theorem elt_cPrime_eq_nsElt :
    (elt (.positiveLong 0) (1 : K) * elt (.negativeLong 0) 1 : StatedSp 3 K) = nsElt 0 := by
  apply mat_injective
  rw [map_mul, mat_elt_one, mat_elt_one, ← Matrix.map_mul, edgeSp_cPrime_eq_blockMat, mat_nsElt]
  exact (blockMat_omMat _ _ _).trans (by rw [zThreeMat_omMat])

include hK in
theorem q2OmIota_cPrime :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
      (elt (.positiveLong 0) 1 * elt (.negativeLong 0) 1) = omPXhK hK := by
  rw [elt_cPrime_eq_nsElt]
  exact q2OmIota_nsElt hK

theorem elt_relay_eq_conj :
    elt (.difference 0 1 (by decide)) (1 : K) * elt (.negativeSum 0 1 (by decide)) 1 =
      edgePi' K * (elt (.difference 2 1 (by decide)) 1 * elt (.negativeSum 1 2 (by decide)) 1) *
        edgePi' K := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, mat_leviEmbedSL_edgeSL3 det_edgeS02 edgeS02_mul_transpose]
  rw [← Matrix.map_mul, edgeSp_relay_eq_conj]
  simp only [Matrix.map_mul]

theorem elt_relay'_eq_conj :
    elt (.difference 1 0 (by decide)) (1 : K) * elt (.positiveSum 0 1 (by decide)) 1 =
      edgePi' K * (elt (.difference 1 2 (by decide)) 1 * elt (.positiveSum 1 2 (by decide)) 1) *
        edgePi' K := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, mat_leviEmbedSL_edgeSL3 det_edgeS02 edgeS02_mul_transpose]
  rw [← Matrix.map_mul, edgeSp_relay'_eq_conj]
  simp only [Matrix.map_mul]

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

include h hK in
theorem coe_q2OmIota_relay :
    (((q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
        (elt (.difference 0 1 (by decide)) 1 * elt (.negativeSum 0 1 (by decide)) 1) :
      StatedOmega (StatedQuadPlus (3 + 1) K)) : GL omPI K) : Matrix omPI omPI K) =
      omMat K (omPMat twRuTab) := by
  rw [elt_relay_eq_conj, map_mul, map_mul, map_mul, q2OmIota_edgePi' hK, q2OmIota_D21_twMu h hK,
    q2OmIota_M12_twMu h hK]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_twPiK, coe_twMu, coe_twMu, coe_twTau_twSUOfZ2, coe_twTau_twSUOfZ2, twMu0_A21, twMu0_A30,
    ← twRu_eq]
  simp only [omMat_mul, Matrix.mul_assoc]

include h hK in
theorem coe_q2OmIota_relay' :
    (((q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
        (elt (.difference 1 0 (by decide)) 1 * elt (.positiveSum 0 1 (by decide)) 1) :
      StatedOmega (StatedQuadPlus (3 + 1) K)) : GL omPI K) : Matrix omPI omPI K) =
      omMat K (omPMat twRu'Tab) := by
  rw [elt_relay'_eq_conj, map_mul, map_mul, map_mul, q2OmIota_edgePi' hK, q2OmIota_D12_twMu h hK,
    q2OmIota_P12_twMu h hK]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_twPiK, coe_twMu, coe_twMu, coe_twTau_twSUOfZ2, coe_twTau_twSUOfZ2, twMu0_A12, twMu0_A03,
    ← twRu'_eq]
  simp only [omMat_mul, Matrix.mul_assoc]

theorem twCommute_of_coe {x y : StatedOmega (StatedQuadPlus (3 + 1) K)}
    {X Y : Matrix omPI omPI (ZMod 2)}
    (hx : ((x : GL omPI K) : Matrix omPI omPI K) = omMat K X)
    (hy : ((y : GL omPI K) : Matrix omPI omPI K) = omMat K Y) (hXY : X * Y = Y * X) :
    Commute x y := by
  show _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hx, hy, ← omMat_mul, ← omMat_mul, hXY]

include hK in
theorem commute_q2OmIota_relay_twMu_twX {g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)}
    {a : TwF4} (hg : (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
      Matrix (Fin 4) (Fin 4) TwF4) = twX a) :
    Commute (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
        (elt (.difference 0 1 (by decide)) 1 * elt (.negativeSum 0 1 (by decide)) 1))
      (twMu h hK g) :=
  twCommute_of_coe (coe_q2OmIota_relay hK h) (by rw [coe_twMu, hg]) (twRu_commute_twX a)

include hK in
theorem commute_q2OmIota_relay_twMu_twX' {g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)}
    {a : TwF4} (hg : (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
      Matrix (Fin 4) (Fin 4) TwF4) = twX' a) :
    Commute (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
        (elt (.difference 0 1 (by decide)) 1 * elt (.negativeSum 0 1 (by decide)) 1))
      (twMu h hK g) :=
  twCommute_of_coe (coe_q2OmIota_relay hK h) (by rw [coe_twMu, hg]) (twRu_commute_twX' a)

include hK in
theorem commute_q2OmIota_relay'_twMu_twX {g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)}
    {a : TwF4} (hg : (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
      Matrix (Fin 4) (Fin 4) TwF4) = twX a) :
    Commute (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
        (elt (.difference 1 0 (by decide)) 1 * elt (.positiveSum 0 1 (by decide)) 1))
      (twMu h hK g) :=
  twCommute_of_coe (coe_q2OmIota_relay' hK h) (by rw [coe_twMu, hg]) (twRu'_commute_twX a)

include hK in
theorem commute_q2OmIota_relay'_twMu_twX' {g : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)}
    {a : TwF4} (hg : (((twTau h g : CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
      Matrix (Fin 4) (Fin 4) TwF4) = twX' a) :
    Commute (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
        (elt (.difference 1 0 (by decide)) 1 * elt (.positiveSum 0 1 (by decide)) 1))
      (twMu h hK g) :=
  twCommute_of_coe (coe_q2OmIota_relay' hK h) (by rw [coe_twMu, hg]) (twRu'_commute_twX' a)

end Relay

end CFSG.SeitzReduction.F4Pilot
