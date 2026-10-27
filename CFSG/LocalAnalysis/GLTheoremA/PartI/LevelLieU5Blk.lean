module

public import CFSG.GroupTheory.PCore.JointlyInjective
public import CFSG.GroupTheory.PCore.SelfCentralizing
public import CFSG.LocalAnalysis.GLTheoremA.PartI.SmallSUThreeCore
public import CFSG.RankThree.PartOne.KFCL.BlockSLUnits

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU5

open CFSG CFSG.Open Matrix CFSG.Fischer
open CFSG.LocalAnalysis.GLTheoremA.SmallSUThreeCore
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartOne.KFCL.BlockSL

private noncomputable def blkUnit' {g : M5} {d : Fin 5 → F4}
    (hg : mM5 g = Matrix.diagonal d) (c : F4)
    (x : ↥(Subgroup.centralizer {g})) : GL (Blk d c) F4 :=
  ⟨LevelLieU.blkM d c (mM5 x.1), LevelLieU.blkM d c (mM5 x.1⁻¹),
    by
      rw [← blkM_mul d c (fun i j hij => centralizer_zero hg x hij)
        (fun i j hij => centralizer_zero_inv hg x hij), ← mM5_mul, mul_inv_cancel, mM5_one,
        blkM_one],
    by
      rw [← blkM_mul d c (fun i j hij => centralizer_zero_inv hg x hij)
        (fun i j hij => centralizer_zero hg x hij), ← mM5_mul, inv_mul_cancel, mM5_one,
        blkM_one]⟩

private noncomputable def blkHom' {g : M5} {d : Fin 5 → F4}
    (hg : mM5 g = Matrix.diagonal d) (c : F4) :
    ↥(Subgroup.centralizer {g}) →* GL (Blk d c) F4 :=
  MonoidHom.mk' (blkUnit' hg c) (fun x y => by
    apply Units.ext
    show LevelLieU.blkM d c (mM5 (x * y).1) = LevelLieU.blkM d c (mM5 x.1) * LevelLieU.blkM d c (mM5 y.1)
    rw [Subgroup.coe_mul, mM5_mul]
    exact blkM_mul d c (fun i j hij => centralizer_zero hg x hij)
      (fun i j hij => centralizer_zero hg y hij))

private theorem blkHom'_apply {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) (c : F4)
    (y : ↥(Subgroup.centralizer {g})) :
    ((blkHom' hg c y : GL (Blk d c) F4) : Matrix (Blk d c) (Blk d c) F4) =
      LevelLieU.blkM d c (mM5 y.1) := rfl

private theorem blkPi'_injective {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) :
    Function.Injective (MonoidHom.pi (fun c : F4 => blkHom' hg c)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hblk : ∀ c : F4, LevelLieU.blkM d c (mM5 x.1) = 1 := by
    intro c
    have h1 := congrFun hx c
    simp only [MonoidHom.pi_apply, Pi.one_apply] at h1
    have h2 := congrArg Units.val h1
    rwa [blkHom'_apply] at h2
  have hM : mM5 x.1 = 1 := by
    ext i j
    by_cases hij : d i = d j
    · have h2 := congrFun (congrFun (hblk (d i)) ⟨i, rfl⟩) ⟨j, hij.symm⟩
      simpa [LevelLieU.blkM, Matrix.one_apply, Subtype.ext_iff] using h2
    · rw [centralizer_zero hg x hij, Matrix.one_apply_ne (fun h => hij (by rw [h]))]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [mM5] using hM

private theorem blkHom'_mem_Ucat {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) (c : F4)
    (y : ↥(Subgroup.centralizer {g}))
    (hdet : Matrix.GeneralLinearGroup.det (blkHom' hg c y) = 1) : blkHom' hg c y ∈ Ucat d c := by
  have hd : (LevelLieU.blkM d c (mM5 y.1)).det = 1 := by
    have := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    exact this
  rw [Ucat, Subgroup.mem_comap]
  apply mem_statedSU_of
  · rw [LevelLieU.reindexGL_val, Matrix.det_reindex_self]
    exact hd
  · rw [LevelLieU.reindexGL_val]
    exact reindex_unitary _ _ (blkM_unitary d c (fun i j hij => centralizer_zero hg y hij)
      (M5_unitary y.1))

private theorem ext1GL_mem_M5 (d : Fin 5 → F4) (c : F4) (A : GL (Blk d c) F4)
    (hdet : (A : Matrix (Blk d c) (Blk d c) F4).det = 1)
    (huni : ((A : Matrix (Blk d c) (Blk d c) F4).map bar)ᵀ *
      (A : Matrix (Blk d c) (Blk d c) F4) = 1) :
    (ext1GL (p := fun i => d i = c) A : GL (Fin 5) F4) ∈ StatedSU 5 (2 ^ 1) F4 := by
  rw [mem_M5_iff]
  refine ⟨?_, ?_⟩
  · rw [ext1GL_val, ext1_det, hdet]
  · rw [ext1GL_val]
    exact unitary_ext1 (fun i => d i = c) (A : Matrix (Blk d c) (Blk d c) F4)
      (f := bar) (map_zero bar) (map_one bar) huni

private theorem ext1GL_mem_centralizer {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d)
    (c : F4) (A : GL (Blk d c) F4) (hdet : (A : Matrix (Blk d c) (Blk d c) F4).det = 1)
    (huni : ((A : Matrix (Blk d c) (Blk d c) F4).map bar)ᵀ *
      (A : Matrix (Blk d c) (Blk d c) F4) = 1) :
    (⟨ext1GL (p := fun i => d i = c) A, ext1GL_mem_M5 d c A hdet huni⟩ : M5) ∈
      Subgroup.centralizer ({g} : Set M5) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  show (ext1GL (p := fun i => d i = c) A : Matrix (Fin 5) (Fin 5) F4) * mM5 g =
    mM5 g * (ext1GL (p := fun i => d i = c) A : Matrix (Fin 5) (Fin 5) F4)
  rw [hg, ext1GL_val]
  exact commute_diagonal_ext1 d c (A : Matrix (Blk d c) (Blk d c) F4)

private theorem Ucat_le_range_blkHom' {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d)
    (c : F4) : Ucat d c ≤ (blkHom' hg c).range := by
  intro A hA
  have hdet : (A : Matrix (Blk d c) (Blk d c) F4).det = 1 :=
    det_eq_one_of_mem_comap_reindexGL (ι := Blk d c) hA
  have huni : ((A : Matrix (Blk d c) (Blk d c) F4).map bar)ᵀ *
      (A : Matrix (Blk d c) (Blk d c) F4) = 1 :=
    unitary_of_mem_comap_reindexGL (ι := Blk d c) hA
  let y0 : M5 := ⟨ext1GL (p := fun i => d i = c) A, ext1GL_mem_M5 d c A hdet huni⟩
  have hy0 : y0 ∈ Subgroup.centralizer ({g} : Set M5) :=
    ext1GL_mem_centralizer hg c A hdet huni
  refine ⟨⟨y0, hy0⟩, ?_⟩
  apply Units.ext
  rw [blkHom'_apply]
  have hy0mat : mM5 y0 = ext1 (fun i => d i = c) (A : Matrix (Blk d c) (Blk d c) F4) :=
    ext1GL_val A
  rw [hy0mat]
  ext i j
  show ext1 (fun i => d i = c) (A : Matrix (Blk d c) (Blk d c) F4) i.1 j.1 =
    (A : Matrix (Blk d c) (Blk d c) F4) i j
  rw [ext1_apply, dif_pos ⟨i.2, j.2⟩]

private theorem mem_Ucat_iff_det {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) (c : F4)
    {y : GL (Blk d c) F4} (hy : y ∈ (blkHom' hg c).range) :
    y ∈ Ucat d c ↔ (y : Matrix (Blk d c) (Blk d c) F4).det = 1 := by
  constructor
  · intro h
    exact det_eq_one_of_mem_comap_reindexGL (ι := Blk d c) h
  · intro hdet
    obtain ⟨z, rfl⟩ := hy
    exact blkHom'_mem_Ucat hg c z (by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact hdet)

theorem pPrimeCore_centralizer_diag_eq_bot {g : M5} {d : Fin 5 → F4}
    (hg : mM5 g = Matrix.diagonal d)
    (hcnt : ∀ x : F4, (Finset.univ.filter fun i => d i = x).card ≤ 3) :
    pPrimeCore 3 ↥(Subgroup.centralizer ({g} : Set M5)) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ∀ c : F4, Fintype.card (Blk d c) ≤ 3 := fun c => by
    rw [Fintype.card_subtype]
    exact hcnt c
  refine CFSG.pPrimeCore_eq_bot_of_pi_range_eq_bot (fun c => blkHom' hg c)
    (blkPi'_injective hg) (fun c => ?_)
  exact pPrimeCore_eq_bot_of_det_eq_one (Ucat_le_range_blkHom' hg c)
    (fun y hy => mem_Ucat_iff_det hg c hy)
    (pPrimeCore_comap_reindexGL_statedSU_eq_bot (ι := Blk d c) (by have := hcard c; omega))

theorem odd_card_centralizer_diag {g : M5} {d : Fin 5 → F4}
    (hg : mM5 g = Matrix.diagonal d)
    (hcnt : ∀ x : F4, (Finset.univ.filter fun i => d i = x).card ≤ 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({g} : Set M5)))) := by
  have h := pPrimeCore_centralizer_diag_eq_bot hg hcnt
  have hcore : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({g} : Set M5)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr h
  rw [hcore, Subgroup.card_bot]
  exact odd_one

theorem odd_card_centralizer_yM5 :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({yM5} : Set M5)))) := by
  obtain ⟨Kb, hKbC, hsup, hdisj, hsimple, -, h3dvd, -⟩ := m5_u4_layer
  have hKbCore : GLAPPrimeCoreOf 3 Kb = ⊥ := by
    have hb : CFSG.pPrimeCore 3 ↥Kb = ⊥ :=
      gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three hsimple h3dvd
    exact gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hb
  have hcomm : ∀ k ∈ Kb, k * yM5 = yM5 * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKbC hk)
  have hyNorm : yM5 ∈ Subgroup.normalizer Kb :=
    Subgroup.centralizer_le_normalizer (Kb : Set M5) (by
      rw [Subgroup.mem_centralizer_iff]
      exact hcomm)
  have hCnorm : Subgroup.centralizer ({yM5} : Set M5) ≤ Subgroup.normalizer Kb := by
    rw [hsup]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hyNorm)
  have hnorm : (Kb.subgroupOf (Subgroup.centralizer ({yM5} : Set M5))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKbC).2 hCnorm
  have hcardSup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Kb
    (Subgroup.zpowers yM5) (Subgroup.zpowers_le.mpr hyNorm) (disjoint_iff.mpr hdisj)
  have hcardC : Nat.card (Subgroup.centralizer ({yM5} : Set M5)) = Nat.card Kb * 3 := by
    rw [hsup, hcardSup, Nat.card_zpowers, orderOf_eq_prime yM5_pow_three yM5_ne_one]
  have hindex : Kb.relIndex (Subgroup.centralizer ({yM5} : Set M5)) = 3 := by
    have hmul := (Kb.subgroupOf (Subgroup.centralizer ({yM5} : Set M5))).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbC).toEquiv, hcardC] at hmul
    exact Nat.mul_left_cancel Nat.card_pos hmul
  have hcore : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({yM5} : Set M5)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_relIndex_eq_pow Nat.prime_three hKbC hnorm
      (by rw [hindex, pow_one]) hKbCore
  rw [hcore, Subgroup.card_bot]
  exact odd_one

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU5
