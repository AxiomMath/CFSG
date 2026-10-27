module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Rel
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelBasic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam comm_famL₂ fuel)
open scoped commutatorElement

section Commutators

variable {K : Type} [Field K] {a : ℕ}

local notation "σ" => largeReeSigma a

theorem rootElt_i3_eq_fam (u : K) :
    rootElt K a .i3 u = fam a K 0 u := rfl

theorem rootElt_i1_eq_fam (u : K) :
    rootElt K a .i1 u = fam a K 1 u := rfl

theorem rootElt_i2_eq_fam (u : K) :
    rootElt K a .i2 u = fam a K 2 u := rfl

theorem rootElt_i4_eq_fam (u : K) :
    rootElt K a .i4 u = fam a K 3 u := rfl

theorem rootElt_i8_eq_fam (u : K) :
    rootElt K a .i8 u = fam a K 4 u := rfl

theorem rootElt_i6_eq_fam (u : K) :
    rootElt K a .i6 u = fam a K 5 u := rfl

theorem rootElt_i11_eq_fam (u : K) :
    rootElt K a .i11 u = fam a K 6 u := rfl

theorem rootElt_i5_eq_fam (u : K) :
    rootElt K a .i5 u = fam a K 7 u := rfl

theorem rootElt_i12_eq_fam (u : K) :
    rootElt K a .i12 u = fam a K 8 u := rfl

theorem rootElt_i7_eq_fam (u : K) :
    rootElt K a .i7 u = fam a K 9 u := rfl

theorem rootElt_i9_eq_fam (u : K) :
    rootElt K a .i9 u = fam a K 10 u := rfl

theorem rootElt_i10_eq_fam (u : K) :
    rootElt K a .i10 u = fam a K 11 u := rfl

variable [CharP K F4.prime] [Finite K]

theorem rootElt_comm_3_1 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i1 t⁆ =
      rootElt K a .i4 (s * t) *
      rootElt K a .i7 (s * (t * (t * σ t))) *
      rootElt K a .i5 (t * (σ s * σ t)) *
      rootElt K a .i9 (s * (t * (t * (σ s * σ t)))) *
      rootElt K a .i10 (s * (t * (t * (σ s * (σ t * σ t))))) *
      rootElt K a .i12 (s * (s * (t * (t * (t * (σ s * (σ t * σ t))))))) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 1) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(3, [[0, 1]]), (9, [[0, 1, 1, 13]]), (7, [[1, 12, 13]]),
      (10, [[0, 1, 1, 12, 13]]), (11, [[0, 1, 1, 12, 13, 13]]),
      (8, [[0, 0, 1, 1, 1, 12, 13, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i1_eq_fam, rootElt_i4_eq_fam, rootElt_i5_eq_fam,
    rootElt_i12_eq_fam, rootElt_i7_eq_fam, rootElt_i9_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_2 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i2 t⁆ =
      rootElt K a .i6 (s * t) *
      rootElt K a .i7 (s * σ t) *
      rootElt K a .i5 (t * σ s) *
      rootElt K a .i8 (s * (t * σ s)) *
      rootElt K a .i9 (s * (σ s * σ t)) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 2) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(5, [[0, 1]]), (9, [[0, 13]]), (7, [[1, 12]]), (4, [[0, 1, 12]]),
      (10, [[0, 12, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i2_eq_fam, rootElt_i8_eq_fam, rootElt_i6_eq_fam,
    rootElt_i5_eq_fam, rootElt_i7_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_4 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i4 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 3) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i4_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_8 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i8 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 4) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i8_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_6 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i6 t⁆ =
      rootElt K a .i8 (t * σ s) *
      rootElt K a .i9 (s * σ t) *
      rootElt K a .i12 (s * (t * σ t)) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 5) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(4, [[1, 12]]), (10, [[0, 13]]), (8, [[0, 1, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i8_eq_fam, rootElt_i6_eq_fam, rootElt_i12_eq_fam,
    rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i11 t⁆ =
      rootElt K a .i12 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i11_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_5 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i5 t⁆ =
      rootElt K a .i8 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(4, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i8_eq_fam, rootElt_i5_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i7 t⁆ =
      rootElt K a .i9 (t * σ s) *
      rootElt K a .i10 (s * σ t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(10, [[1, 12]]), (11, [[0, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i7_eq_fam, rootElt_i9_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_3_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i3_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_1_4 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i1 s, rootElt K a .i4 t⁆ =
      rootElt K a .i6 (t * σ s) *
      rootElt K a .i7 (s * (t * σ s)) *
      rootElt K a .i5 (s * σ t) *
      rootElt K a .i9 (s * (t * σ t)) *
      rootElt K a .i11 (s * (s * (t * (σ s * σ t)))) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 3) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(5, [[1, 12]]), (9, [[0, 1, 12]]), (7, [[0, 13]]), (10, [[0, 1, 13]]),
      (6, [[0, 0, 1, 12, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i1_eq_fam, rootElt_i4_eq_fam, rootElt_i6_eq_fam, rootElt_i11_eq_fam,
    rootElt_i5_eq_fam, rootElt_i7_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_1_8 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i1 s, rootElt K a .i8 t⁆ =
      rootElt K a .i9 (s * t) *
      rootElt K a .i11 (s * (s * (t * σ s))) *
      rootElt K a .i12 (s * (σ s * σ t)) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 4) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(10, [[0, 1]]), (6, [[0, 0, 1, 12]]), (8, [[0, 12, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i1_eq_fam, rootElt_i8_eq_fam, rootElt_i11_eq_fam, rootElt_i12_eq_fam,
    rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_1_11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i1 s, rootElt K a .i11 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i1_eq_fam, rootElt_i11_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_1_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i1 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i1_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_1_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i1 s, rootElt K a .i9 t⁆ =
      rootElt K a .i10 (t * σ s) *
      rootElt K a .i11 (s * (t * σ s)) *
      rootElt K a .i12 (s * σ t) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(11, [[1, 12]]), (6, [[0, 1, 12]]), (8, [[0, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i1_eq_fam, rootElt_i11_eq_fam, rootElt_i12_eq_fam, rootElt_i9_eq_fam,
    rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_1_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i1 s, rootElt K a .i10 t⁆ =
      rootElt K a .i11 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(6, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i1_eq_fam, rootElt_i11_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_8 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i8 t⁆ =
      rootElt K a .i10 (s * t) *
      rootElt K a .i11 (t * σ s) *
      rootElt K a .i12 (s * σ t) := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 4) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(11, [[0, 1]]), (6, [[1, 12]]), (8, [[0, 13]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i8_eq_fam, rootElt_i11_eq_fam, rootElt_i12_eq_fam,
    rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_6 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i6 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 5) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i6_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i11 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i11_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_5 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i5 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i5_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i9 t⁆ =
      rootElt K a .i11 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(6, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i11_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_2_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i2 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i2_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_8 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i8 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 4) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i8_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_6 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i6 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 5) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i6_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i11 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i11_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_5 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i5 t⁆ =
      rootElt K a .i9 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(10, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i5_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i7 t⁆ =
      rootElt K a .i10 (t * σ s) *
      rootElt K a .i11 (s * σ t) *
      rootElt K a .i12 (s * (t * σ s)) := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(11, [[1, 12]]), (6, [[0, 13]]), (8, [[0, 1, 12]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i11_eq_fam, rootElt_i12_eq_fam, rootElt_i7_eq_fam,
    rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_4_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i4 s, rootElt K a .i10 t⁆ =
      rootElt K a .i12 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i4_eq_fam, rootElt_i12_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_6 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i6 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 5) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i6_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i11 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i11_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_5 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i5 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i5_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i7 t⁆ =
      rootElt K a .i12 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i12_eq_fam, rootElt_i7_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_8_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i8 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 4) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i8_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_6_11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i6 s, rootElt K a .i11 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 5) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i6_eq_fam, rootElt_i11_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_6_5 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i6 s, rootElt K a .i5 t⁆ =
      rootElt K a .i10 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 5) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(11, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i6_eq_fam, rootElt_i5_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_6_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i6 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 5) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i6_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_6_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i6 s, rootElt K a .i7 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 5) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i6_eq_fam, rootElt_i7_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_6_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i6 s, rootElt K a .i9 t⁆ =
      rootElt K a .i12 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 5) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i6_eq_fam, rootElt_i12_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_6_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i6 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 5) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i6_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_11_5 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i11 s, rootElt K a .i5 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 6) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i11_eq_fam, rootElt_i5_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_11_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i11 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 6) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i11_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_11_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i11 s, rootElt K a .i7 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 6) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i11_eq_fam, rootElt_i7_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_11_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i11 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 6) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i11_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_11_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i11 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 6) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i11_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_5_12 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i5 s, rootElt K a .i12 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 7) (j := 8) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i5_eq_fam, rootElt_i12_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_5_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i5 s, rootElt K a .i7 t⁆ =
      rootElt K a .i11 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 7) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(6, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i11_eq_fam, rootElt_i5_eq_fam, rootElt_i7_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_5_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i5 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 7) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i5_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_5_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i5 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 7) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i5_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_12_7 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i12 s, rootElt K a .i7 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 8) (j := 9) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i12_eq_fam, rootElt_i7_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_12_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i12 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 8) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i12_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_12_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i12 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 8) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i12_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_7_9 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i7 s, rootElt K a .i9 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 9) (j := 10) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i7_eq_fam, rootElt_i9_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_7_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i7 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 9) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i7_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rootElt_comm_9_10 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i9 s, rootElt K a .i10 t⁆ =
      1 := by
  have := comm_famL₂ hK (n := fuel) (i := 10) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := []) (by decide)
    (by decide +kernel) s t
  simp only [rootElt_i9_eq_fam, rootElt_i10_eq_fam]
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

end Commutators

end CFSG.LocalAnalysis.EvenBN.TwoF4
