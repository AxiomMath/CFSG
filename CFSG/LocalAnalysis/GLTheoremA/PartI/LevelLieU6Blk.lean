module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem perfect_hom_trivial {J G : Type} [Group J] [Group G] [Group.IsPerfect J]
    [Group.IsSolvable G] (φ : J →* G) (x : J) : φ x = 1 := by
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  haveI : Group.IsSolvable φ.range := solvable_of_solvable_injective φ.range.subtype_injective
  haveI : Subsingleton φ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  have := Subsingleton.elim (⟨φ x, ⟨x, rfl⟩⟩ : φ.range) 1
  simpa using congrArg Subtype.val this

abbrev Blk {n : ℕ} (d : Fin n → F4) (c : F4) : Type := {i : Fin n // d i = c}

@[expose] def blkM {n : ℕ} (d : Fin n → F4) (c : F4) (M : Matrix (Fin n) (Fin n) F4) :
    Matrix (Blk d c) (Blk d c) F4 :=
  fun i j => M i.1 j.1

theorem zero_of_commute_diag {n : ℕ} {d : Fin n → F4} {M : Matrix (Fin n) (Fin n) F4}
    (hM : M * Matrix.diagonal d = Matrix.diagonal d * M) {i j : Fin n} (hij : d i ≠ d j) :
    M i j = 0 := by
  have h := congrFun (congrFun hM i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : M i j * (d j - d i) = 0 := by
    rw [mul_sub, h, mul_comm (d i), sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hij

theorem sum_blk {n : ℕ} (d : Fin n → F4) (c : F4) (f : Fin n → F4) (hf : ∀ k, d k ≠ c → f k = 0) :
    ∑ k, f k = ∑ k : Blk d c, f k.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun k => d k = c) (by simp) f,
    Finset.sum_filter_of_ne]
  intro x _ hx
  by_contra h
  exact hx (hf x h)

theorem blkM_mul {n : ℕ} (d : Fin n → F4) (c : F4) {M N : Matrix (Fin n) (Fin n) F4}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) (hN : ∀ i j, d i ≠ d j → N i j = 0) :
    blkM d c (M * N) = blkM d c M * blkM d c N := by
  ext i j
  simp only [blkM, Matrix.mul_apply]
  rw [sum_blk d c (fun k => M i.1 k * N k j.1)]
  intro k hk
  have hi : d i.1 ≠ d k := by rw [i.2]; exact fun h => hk h.symm
  simp [hM i.1 k hi]

theorem blkM_one {n : ℕ} (d : Fin n → F4) (c : F4) : blkM d c 1 = 1 := by
  ext i j
  simp only [blkM, Matrix.one_apply, Subtype.ext_iff]

theorem blkM_unitary {n : ℕ} (d : Fin n → F4) (c : F4) {M : Matrix (Fin n) (Fin n) F4}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) (hU : (M.map bar).transpose * M = 1) :
    ((blkM d c M).map bar).transpose * blkM d c M = 1 := by
  ext i j
  have h := congrFun (congrFun hU i.1) j.1
  rw [Matrix.mul_apply] at h
  have hz : ∀ k : Fin n, d k ≠ c → bar (M k i.1) * M k j.1 = 0 := by
    intro k hk
    rw [hM k j.1 (by rw [j.2]; exact hk), mul_zero]
  have hs := sum_blk d c (fun k => bar (M k i.1) * M k j.1) hz
  simp only [Matrix.transpose_apply, Matrix.map_apply] at h
  simp only [blkM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [← hs, h]
  simp [Matrix.one_apply, Subtype.ext_iff]

theorem M6_unitary (x : M6) : ((mM6 x).map bar).transpose * mM6 x = 1 := by
  have h := ((mem_unitarySU_iff hF4).1 x.2).2
  rwa [hF4_bar] at h

theorem mM6_mul (a b : M6) : mM6 (a * b) = mM6 a * mM6 b := rfl

theorem mM6_one : mM6 (1 : M6) = 1 := rfl

theorem mM6_inv (a : M6) : mM6 a⁻¹ = (mM6 a)⁻¹ :=
  (Matrix.inv_eq_left_inv (by rw [← mM6_mul, inv_mul_cancel, mM6_one])).symm

variable {D : GL (Fin 6) F4} {d : Fin 6 → F4}

theorem CenD_zero (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (x : ↥(CenD D)) {i j : Fin 6} (hij : d i ≠ d j) : mM6 x.1 i j = 0 := by
  apply zero_of_commute_diag _ hij
  have hx := mem_CenD.1 x.2
  rw [← hD]
  exact congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) hx

@[expose] noncomputable def blkUnit (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (c : F4) (x : ↥(CenD D)) : GL (Blk d c) F4 :=
  ⟨blkM d c (mM6 x.1), blkM d c (mM6 x.1⁻¹),
    by
      rw [← blkM_mul d c (M := mM6 x.1) (N := mM6 x.1⁻¹) (fun i j hij => CenD_zero hD x hij)
        (fun i j hij => CenD_zero hD x⁻¹ hij), ← mM6_mul, mul_inv_cancel, mM6_one, blkM_one],
    by
      rw [← blkM_mul d c (M := mM6 x.1⁻¹) (N := mM6 x.1) (fun i j hij => CenD_zero hD x⁻¹ hij)
        (fun i j hij => CenD_zero hD x hij), ← mM6_mul, inv_mul_cancel, mM6_one, blkM_one]⟩

@[expose] noncomputable def blkHom (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (c : F4) : ↥(CenD D) →* GL (Blk d c) F4 :=
  MonoidHom.mk' (blkUnit hD c) (fun x y => by
    apply Units.ext
    show blkM d c (mM6 (x * y).1) = blkM d c (mM6 x.1) * blkM d c (mM6 y.1)
    rw [Subgroup.coe_mul, mM6_mul]
    exact blkM_mul d c (fun i j hij => CenD_zero hD x hij) (fun i j hij => CenD_zero hD y hij))

theorem blkHom_val (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (c : F4)
    (x : ↥(CenD D)) : ((blkHom hD c x : GL (Blk d c) F4) : Matrix (Blk d c) (Blk d c) F4) =
      blkM d c (mM6 x.1) := rfl

theorem blkPi_injective (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) :
    Function.Injective (MonoidHom.pi (fun c : F4 => blkHom hD c)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hblk : ∀ c : F4, blkM d c (mM6 x.1) = 1 := by
    intro c
    have h1 := congrFun hx c
    simp only [MonoidHom.pi_apply, Pi.one_apply] at h1
    exact congrArg Units.val h1
  have hM : mM6 x.1 = 1 := by
    ext i j
    by_cases hij : d i = d j
    · have h2 := congrFun (congrFun (hblk (d i)) ⟨i, rfl⟩) ⟨j, hij.symm⟩
      simpa [blkM, Matrix.one_apply, Subtype.ext_iff] using h2
    · rw [CenD_zero hD x hij, Matrix.one_apply_ne (fun h => hij (by rw [h]))]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [mM6] using hM

theorem det_blk_of_perfect (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    {J : Subgroup M6} (hJ : J ≤ CenD D) (hperf : ⁅J, J⁆ = J) (c : F4) {u : M6} (hu : u ∈ J) :
    (blkM d c (mM6 u)).det = 1 := by
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
  let φ : ↥J →* F4ˣ :=
    (Matrix.GeneralLinearGroup.det).comp ((blkHom hD c).comp (Subgroup.inclusion hJ))
  have h := perfect_hom_trivial φ ⟨u, hu⟩
  have h1 := congrArg Units.val h
  simpa [φ, Matrix.GeneralLinearGroup.val_det_apply, blkHom_val] using h1

theorem blk_eq_one_of_small (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    {J : Subgroup M6} (hJ : J ≤ CenD D) (hperf : ⁅J, J⁆ = J) (c : F4)
    (hc : Fintype.card (Blk d c) ≤ 3) {u : M6} (hu : u ∈ J) : blkHom hD c ⟨u, hJ hu⟩ = 1 := by
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
  let e := Fintype.equivFin (Blk d c)
  have hmem : ∀ x : ↥J, reindexGL e (blkHom hD c ⟨x.1, hJ x.2⟩) ∈
      StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4 := by
    intro x
    apply mem_statedSU_of
    · rw [reindexGL_val, Matrix.det_reindex_self]
      exact det_blk_of_perfect hD hJ hperf c x.2
    · rw [reindexGL_val]
      exact reindex_unitary _ _ (blkM_unitary d c (fun i j hij => CenD_zero hD ⟨x.1, hJ x.2⟩ hij)
        (M6_unitary x.1))
  let ψ : ↥J →* ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) :=
    ((reindexGL e).comp ((blkHom hD c).comp (Subgroup.inclusion hJ))).codRestrict _ hmem
  haveI := isSolvable_statedSU_le_three _ hc
  have h := perfect_hom_trivial ψ ⟨u, hu⟩
  have h1 : reindexGL e (blkHom hD c ⟨u, hJ hu⟩) = 1 := congrArg Subtype.val h
  exact reindexGL_injective e (by rw [h1, map_one])

theorem eq_bot_of_perfect_of_small (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (hcnt : ∀ c : F4, Fintype.card (Blk d c) ≤ 3) {J : Subgroup M6} (hJ : J ≤ CenD D)
    (hperf : ⁅J, J⁆ = J) : J = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  have h : (⟨u, hJ hu⟩ : ↥(CenD D)) = 1 := by
    apply blkPi_injective hD
    funext c
    simp only [MonoidHom.pi_apply, map_one, Pi.one_apply]
    exact blk_eq_one_of_small hD hJ hperf c (hcnt c) hu
  exact congrArg Subtype.val h

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
