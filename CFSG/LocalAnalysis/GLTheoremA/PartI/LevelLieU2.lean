module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU

open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer CFSG.Open
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.RankThree.SubgroupLists (card_statedSU_two)

abbrev Blk (d : Fin 5 → F4) (c : F4) : Type := {i : Fin 5 // d i = c}

@[expose] def blkM (d : Fin 5 → F4) (c : F4) (M : Matrix (Fin 5) (Fin 5) F4) :
    Matrix (Blk d c) (Blk d c) F4 :=
  fun i j => M i.1 j.1

theorem zero_of_commute_diag {d : Fin 5 → F4} {M : Matrix (Fin 5) (Fin 5) F4}
    (hM : M * Matrix.diagonal d = Matrix.diagonal d * M) {i j : Fin 5} (hij : d i ≠ d j) :
    M i j = 0 := by
  have h := congrFun (congrFun hM i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : M i j * (d j - d i) = 0 := by
    rw [mul_sub, h, mul_comm (d i), sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hij

theorem sum_blk (d : Fin 5 → F4) (c : F4) (f : Fin 5 → F4) (hf : ∀ k, d k ≠ c → f k = 0) :
    ∑ k, f k = ∑ k : Blk d c, f k.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun k => d k = c) (by simp) f,
    Finset.sum_filter_of_ne]
  intro x _ hx
  by_contra h
  exact hx (hf x h)

theorem blkM_mul (d : Fin 5 → F4) (c : F4) {M N : Matrix (Fin 5) (Fin 5) F4}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) (hN : ∀ i j, d i ≠ d j → N i j = 0) :
    blkM d c (M * N) = blkM d c M * blkM d c N := by
  ext i j
  simp only [blkM, Matrix.mul_apply]
  rw [sum_blk d c (fun k => M i.1 k * N k j.1)]
  intro k hk
  have hi : d i.1 ≠ d k := by rw [i.2]; exact fun h => hk h.symm
  simp [hM i.1 k hi]

theorem blkM_one (d : Fin 5 → F4) (c : F4) : blkM d c 1 = 1 := by
  ext i j
  simp only [blkM, Matrix.one_apply, Subtype.ext_iff]

theorem blkM_unitary (d : Fin 5 → F4) (c : F4) {M : Matrix (Fin 5) (Fin 5) F4}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) (hU : (M.map bar).transpose * M = 1) :
    ((blkM d c M).map bar).transpose * blkM d c M = 1 := by
  ext i j
  have h := congrFun (congrFun hU i.1) j.1
  rw [Matrix.mul_apply] at h
  have hz : ∀ k : Fin 5, d k ≠ c → bar (M k i.1) * M k j.1 = 0 := by
    intro k hk
    rw [hM k j.1 (by rw [j.2]; exact hk), mul_zero]
  have hs := sum_blk d c (fun k => bar (M k i.1) * M k j.1) hz
  simp only [Matrix.transpose_apply, Matrix.map_apply] at h
  simp only [blkM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [← hs, h]
  simp [Matrix.one_apply, Subtype.ext_iff]

theorem eq_one_of_subsingleton {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι]
    (A : GL ι F4) (h : (A : Matrix ι ι F4).det = 1) : A = 1 := by
  apply Units.ext
  ext i j
  rw [Subsingleton.elim i j, Units.val_one, Matrix.one_apply_eq]
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · exact isEmptyElim j
  · haveI : Unique ι := uniqueOfSubsingleton a
    rw [Matrix.det_unique] at h
    rw [Subsingleton.elim j default]
    simpa using h

theorem det_one_of_mem_statedSU {n : ℕ} (hn : 1 ≤ n) (A : GL (Fin n) F4)
    (h : A ∈ StatedSU n (2 ^ 1) F4) : (A : Matrix (Fin n) (Fin n) F4).det = 1 := by
  have hset := (CFSG.LinearGroups.unitary_scalar_kernel (K := F4) (p := 2) (f := 1) Nat.prime_two
    hF4card (n := n) hn).1
  have hA : A ∈ (StatedSU n (2 ^ 1) F4 : Set (GL (Fin n) F4)) := h
  rw [hset] at hA
  exact hA.1

@[expose] def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : GL ι F4 →* GL κ F4 :=
  Units.map (Matrix.reindexAlgEquiv F4 F4 e).toRingEquiv.toMonoidHom

theorem reindexGL_injective {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : Function.Injective (reindexGL e) :=
  Units.map_injective (RingEquiv.injective _)

theorem reindexGL_val {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : GL ι F4) :
    ((reindexGL e A : GL κ F4) : Matrix κ κ F4) = Matrix.reindex e e (A : Matrix ι ι F4) := rfl

@[expose] noncomputable def Ucat (d : Fin 5 → F4) (c : F4) :
    Subgroup (GL (Blk d c) F4) :=
  (StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4).comap
    (reindexGL (Fintype.equivFin (Blk d c)))

theorem isSolvable_statedSU_le_three (k : ℕ) (hk : k ≤ 3) :
    Group.IsSolvable ↥(StatedSU k (2 ^ 1) F4) := by
  interval_cases k
  · haveI : Subsingleton ↥(StatedSU 0 (2 ^ 1) F4) :=
      ⟨fun a b => Subtype.ext (by
        rw [eq_one_of_subsingleton (a : GL (Fin 0) F4) (Matrix.det_isEmpty),
          eq_one_of_subsingleton (b : GL (Fin 0) F4) (Matrix.det_isEmpty)])⟩
    infer_instance
  · haveI : Subsingleton ↥(StatedSU 1 (2 ^ 1) F4) :=
      ⟨fun a b => Subtype.ext (by
        rw [eq_one_of_subsingleton (a : GL (Fin 1) F4) (det_one_of_mem_statedSU le_rfl _ a.2),
          eq_one_of_subsingleton (b : GL (Fin 1) F4) (det_one_of_mem_statedSU le_rfl _ b.2)])⟩
    infer_instance
  · have h := card_statedSU_two (K := F4) (r := 2) (f := 1) hF4card
    apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    rw [h, show (2 : ℕ) ^ 1 * ((2 ^ 1) ^ 2 - 1) = 6 from rfl]
    have h6 : Nat.primeFactors 6 = {2, 3} := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
      rfl
    rw [h6]
    simp
  · exact CFSG.Quasithin.isSolvable_statedSU_one hF4card

theorem M5_unitary (x : M5) : ((mM5 x).map bar).transpose * mM5 x = 1 := by
  have h := (mem_M5_iff.1 x.2).2
  have hfun : (fun c : F4 => c ^ 2 ^ 1) = bar := funext fun c => by rw [bar_apply]; norm_num
  rw [hfun] at h
  exact h

theorem mM5_mul (a b : M5) : mM5 (a * b) = mM5 a * mM5 b := rfl

theorem mM5_one : mM5 (1 : M5) = 1 := rfl

theorem centralizer_zero {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d)
    (x : ↥(Subgroup.centralizer {g})) {i j : Fin 5} (hij : d i ≠ d j) :
    mM5 x.1 i j = 0 := by
  apply zero_of_commute_diag _ hij
  have hx : x.1 * g = g * x.1 := Subgroup.mem_centralizer_singleton_iff.1 x.2
  rw [← hg]
  exact congrArg mM5 hx

theorem centralizer_zero_inv {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d)
    (x : ↥(Subgroup.centralizer {g})) {i j : Fin 5} (hij : d i ≠ d j) :
    mM5 x.1⁻¹ i j = 0 :=
  centralizer_zero hg x⁻¹ hij

noncomputable def blkUnit {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) (c : F4)
    (x : ↥(Subgroup.centralizer {g})) : GL (Blk d c) F4 :=
  ⟨blkM d c (mM5 x.1), blkM d c (mM5 x.1⁻¹),
    by
      rw [← blkM_mul d c (fun i j hij => centralizer_zero hg x hij)
        (fun i j hij => centralizer_zero_inv hg x hij), ← mM5_mul, mul_inv_cancel, mM5_one,
        blkM_one],
    by
      rw [← blkM_mul d c (fun i j hij => centralizer_zero_inv hg x hij)
        (fun i j hij => centralizer_zero hg x hij), ← mM5_mul, inv_mul_cancel, mM5_one,
        blkM_one]⟩

theorem mem_statedSU_of (k : ℕ) (A : GL (Fin k) F4)
    (hdet : (A : Matrix (Fin k) (Fin k) F4).det = 1)
    (hU : ((A : Matrix (Fin k) (Fin k) F4).map bar).transpose * (A : Matrix (Fin k) (Fin k) F4) = 1) :
    A ∈ StatedSU k (2 ^ 1) F4 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [eq_one_of_subsingleton A hdet]
    exact Subgroup.one_mem _
  · have hset := (CFSG.LinearGroups.unitary_scalar_kernel (K := F4) (p := 2) (f := 1)
      Nat.prime_two hF4card (n := k) hk).1
    have hfun : (fun c : F4 => c ^ 2 ^ 1) = bar := funext fun c => by rw [bar_apply]; norm_num
    have hA : A ∈ (StatedSU k (2 ^ 1) F4 : Set (GL (Fin k) F4)) := by
      rw [hset]
      refine ⟨hdet, ?_⟩
      rw [hfun]
      exact hU
    exact hA

theorem reindex_unitary {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι F4) (h : ((M.map bar).transpose) * M = 1) :
    (((Matrix.reindex e e M).map bar).transpose) * Matrix.reindex e e M = 1 := by
  ext a b
  have hab := congrFun (congrFun h (e.symm a)) (e.symm b)
  rw [Matrix.mul_apply] at hab
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at hab
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [show (∑ x, bar (M (e.symm x) (e.symm a)) * M (e.symm x) (e.symm b)) =
    ∑ x, bar (M x (e.symm a)) * M x (e.symm b) from
      Equiv.sum_comp e.symm (fun x => bar (M x (e.symm a)) * M x (e.symm b)), hab]
  simp [Equiv.apply_eq_iff_eq]

noncomputable def blkHom {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) (c : F4) :
    ↥(Subgroup.centralizer {g}) →* GL (Blk d c) F4 :=
  MonoidHom.mk' (blkUnit hg c) (fun x y => by
    apply Units.ext
    show blkM d c (mM5 (x * y).1) = blkM d c (mM5 x.1) * blkM d c (mM5 y.1)
    rw [Subgroup.coe_mul, mM5_mul]
    exact blkM_mul d c (fun i j hij => centralizer_zero hg x hij)
      (fun i j hij => centralizer_zero hg y hij))

theorem blkPi_injective {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) :
    Function.Injective (MonoidHom.pi (fun c : F4 => blkHom hg c)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hblk : ∀ c : F4, blkM d c (mM5 x.1) = 1 := by
    intro c
    have h1 := congrFun hx c
    simp only [MonoidHom.pi_apply, Pi.one_apply] at h1
    exact congrArg Units.val h1
  have hM : mM5 x.1 = 1 := by
    ext i j
    by_cases hij : d i = d j
    · have h2 := congrFun (congrFun (hblk (d i)) ⟨i, rfl⟩) ⟨j, hij.symm⟩
      simpa [blkM, Matrix.one_apply, Subtype.ext_iff] using h2
    · rw [centralizer_zero hg x hij, Matrix.one_apply_ne (fun h => hij (by rw [h]))]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [mM5] using hM

noncomputable def detHom {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) :
    ↥(Subgroup.centralizer {g}) →* ∀ c : F4, (F4)ˣ :=
  MonoidHom.pi (fun c => Matrix.GeneralLinearGroup.det.comp (blkHom hg c))

theorem isSolvable_Ucat (d : Fin 5 → F4) (c : F4) (hc : Fintype.card (Blk d c) ≤ 3) :
    Group.IsSolvable ↥(Ucat d c) := by
  let ψ : ↥(Ucat d c) →* ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) :=
    MonoidHom.codRestrict ((reindexGL (Fintype.equivFin (Blk d c))).comp (Ucat d c).subtype)
      _ (fun x => x.2)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    exact reindexGL_injective _ (congrArg Subtype.val hxy)
  haveI := isSolvable_statedSU_le_three _ hc
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem blkHom_mem_Ucat {g : M5} {d : Fin 5 → F4} (hg : mM5 g = Matrix.diagonal d) (c : F4)
    (y : ↥(Subgroup.centralizer {g}))
    (hdet : Matrix.GeneralLinearGroup.det (blkHom hg c y) = 1) : blkHom hg c y ∈ Ucat d c := by
  have hd : (blkM d c (mM5 y.1)).det = 1 := by
    have := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    exact this
  rw [Ucat, Subgroup.mem_comap]
  apply mem_statedSU_of
  · rw [reindexGL_val, Matrix.det_reindex_self]
    exact hd
  · rw [reindexGL_val]
    exact reindex_unitary _ _ (blkM_unitary d c (fun i j hij => centralizer_zero hg y hij)
      (M5_unitary y.1))

theorem centralizer_diag_solvable (g : M5) (d : Fin 5 → F4) (hg : mM5 g = Matrix.diagonal d)
    (hcnt : ∀ x : F4, (Finset.univ.filter fun i => d i = x).card ≤ 3) :
    Group.IsSolvable ↥(Subgroup.centralizer {g}) := by
  have hcard : ∀ c : F4, Fintype.card (Blk d c) ≤ 3 := fun c => by
    rw [Fintype.card_subtype]
    exact hcnt c
  let K := (detHom hg).ker
  have hU : ∀ c : F4, Group.IsSolvable ↥(Ucat d c) := fun c => isSolvable_Ucat d c (hcard c)
  haveI : Group.IsSolvable (∀ c : F4, ↥(Ucat d c)) :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.isSolvable_pi_of_finite
  let F : ↥K →* ∀ c : F4, ↥(Ucat d c) := MonoidHom.pi fun c =>
    ((blkHom hg c).comp K.subtype).codRestrict (Ucat d c) (fun y => by
      have hy : detHom hg y.1 = 1 := MonoidHom.mem_ker.1 y.2
      have h1 := congrFun hy c
      simp only [detHom, MonoidHom.pi_apply, Pi.one_apply] at h1
      exact blkHom_mem_Ucat hg c y.1 h1)
  have hF : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h2 : ∀ c, blkHom hg c y.1 = 1 := by
      intro c
      have h3 := congrArg Subtype.val (congrFun hy c)
      exact h3
    apply Subtype.ext
    apply blkPi_injective hg
    funext c
    simp only [MonoidHom.pi_apply, map_one, Pi.one_apply]
    rw [h2 c, Subgroup.coe_one, map_one]
  haveI : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective hF
  exact Group.isSolvable_of_ker_le_range K.subtype (detHom hg) (by rw [Subgroup.range_subtype])

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU
