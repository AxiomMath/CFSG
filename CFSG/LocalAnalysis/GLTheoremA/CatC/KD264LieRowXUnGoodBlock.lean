module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnModel
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped Matrix

theorem card_xunK_sq : Nat.card xunK = (2 ^ 1) ^ 2 := by
  rw [xunK_card]
  norm_num

theorem pow_three_eq_one_of_ne_zero {x : xunK} (hx : x ≠ 0) : x ^ 3 = 1 := by
  classical
  haveI : Fintype xunK := Fintype.ofFinite xunK
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  have hc : Fintype.card xunK = 4 := by
    rw [← Nat.card_eq_fintype_card, xunK_card]
    norm_num
  rw [hc] at h
  norm_num at h
  exact h

section Block

variable {N : ℕ}

@[expose] noncomputable def blk (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 1 ≤ C.card) :
    StatedSU C.card (2 ^ 1) xunK →* StatedSU N (2 ^ 1) xunK :=
  embedSU (C.orderEmbOfFin rfl).injective card_xunK_sq hC hN

theorem blk_injective (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 1 ≤ C.card) :
    Function.Injective (blk hN C hC) :=
  embedSU_injective _ card_xunK_sq hC hN

theorem mem_range_blk (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 1 ≤ C.card)
    (x : StatedSU N (2 ^ 1) xunK) :
    x ∈ (blk hN C hC).range ↔
      IsIdOutside (C : Set (Fin N)) ((x : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) := by
  unfold blk
  rw [mem_range_embedSU_iff _ card_xunK_sq hC hN x, Finset.range_orderEmbOfFin]

@[expose] noncomputable def blkProj (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 1 ≤ C.card) :
    StatedSU C.card (2 ^ 1) xunK →* xunM N :=
  (projH (StatedSU N (2 ^ 1) xunK)).comp (blk hN C hC)

@[expose] noncomputable abbrev blkRange (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 1 ≤ C.card) : Subgroup (xunM N) :=
  (blkProj hN C hC).range

theorem blkProj_injective (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 1 ≤ C.card)
    (j : Fin N) (hj : j ∉ C) : Function.Injective (blkProj hN C hC) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : blk hN C hC x ∈ (StatedScalars (Fin N) xunK).subgroupOf (StatedSU N (2 ^ 1) xunK) := by
    have hx' := hx
    simp only [blkProj, MonoidHom.comp_apply, projH, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx'
    exact hx'
  rw [Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h1
  have hout := (mem_range_blk hN C hC (blk hN C hC x)).1 ⟨x, rfl⟩
  have hjj := hout j j (Or.inl (by simpa using hj))
  have e := congrArg (fun g : GL (Fin N) xunK => (g : Matrix (Fin N) (Fin N) xunK) j j) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Subgroup.coe_mul] at e
  have hc1 : (c : xunK) = 1 := by
    rw [e, hjj]
    simp
  have hc2 : c = 1 := Units.ext (by rw [hc1, Units.val_one])
  have hone : (blk hN C hC x : GL (Fin N) xunK) = 1 := by
    rw [← hc, hc2, map_one]
  have : blk hN C hC x = 1 := Subtype.ext hone
  exact (blk_injective hN C hC) (by rw [this, map_one])

theorem isQuasisimple_blkRange (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 4 ≤ C.card)
    (j : Fin N) (hj : j ∉ C) :
    CFSG.Open.IsQuasisimple ↥(blkRange hN C (by omega)) := by
  have hinj := blkProj_injective hN C (by omega) j hj
  have hq : CFSG.IsQuasisimple (StatedSU C.card (2 ^ 1) xunK) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card card_xunK_sq (by omega)
      (by
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp at h2
        omega)).1
  exact ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).mp
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj) hq)

@[expose] noncomputable def diagGL {m : ℕ} (a : Fin m → xunK) (ha : ∀ i, a i ≠ 0) : GL (Fin m) xunK :=
  Units.mk (Matrix.diagonal a) (Matrix.diagonal (fun i => (a i)⁻¹))
    (by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      simp [mul_inv_cancel₀ (ha i)])
    (by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      simp [inv_mul_cancel₀ (ha i)])

theorem diagGL_mem {m : ℕ} (hm : 1 ≤ m) (a : Fin m → xunK) (ha : ∀ i, a i ≠ 0)
    (h3 : ∀ i, a i ^ 3 = 1) (hprod : ∏ i, a i = 1) :
    diagGL a ha ∈ StatedSU m (2 ^ 1) xunK := by
  rw [mem_statedSU_iff' 1 card_xunK_sq hm (diagGL a ha)]
  refine ⟨?_, ?_⟩
  · change (Matrix.diagonal a).det = 1
    rw [Matrix.det_diagonal, hprod]
  · change ((Matrix.diagonal a).map (iterateFrobenius xunK 2 1))ᵀ * Matrix.diagonal a = 1
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [iterateFrobenius_def, pow_one, Pi.one_apply]
    rw [← pow_succ]
    exact h3 i

@[expose] noncomputable def sa (ω : xunK) (m : ℕ) (i : Fin m) : xunK :=
  if (i : ℕ) = 0 then ω else if (i : ℕ) = 1 then ω ^ 2 else 1

theorem sa_ne_zero {ω : xunK} (hω : ω ≠ 0) (m : ℕ) (i : Fin m) : sa ω m i ≠ 0 := by
  unfold sa
  split_ifs
  · exact hω
  · exact pow_ne_zero _ hω
  · exact one_ne_zero

theorem sa_pow_three {ω : xunK} (hω : ω ≠ 0) (m : ℕ) (i : Fin m) : sa ω m i ^ 3 = 1 := by
  unfold sa
  split_ifs
  · exact pow_three_eq_one_of_ne_zero hω
  · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, pow_three_eq_one_of_ne_zero hω, one_pow]
  · exact one_pow _

theorem sa_prod {ω : xunK} (hω : ω ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    ∏ i : Fin m, sa ω m i = 1 := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  rw [← Finset.prod_subset (Finset.subset_univ {i0, i1})]
  · rw [Finset.prod_pair hne]
    have e0 : sa ω m i0 = ω := by simp [sa, i0]
    have e1 : sa ω m i1 = ω ^ 2 := by simp [sa, i1]
    rw [e0, e1, ← pow_succ']
    exact pow_three_eq_one_of_ne_zero hω
  · intro x _ hx
    have hx0 : (x : ℕ) ≠ 0 := by
      intro h
      apply hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      exact Fin.ext (by simp [i0, h])
    have hx1 : (x : ℕ) ≠ 1 := by
      intro h
      apply hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      exact Fin.ext (by simp [i1, h])
    simp [sa, hx0, hx1]

theorem one_le_of_four_le {m : ℕ} (hm : 4 ≤ m) : 1 ≤ m := by omega

theorem nq_of_four_le {m : ℕ} (hm : 4 ≤ m) : (m, 2 ^ 1) ≠ (3, 2) := by
  intro h
  have := congrArg Prod.fst h
  simp at this
  omega

theorem three_dvd_card_quotient_blkRange (hN : 1 ≤ N) (C : Finset (Fin N)) (hC : 4 ≤ C.card)
    (j : Fin N) (hj : j ∉ C) (ω : xunK) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    3 ∣ Nat.card (↥(blkRange hN C (one_le_of_four_le hC)) ⧸ Subgroup.center ↥(blkRange hN C (one_le_of_four_le hC))) := by
  classical
  have hm2 : 2 ≤ C.card := by omega
  have hm3 : 3 ≤ C.card := by omega
  have hmne : (C.card, 2 ^ 1) ≠ (3, 2) := nq_of_four_le hC
  let y : StatedSU C.card (2 ^ 1) xunK :=
    ⟨diagGL (sa ω C.card) (sa_ne_zero hω0 C.card),
      diagGL_mem (one_le_of_four_le hC) _ _ (sa_pow_three hω0 C.card) (sa_prod hω0 C.card hm2)⟩
  have hyc : (y : GL (Fin C.card) xunK) = diagGL (sa ω C.card) (sa_ne_zero hω0 C.card) := rfl
  let X : ↥(blkRange hN C (one_le_of_four_le hC)) := ⟨blkProj hN C (one_le_of_four_le hC) y, ⟨y, rfl⟩⟩
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (Matrix.diagonal (sa ω C.card)) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact sa_pow_three hω0 C.card i
  have hX3 : X ^ 3 = 1 := by
    apply Subtype.ext
    change blkProj hN C (one_le_of_four_le hC) y ^ 3 = 1
    rw [← map_pow, hy3, map_one]
  have hXne : (QuotientGroup.mk X : ↥(blkRange hN C (one_le_of_four_le hC)) ⧸
      Subgroup.center ↥(blkRange hN C (one_le_of_four_le hC))) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    intro hXc
    rw [Subgroup.mem_center_iff] at hXc
    have hy : y ∈ Subgroup.center (StatedSU C.card (2 ^ 1) xunK) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw := hXc ⟨blkProj hN C (one_le_of_four_le hC) w, ⟨w, rfl⟩⟩
      have h2 : blkProj hN C (one_le_of_four_le hC) (w * y) = blkProj hN C (one_le_of_four_le hC) (y * w) := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val hw
      exact blkProj_injective hN C (one_le_of_four_le hC) j hj h2
    have hcen := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card card_xunK_sq
      hm3 hmne).2
    rw [hcen, Subgroup.mem_subgroupOf] at hy
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hy
    let i0 : Fin C.card := ⟨0, by omega⟩
    let i2 : Fin C.card := ⟨2, by omega⟩
    have e0 : (c : xunK) = ω := by
      have := congrArg (fun g : GL (Fin C.card) xunK =>
        (g : Matrix (Fin C.card) (Fin C.card) xunK) i0 i0) hc
      simpa [hyc, diagGL, sa, i0, Matrix.GeneralLinearGroup.coe_scalar] using this
    have e2 : (c : xunK) = 1 := by
      have := congrArg (fun g : GL (Fin C.card) xunK =>
        (g : Matrix (Fin C.card) (Fin C.card) xunK) i2 i2) hc
      simpa [hyc, diagGL, sa, i2, Matrix.GeneralLinearGroup.coe_scalar] using this
    exact hω1 (e0.symm.trans e2)
  have hord : orderOf (QuotientGroup.mk X : ↥(blkRange hN C (one_le_of_four_le hC)) ⧸
      Subgroup.center ↥(blkRange hN C (one_le_of_four_le hC))) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hX3]
      rfl
    · exact hXne
  rw [← hord]
  exact orderOf_dvd_natCard _

end Block

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

end
