module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import all CFSG.Fischer.F4
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Big
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag
open Matrix

private theorem det_eq_zero_of_off_single (M : Matrix (Fin 6) (Fin 6) F4) (i : Fin 6)
    (h : ∀ j k, j ≠ i → k ≠ i → M j k = 0) : M.det = 0 := by
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [show (∏ j, M (σ j) j) = 0 from ?_]
  · simp
  ·
    have hlt : ({i, σ.symm i} : Finset (Fin 6)).card < Fintype.card (Fin 6) := by
      rw [Fintype.card_fin]
      have := Finset.card_le_two (a := i) (b := σ.symm i)
      omega
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    push Not at hk
    exact Finset.prod_eq_zero (Finset.mem_univ k)
      (h (σ k) k (fun hc => hk.2 (σ.injective (by rw [Equiv.apply_symm_apply]; exact hc))) hk.1)


private theorem scalar_mul_eq_smul (c : F4ˣ) (M : Matrix (Fin 6) (Fin 6) F4) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) * M) = (c : F4) • M := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext a b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne' _ hk, zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private theorem fixSubgroup_Psi0_diag_eq
    {D : GL (Fin 6) F4} {Dg : Gu} (hval : (Dg : GL (Fin 6) F4) = D)
    {a b : F4} {i : Fin 6} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => a) i b)) :
    fixSubgroup (Psi0 Dg) = (CenD D).map pi6 := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
      (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) x
    have hfix : Psi0 Dg (pi6 u) = pi6 u := hx
    have hconj : Psi0 Dg (pi6 u) = pi6 (conjM6 Dg u) :=
      Psi0_mk Dg u (conjM6 Dg u) (conjM6_apply Dg u)
    have hquot : pi6 (conjM6 Dg u * u⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hconj, hfix, mul_inv_cancel]
    have hzZ : conjM6 Dg u * u⁻¹ ∈
        (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) :=
      (QuotientGroup.eq_one_iff _).mp hquot
    obtain ⟨c, hc⟩ := mem_Z6.mp hzZ
    have hconj_eqGL : (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) *
        (Dg : GL (Fin 6) F4)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 6) c * (↑u : GL (Fin 6) F4) := by
      have h := congrArg (fun z : GL (Fin 6) F4 => z * (↑u : GL (Fin 6) F4)) hc
      rw [show (↑(conjM6 Dg u * u⁻¹) : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) =
          (↑(conjM6 Dg u) : GL (Fin 6) F4) from by
            rw [Subgroup.coe_mul, Subgroup.coe_inv]
            group] at h
      rw [conjM6_apply] at h
      exact h.symm
    by_cases hc1 : c = 1
    · have hcommGL : (↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4) =
          (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) := by
        have h2 : (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) *
            (Dg : GL (Fin 6) F4)⁻¹ = (↑u : GL (Fin 6) F4) := by
          rw [hconj_eqGL, hc1, map_one, one_mul]
        calc (↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4)
            = ((Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) *
                (Dg : GL (Fin 6) F4)⁻¹) * (Dg : GL (Fin 6) F4) := by rw [h2]
          _ = (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) := by group
      rw [Subgroup.mem_map]
      refine ⟨u, ?_, rfl⟩
      rw [mem_CenD]
      simpa [hval] using hcommGL
    · exfalso
      have hcne : (c : F4) ≠ 1 := fun h => hc1 (Units.ext h)
      have hdmul : (D : Matrix (Fin 6) (Fin 6) F4) * mM6 u =
          (c : F4) • (mM6 u * (D : Matrix (Fin 6) (Fin 6) F4)) := by
        have hGL : (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) =
            Matrix.GeneralLinearGroup.scalar (Fin 6) c *
              ((↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4)) := by
          calc (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4)
              = ((Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) *
                  (Dg : GL (Fin 6) F4)⁻¹) * (Dg : GL (Fin 6) F4) := by group
            _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) c * (↑u : GL (Fin 6) F4)) *
                  (Dg : GL (Fin 6) F4) := by rw [hconj_eqGL]
            _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c *
                  ((↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4)) := by group
        have h := congrArg (fun z : GL (Fin 6) F4 =>
          ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) hGL
        have hmat : (D : Matrix (Fin 6) (Fin 6) F4) * mM6 u =
            (Matrix.diagonal fun _ => (c : F4)) *
              (mM6 u * (D : Matrix (Fin 6) (Fin 6) F4)) := by
          simpa [mM6, hval, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] using h
        rw [hmat]
        ext jj kk
        rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
      have hzero : ∀ j k, j ≠ i → k ≠ i → mM6 u j k = 0 := by
        intro j k hji hki
        have hdj : Function.update (fun _ => a) i b j = a := by
          simp [Function.update, hji]
        have hdk : Function.update (fun _ => a) i b k = a := by
          simp [Function.update, hki]
        have h := congrFun (congrFun hdmul j) k
        rw [hD] at h
        rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal] at h
        rw [hdj, hdk] at h
        have h3 : a * mM6 u j k = (c : F4) * a * mM6 u j k := by
          calc a * mM6 u j k = (c : F4) * (mM6 u j k * a) := h
            _ = (c : F4) * a * mM6 u j k := by ring
        have h4 : mM6 u j k = (c : F4) * mM6 u j k := by
          refine mul_left_cancel₀ ha ?_
          rw [h3]
          ring
        have h5 : (1 - (c : F4)) * mM6 u j k = 0 := by
          rw [sub_mul, one_mul, ← h4]
          ring
        exact (mul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr (Ne.symm hcne))
      have hdet0 : (mM6 u).det = 0 := det_eq_zero_of_off_single (mM6 u) i hzero
      have hdet1 : (mM6 u).det = 1 := det_one_of_mem_statedSU (by norm_num) _ u.2
      rw [hdet0] at hdet1
      exact zero_ne_one hdet1
  · rintro ⟨u, hu, rfl⟩
    rw [mem_fixSubgroup]
    have hcomm : (↑u : GL (Fin 6) F4) * D = D * (↑u : GL (Fin 6) F4) := mem_CenD.mp hu
    have hcu : (↑(conjM6 Dg u) : GL (Fin 6) F4) = (↑u : GL (Fin 6) F4) := by
      rw [conjM6_apply]
      have hcommGL : (↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4) =
          (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) := by
        simpa [hval] using hcomm
      calc (Dg : GL (Fin 6) F4) * (↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4)⁻¹
          = ((↑u : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4)) *
              (Dg : GL (Fin 6) F4)⁻¹ := by rw [hcommGL]
        _ = (↑u : GL (Fin 6) F4) := by group
    have hcuM : conjM6 Dg u = u := Subtype.ext hcu
    have h := Psi0_mk Dg u (conjM6 Dg u) (conjM6_apply Dg u)
    change (Psi0 Dg) (QuotientGroup.mk u) = QuotientGroup.mk u
    rw [h, hcuM]


private theorem cenD_diag_decomp
    {D : GL (Fin 6) F4} {a b : F4} {i : Fin 6} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => a) i b))
    (u : ↥(CenD D)) :
    ∃ z ∈ (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6),
      ∃ A : ↥(StatedSU (Fintype.card (Blk (Function.update (fun _ => a) i b) a)) (2 ^ 1) F4),
        (u : M6) = z * embSU (Function.update (fun _ => a) i b) a A := by
  let d : Fin 6 → F4 := Function.update (fun _ => a) i b
  have hDd : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hD
  have hdi : d i = b := by simp [d, Function.update]
  have hdne : ∀ j : Fin 6, j ≠ i → d j = a := by
    intro j hj
    simp [d, Function.update, hj]
  have hi_single : ∀ j : Fin 6, d j = d i → j = i := by
    intro j hj
    by_contra hji
    have hj' : d j = a := hdne j hji
    rw [hj', hdi] at hj
    exact hab hj
  set M : Matrix (Fin 6) (Fin 6) F4 := mM6 u with hMdef
  have hMoff : ∀ j k : Fin 6, d j ≠ d k → M j k = 0 := fun j k hjk =>
    CenD_zero hDd u hjk
  have hm3 : (M i i) ^ 3 = 1 := by
    have h := congrFun (congrFun (M6_unitary u) i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply,
      if_pos rfl] at h
    have hsum : ∑ k, bar (M k i) * M k i = bar (M i i) * M i i := by
      apply Finset.sum_eq_single i
      · intro k _ hk
        have hd : d k ≠ d i := fun h' => hk (hi_single k h')
        rw [hMoff k i hd]
        simp
      · intro h'
        exact absurd (Finset.mem_univ i) h'
    rw [hsum, bar_apply] at h
    calc (M i i) ^ 3 = (M i i) ^ 2 * M i i := by ring
      _ = 1 := h
  have hm0 : M i i ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hm3
    exact zero_ne_one hm3
  let mU : F4ˣ := Units.mk0 (M i i) hm0
  have hmU : (mU : F4) = M i i := rfl
  have hmU3 : (mU : F4) ^ 3 = 1 := by rw [hmU]; exact hm3
  have hzmem : Matrix.GeneralLinearGroup.scalar (Fin 6) mU ∈ StatedSU 6 (2 ^ 1) F4 := by
    apply scalar_mem_unitarySU (h := hF4) (n := 6) (by norm_num)
    · show (mU : F4) * bar (mU : F4) = 1
      rw [bar_apply]
      calc (mU : F4) * (mU : F4) ^ 2 = (mU : F4) ^ 3 := by ring
        _ = 1 := hmU3
    · rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_cube mU, one_pow]
  let z : M6 := ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) mU, hzmem⟩
  have hzZ : z ∈ (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) := by
    rw [mem_Z6]
    exact ⟨mU, rfl⟩
  have hzCen : z ∈ CenD D := by
    rw [mem_CenD]
    exact ((commute_scalar mU D).eq).symm
  let r : M6 := z⁻¹ * u
  have hrC : r ∈ CenD D := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzCen) u.2
  have hzmat : mM6 z = Matrix.diagonal (fun _ : Fin 6 => (mU : F4)) := by
    change (((z : GL (Fin 6) F4)) : Matrix (Fin 6) (Fin 6) F4) = _
    rw [show (z : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) mU from rfl,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hzimat : mM6 z⁻¹ = Matrix.diagonal (fun _ : Fin 6 => ((mU : F4)))⁻¹ := by
    rw [mM6_inv, hzmat]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (Units.ne_zero mU)
  have hentry : ∀ j k : Fin 6, mM6 r j k = ((mU : F4))⁻¹ * M j k := by
    intro j k
    change mM6 (z⁻¹ * u) j k = _
    rw [mM6_mul, hzimat, Matrix.diagonal_mul]
    rfl
  have hblk : mM6 r = extMat d a (blkM d a (mM6 r)) := by
    symm
    apply extMat_blkM
    intro j k hjk
    rw [hentry]
    by_cases hEq : j = k
    · have hji : j = i := by
        by_contra hne
        exact hjk ⟨hdne j hne, by rw [← hEq]; exact hdne j hne⟩
      have hki : k = i := by rw [← hEq, hji]
      rw [hji, hki, Matrix.one_apply_eq]
      change ((mU : F4))⁻¹ * M i i = 1
      rw [← hmU]
      exact inv_mul_cancel₀ (Units.ne_zero mU)
    · rw [Matrix.one_apply_ne hEq]
      have hdjk : d j ≠ d k := by
        intro heq
        by_cases hji : j = i
        · have hki : k = i := by
            apply hi_single k
            rw [hji] at heq
            exact heq.symm
          exact hEq (hji.trans hki.symm)
        · have hdj : d j = a := hdne j hji
          by_cases hki : k = i
          · rw [hki, hdi, hdj] at heq
            exact hab heq
          · have hdk : d k = a := hdne k hki
            exact hjk ⟨hdj, hdk⟩
      rw [hMoff j k hdjk, mul_zero]
  let eW := Fintype.equivFin (Blk d a)
  let Ab : GL (Blk d a) F4 := blkHom hDd a ⟨r, hrC⟩
  have hAbval : ((Ab : GL (Blk d a) F4) : Matrix (Blk d a) (Blk d a) F4) =
      blkM d a (mM6 r) := blkHom_val hDd a ⟨r, hrC⟩
  have hA_mem : reindexGL eW Ab ∈ StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4 := by
    apply mem_statedSU_of
    · rw [reindexGL_val, Matrix.det_reindex_self, hAbval]
      have hdetr : (mM6 r).det = 1 := det_one_of_mem_statedSU (by norm_num) _ r.2
      rw [hblk, det_extMat] at hdetr
      exact hdetr
    · rw [reindexGL_val, hAbval]
      have hU : ((blkM d a (mM6 r)).map bar).transpose * blkM d a (mM6 r) = 1 :=
        blkM_unitary d a (fun j k hjk => by rw [hentry, hMoff j k hjk, mul_zero])
          (M6_unitary r)
      exact reindex_unitary eW (blkM d a (mM6 r)) hU
  have hrEq : r = embSU d a ⟨reindexGL eW Ab, hA_mem⟩ := by
    apply Subtype.ext
    apply Units.ext
    change mM6 r = extMat d a ((Matrix.reindex eW.symm eW.symm)
      (((reindexGL eW Ab : GL (Fin (Fintype.card (Blk d a))) F4) :
        Matrix (Fin (Fintype.card (Blk d a))) (Fin (Fintype.card (Blk d a))) F4)))
    rw [reindexGL_val]
    have hround : (Matrix.reindex eW.symm eW.symm) ((Matrix.reindex eW eW)
        ((Ab : GL (Blk d a) F4) : Matrix (Blk d a) (Blk d a) F4)) =
        ((Ab : GL (Blk d a) F4) : Matrix (Blk d a) (Blk d a) F4) := by
      rw [← Matrix.reindex_symm]
      exact (Matrix.reindex eW eW).symm_apply_apply _
    rw [hround, hAbval]
    exact hblk
  refine ⟨z, hzZ, ⟨reindexGL eW Ab, hA_mem⟩, ?_⟩
  change (u : M6) = z * embSU d a ⟨reindexGL eW Ab, hA_mem⟩
  rw [← hrEq]
  change (u : M6) = z * (z⁻¹ * u)
  group


private theorem range_embSU_inf_Z6 {a b : F4} {i : Fin 6} (hab : a ≠ b) :
    (embSU (Function.update (fun _ => a) i b) a).range ⊓
      (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) = ⊥ := by
  let d : Fin 6 → F4 := Function.update (fun _ => a) i b
  have hdi : d i = b := by simp [d, Function.update]
  rw [eq_bot_iff]
  rintro z ⟨hzR, hzZ⟩
  rw [Subgroup.mem_bot]
  obtain ⟨A, hA⟩ := hzR
  obtain ⟨lam, hlam⟩ := mem_Z6.mp hzZ
  have h1 : mM6 z i i = 1 := by
    rw [← hA, mM6_embSU, extMat_apply]
    rw [dif_neg (show ¬ (d i = a ∧ d i = a) from fun h => (Ne.symm hab) (by
      rw [← hdi]; exact h.1))]
    exact Matrix.one_apply_eq i
  have hzmat : mM6 z = ((Matrix.GeneralLinearGroup.scalar (Fin 6) lam : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) := by
    change (((z : GL (Fin 6) F4)) : Matrix (Fin 6) (Fin 6) F4) = _
    rw [← hlam]
  have h2 : mM6 z i i = (lam : F4) := by
    rw [hzmat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq]
  have hlam1 : (lam : F4) = 1 := by rw [← h2, h1]
  apply Subtype.ext
  rw [← hlam, show lam = 1 from Units.ext hlam1, map_one]
  rfl

private noncomputable def diagFixEquiv
    {D : GL (Fin 6) F4} {Dg : Gu} (hval : (Dg : GL (Fin 6) F4) = D)
    {a b : F4} {i : Fin 6} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => a) i b)) :
    ↥(StatedSU (Fintype.card (Blk (Function.update (fun _ => a) i b) a)) (2 ^ 1) F4) ≃*
      ↥(fixSubgroup (Psi0 Dg)) := by
  let d : Fin 6 → F4 := Function.update (fun _ => a) i b
  have hfix : fixSubgroup (Psi0 Dg) = (CenD D).map pi6 :=
    fixSubgroup_Psi0_diag_eq hval ha hb hab hD
  let φ : ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4) →*
      ↥(fixSubgroup (Psi0 Dg)) :=
    MonoidHom.codRestrict (pi6.comp (embSU d a)) (fixSubgroup (Psi0 Dg)) (fun A => by
      rw [hfix]
      exact Subgroup.mem_map.mpr ⟨embSU d a A, embSU_mem_CenD d a hD A, rfl⟩)
  have hinj : Function.Injective φ := by
    intro A B hAB
    have h1 : pi6 (embSU d a A) = pi6 (embSU d a B) := congrArg Subtype.val hAB
    have h2 : pi6 ((embSU d a A) * (embSU d a B)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 : (embSU d a A) * (embSU d a B)⁻¹ ∈
        (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) :=
      (QuotientGroup.eq_one_iff _).mp h2
    have h4 : (embSU d a A) * (embSU d a B)⁻¹ ∈ (embSU d a).range :=
      Subgroup.mul_mem _ (MonoidHom.mem_range.mpr ⟨A, rfl⟩)
        (Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨B, rfl⟩))
    have h5 : (embSU d a A) * (embSU d a B)⁻¹ = 1 := by
      have hin : (embSU d a A) * (embSU d a B)⁻¹ ∈
          (embSU d a).range ⊓ (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) :=
        Subgroup.mem_inf.mpr ⟨h4, h3⟩
      rwa [range_embSU_inf_Z6 (a := a) (b := b) (i := i) hab, Subgroup.mem_bot] at hin
    have h6 : embSU d a A = embSU d a B := by
      calc embSU d a A = ((embSU d a A) * (embSU d a B)⁻¹) * embSU d a B := by group
        _ = embSU d a B := by rw [h5, one_mul]
    exact embSU_injective d a h6
  have hsurj : Function.Surjective φ := by
    intro x
    have hx : (x : S6) ∈ (CenD D).map pi6 := by
      rw [← hfix]
      exact x.2
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hzZ, A, hA⟩ := cenD_diag_decomp ha hb hab hD ⟨u, hu⟩
    refine ⟨A, ?_⟩
    apply Subtype.ext
    change pi6 (embSU d a A) = (x : S6)
    have hz1 : pi6 z = 1 := (QuotientGroup.eq_one_iff z).mpr hzZ
    calc pi6 (embSU d a A) = 1 * pi6 (embSU d a A) := (one_mul _).symm
      _ = pi6 z * pi6 (embSU d a A) := by rw [hz1]
      _ = pi6 (z * embSU d a A) := (map_mul _ _ _).symm
      _ = pi6 u := by rw [← hA]
      _ = (x : S6) := hux
  exact MulEquiv.ofBijective φ ⟨hinj, hsurj⟩


private noncomputable def omegaU : F4ˣ := Units.mk0 F4.ω (by decide)

private theorem omegaU_val : (omegaU : F4) = F4.ω := rfl

private theorem omegaU_cube : (omegaU : F4) ^ 3 = 1 := by decide

private theorem omegaU_ne_one : (omegaU : F4) ≠ 1 := by decide

private theorem omegaU_sq_ne_one : (omegaU : F4) ^ 2 ≠ 1 := by decide

private theorem omegaU_norm : hF4.norm (omegaU : F4) = 1 := by
  show (omegaU : F4) * bar (omegaU : F4) = 1
  rw [bar_apply]
  calc (omegaU : F4) * (omegaU : F4) ^ 2 = (omegaU : F4) ^ 3 := by ring
    _ = 1 := omegaU_cube

private theorem omegaU_sq_norm : hF4.norm ((omegaU : F4) ^ 2) = 1 := by
  show (omegaU : F4) ^ 2 * bar ((omegaU : F4) ^ 2) = 1
  rw [map_pow, bar_apply]
  calc (omegaU : F4) ^ 2 * ((omegaU : F4) ^ 2) ^ 2 = ((omegaU : F4) ^ 3) ^ 2 := by ring
    _ = 1 := by rw [omegaU_cube, one_pow]

private theorem mem_statedSU_five_gram {A : GL (Fin 5) F4} :
    A ∈ StatedSU 5 (2 ^ 1) F4 ↔
      A ∈ gramSU hF4 ((1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) := by
  rw [show StatedSU 5 (2 ^ 1) F4 = unitarySU 2 1 F4 5 from rfl,
    CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU hF4 5]
  simp

private theorem eq_scalar_of_commute_statedSU5 (C : Matrix (Fin 5) (Fin 5) F4)
    (hcomm : ∀ A : ↥(StatedSU 5 (2 ^ 1) F4),
      C * ((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
        ((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) * C) :
    ∃ ν : F4, C = Matrix.scalar (Fin 5) ν := by
  let ω : F4 := F4.ω
  have hω3 : ω ^ 3 = 1 := by decide
  have hω1 : ω ≠ 1 := by decide
  have hω0 : ω ≠ 0 := by decide
  let ωU : F4ˣ := omegaU
  have hωU : (ωU : F4) = ω := rfl
  have hωU3 : (ωU : F4) ^ 3 = 1 := by rw [hωU]; exact hω3
  have hωU_inv_ne : (ωU⁻¹ : F4) ≠ (ωU : F4) := by
    intro h
    have h2 : (ωU : F4) ^ 2 = 1 := by
      calc (ωU : F4) ^ 2 = (ωU : F4) * (ωU : F4) := by ring
        _ = (ωU⁻¹ : F4) * (ωU : F4) := by rw [h]
        _ = 1 := inv_mul_cancel₀ (Units.ne_zero ωU)
    rw [hωU] at h2
    have h3 : ω = 1 := by
      calc ω = ω * 1 := (mul_one ω).symm
        _ = ω * ω ^ 2 := by rw [← h2]
        _ = ω ^ 3 := by ring
        _ = 1 := hω3
    exact hω1 h3
  have hωU_norm : hF4.norm (ωU : F4) = 1 := by
    show (ωU : F4) * bar (ωU : F4) = 1
    rw [bar_apply]
    calc (ωU : F4) * (ωU : F4) ^ 2 = (ωU : F4) ^ 3 := by ring
      _ = 1 := hωU3
  have hdiag_mem : ∀ a b : Fin 5,
      unitaryDiagGL (Pi.mulSingle a ωU * Pi.mulSingle b ωU⁻¹) ∈ StatedSU 5 (2 ^ 1) F4 := by
    intro a b
    rw [mem_statedSU_five_gram]
    exact CFSG.RankThree.Classical.unitaryDiagGL_mem_gramSU hF4
      (CFSG.RankThree.Classical.pairDiag_norm_prod hF4 hωU_norm a b).1
      (CFSG.RankThree.Classical.pairDiag_norm_prod hF4 hωU_norm a b).2
  have hdiagC : ∀ i j : Fin 5, i ≠ j → C i j = 0 := by
    intro i j hij
    obtain ⟨b, hbi, hbj⟩ : ∃ b : Fin 5, b ≠ i ∧ b ≠ j := by
      have hlt : ({i, j} : Finset (Fin 5)).card < Fintype.card (Fin 5) := by
        rw [Fintype.card_fin]
        have := Finset.card_le_two (a := i) (b := j)
        omega
      obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      rw [Finset.mem_insert, Finset.mem_singleton] at hb
      push Not at hb
      exact ⟨b, hb.1, hb.2⟩
    let dd : Fin 5 → F4ˣ := Pi.mulSingle j ωU * Pi.mulSingle b ωU⁻¹
    have hcommD := congrFun (congrFun
      (hcomm ⟨unitaryDiagGL dd, hdiag_mem j b⟩) i) j
    have hmatD : ((unitaryDiagGL dd : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
        Matrix.diagonal (fun x => (dd x : F4)) := CFSG.RankThree.Classical.coe_unitaryDiagGL dd
    rw [hmatD, Matrix.mul_diagonal, Matrix.diagonal_mul] at hcommD
    have hda : (dd j : F4) = (ωU : F4) := by
      simp [dd, Pi.mulSingle_eq_of_ne hbj.symm]
    have hdi : (dd i : F4) ≠ (ωU : F4) := by
      by_cases hib : i = b
      · have hddi : (dd i : F4) = (ωU⁻¹ : F4) := by
          simp [dd, hib, Pi.mulSingle_eq_of_ne hbj]
        rw [hddi]
        simpa using hωU_inv_ne
      · have hddi : (dd i : F4) = 1 := by
          simp [dd, Pi.mulSingle_eq_of_ne hij, Pi.mulSingle_eq_of_ne hib]
        rw [hddi, hωU]
        exact Ne.symm hω1
    rw [hda] at hcommD
    have h1 : ((dd i : F4) - ω) * C i j = 0 := by
      rw [sub_mul]
      rw [show (dd i : F4) * C i j = C i j * ω from hcommD.symm]
      rw [mul_comm (C i j) ω, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (by rw [← hωU]; exact hdi))
  have hdiag_all : ∀ a b : Fin 5, C a a = C b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 5, c ≠ a ∧ c ≠ b := by
        have hlt : ({a, b} : Finset (Fin 5)).card < Fintype.card (Fin 5) := by
          rw [Fintype.card_fin]
          have := Finset.card_le_two (a := a) (b := b)
          omega
        obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        push Not at hc
        exact ⟨c, hc.1, hc.2⟩
      let σ : Equiv.Perm (Fin 5) := Equiv.swap a b * Equiv.swap b c
      have hσ : Equiv.Perm.sign σ = 1 := by
        simp [σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
          Equiv.Perm.sign_swap hcb.symm]
      have hσa : σ a = b := by
        simp [σ, Equiv.swap_apply_of_ne_of_ne hab hca.symm]
      have hperm_mem : unitaryPermGL σ ∈ StatedSU 5 (2 ^ 1) F4 := by
        rw [mem_statedSU_five_gram]
        exact CFSG.RankThree.Classical.unitaryPermGL_mem_gramSU hF4 hσ
      have hp := congrFun (congrFun
        (hcomm ⟨unitaryPermGL σ, hperm_mem⟩) a) b
      rw [show ((unitaryPermGL σ : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
          σ.permMatrix F4 from CFSG.RankThree.Classical.coe_unitaryPermGL σ] at hp
      rw [Matrix.mul_apply, Matrix.mul_apply] at hp
      have hL : ∑ j, C a j * σ.permMatrix F4 j b = C a a := by
        rw [Finset.sum_eq_single a]
        · rw [permMatrix_apply', hσa]
          simp
        · intro j _ hj
          rw [hdiagC a j (Ne.symm hj), zero_mul]
        · intro ha
          exact absurd (Finset.mem_univ a) ha
      have hR : ∑ j, σ.permMatrix F4 a j * C j b = C b b := by
        rw [Finset.sum_eq_single b]
        · rw [permMatrix_apply', hσa]
          simp
        · intro j _ hj
          rw [permMatrix_apply', hσa]
          simp [Ne.symm hj]
        · intro hb
          exact absurd (Finset.mem_univ b) hb
      rw [hL, hR] at hp
      exact hp
  refine ⟨C 0 0, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, hdiag_all i 0]
  · rw [if_neg hij, hdiagC i j hij]


private noncomputable def diagOmega (a : Fin 5) : Fin 5 → F4ˣ :=
  fun x => if x = a then omegaU ^ 2 else omegaU

private theorem diagOmega_mem (a : Fin 5) :
    unitaryDiagGL (diagOmega a) ∈ StatedSU 5 (2 ^ 1) F4 := by
  rw [mem_statedSU_five_gram]
  apply CFSG.RankThree.Classical.unitaryDiagGL_mem_gramSU hF4
  · intro i
    show hF4.norm (((if i = a then omegaU ^ 2 else omegaU : F4ˣ) : F4)) = 1
    by_cases hi : i = a
    · rw [if_pos hi]
      exact omegaU_sq_norm
    · rw [if_neg hi]
      exact omegaU_norm
  · fin_cases a <;> decide

private noncomputable def liftSU {d : Fin 6 → F4} {c : F4}
    (e : Blk d c ≃ Fin 5) (A : ↥(StatedSU 5 (2 ^ 1) F4)) :
    ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) :=
  ⟨reindexGL (Fintype.equivFin (Blk d c)) (reindexGL e.symm (A : GL (Fin 5) F4)),
    by
      apply mem_statedSU_of
      · rw [reindexGL_val, reindexGL_val, Matrix.det_reindex_self, Matrix.det_reindex_self]
        exact det_one_of_mem_statedSU (by norm_num) _ A.2
      · rw [reindexGL_val, reindexGL_val]
        apply reindex_unitary
        apply reindex_unitary
        exact unitary_of_mem_statedSU' 5 A.2⟩

private theorem mM6_embSU_liftSU_apply {d : Fin 6 → F4} {c : F4}
    (e : Blk d c ≃ Fin 5) (A : ↥(StatedSU 5 (2 ^ 1) F4)) (j k : Blk d c) :
    mM6 (embSU d c (liftSU e A)) j k =
      ((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) (e j) (e k) := by
  let eW := Fintype.equivFin (Blk d c)
  rw [mM6_embSU, extMat_apply]
  rw [dif_pos ⟨j.2, k.2⟩]
  change (Matrix.reindex eW.symm eW.symm
    (((liftSU e A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) : GL
      (Fin (Fintype.card (Blk d c))) F4) : Matrix
        (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4)) j k =
    ((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) (e j) (e k)
  have hlift : (((liftSU e A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) : GL
      (Fin (Fintype.card (Blk d c))) F4) : Matrix
        (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4) =
      (Matrix.reindex eW eW) ((Matrix.reindex e.symm e.symm)
        ((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)) := rfl
  rw [hlift]
  have hround : (Matrix.reindex eW.symm eW.symm) ((Matrix.reindex eW eW)
      ((Matrix.reindex e.symm e.symm)
        ((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4))) =
      (Matrix.reindex e.symm e.symm) ((A : GL (Fin 5) F4) :
        Matrix (Fin 5) (Fin 5) F4) := by
    rw [← Matrix.reindex_symm]
    exact (Matrix.reindex eW eW).symm_apply_apply _
  rw [hround, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]


private theorem isPerfect_statedSU_five : Group.IsPerfect ↥(StatedSU 5 (2 ^ 1) F4) := by
  have hK : Nat.card F4 = (2 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, F4.card]
    norm_num
  have h := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK)
    (n := 5) (by norm_num) (fun h3 => by omega)
  rwa [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 5] at h

private theorem z6_isMulCommutative :
    IsMulCommutative ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) := by
  refine isMulCommutative_iff.mpr fun z w => Subtype.ext ?_
  exact (Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 z.2) (w : M6)).symm

private theorem z6_solvable : Group.IsSolvable ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) :=
  @Group.instIsSolvableOfIsMulCommutative _ _ z6_isMulCommutative


private theorem commute_embSU_of_fixing
    {D : GL (Fin 6) F4} {Dg : Gu} (hval : (Dg : GL (Fin 6) F4) = D)
    {a b : F4} {i : Fin 6} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => a) i b))
    (h : PGU6) (ĥ : Gu) (hĥ : QuotientGroup.mk ĥ = h)
    (hfix : ∀ x ∈ fixSubgroup (Psi0 Dg), Psi h x = x) :
    ∀ A : ↥(StatedSU (Fintype.card (Blk (Function.update (fun _ => a) i b) a)) (2 ^ 1) F4),
      (ĥ : GL (Fin 6) F4) *
          (((embSU (Function.update (fun _ => a) i b) a A : M6) : GL (Fin 6) F4)) =
        (((embSU (Function.update (fun _ => a) i b) a A : M6) : GL (Fin 6) F4)) *
          (ĥ : GL (Fin 6) F4) := by
  let d : Fin 6 → F4 := Function.update (fun _ => a) i b
  have hdi : d i = b := by simp [d, Function.update]
  have hdne : ∀ j : Fin 6, j ≠ i → d j = a := by
    intro j hj
    simp [d, Function.update, hj]
  have hcardW : Fintype.card (Blk d a) = 5 := by
    rw [Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun j : Fin 6 => d j = a) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · intro hj
        refine ⟨?_, trivial⟩
        rintro rfl
        rw [hdi] at hj
        exact hab hj.symm
      · intro hji
        exact hdne j hji.1
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  let θfun : ↥(CenD D) → (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) := fun u =>
    ⟨conjM6 ĥ u * u⁻¹, by
      have hmemF : pi6 (u : M6) ∈ fixSubgroup (Psi0 Dg) := by
        rw [fixSubgroup_Psi0_diag_eq hval ha hb hab hD]
        exact Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩
      have hfixu : Psi h (pi6 (u : M6)) = pi6 (u : M6) := hfix _ hmemF
      have hpsi : Psi0 ĥ = Psi h := by rw [← hĥ, Psi_mk]
      have hfixu' : Psi0 ĥ (pi6 (u : M6)) = pi6 (u : M6) := by
        rw [hpsi]
        exact hfixu
      have hconj := Psi0_mk ĥ (u : M6) (conjM6 ĥ u) (conjM6_apply ĥ u)
      have hconj_pi : pi6 (conjM6 ĥ (u : M6)) = pi6 (u : M6) :=
        hconj.symm.trans hfixu'
      have hquot : pi6 (conjM6 ĥ u * u⁻¹) = 1 := by
        change pi6 (conjM6 ĥ (u : M6) * (u : M6)⁻¹) = 1
        rw [map_mul]
        change pi6 (conjM6 ĥ (u : M6)) * (pi6 (u : M6))⁻¹ = 1
        rw [hconj_pi, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp hquot⟩
  have hθmul : ∀ u v : ↥(CenD D), θfun (u * v) = θfun u * θfun v := by
    intro u v
    apply Subtype.ext
    have hzu : ∀ g : M6, g * (θfun u : M6) = (θfun u : M6) * g :=
      Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 (θfun u).2)
    have hzv : ∀ g : M6, g * (θfun v : M6) = (θfun v : M6) * g :=
      Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 (θfun v).2)
    rw [Subgroup.coe_mul]
    change conjM6 ĥ ((u : M6) * (v : M6)) * ((u : M6) * (v : M6))⁻¹ =
      (θfun u : M6) * (θfun v : M6)
    rw [map_mul]
    calc conjM6 ĥ (u : M6) * conjM6 ĥ (v : M6) * ((u : M6) * (v : M6))⁻¹
        = conjM6 ĥ (u : M6) * (conjM6 ĥ (v : M6) * (v : M6)⁻¹) * (u : M6)⁻¹ := by
          group
      _ = conjM6 ĥ (u : M6) * (θfun v : M6) * (u : M6)⁻¹ := rfl
      _ = (θfun v : M6) * (conjM6 ĥ (u : M6) * (u : M6)⁻¹) := by
          rw [hzv (conjM6 ĥ (u : M6))]
          group
      _ = (θfun v : M6) * (θfun u : M6) := rfl
      _ = (θfun u : M6) * (θfun v : M6) := by rw [hzu (θfun v : M6)]
  let θ : ↥(CenD D) →* (CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) :=
    MonoidHom.mk' θfun hθmul
  let ιR : ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4) →* ↥(CenD D) :=
    { toFun := fun A => ⟨embSU d a A, embSU_mem_CenD d a hD A⟩
      map_one' := by
        apply Subtype.ext
        change embSU d a 1 = 1
        rw [map_one]
      map_mul' := by
        intro A B
        apply Subtype.ext
        change embSU d a (A * B) = embSU d a A * embSU d a B
        rw [map_mul] }
  haveI hperf : Group.IsPerfect ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4) := by
    rw [hcardW]
    exact isPerfect_statedSU_five
  haveI hsolv : Group.IsSolvable ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6) := z6_solvable
  have hψ1 : ∀ A, (θ.comp ιR) A = 1 := fun A => perfect_hom_trivial (θ.comp ιR) A
  intro A
  have h := hψ1 A
  have hz : conjM6 ĥ (embSU d a A) * (embSU d a A)⁻¹ = 1 := congrArg Subtype.val h
  have hconj_eq : conjM6 ĥ (embSU d a A) = embSU d a A := by
    calc conjM6 ĥ (embSU d a A)
        = (conjM6 ĥ (embSU d a A) * (embSU d a A)⁻¹) * (embSU d a A) := by group
      _ = 1 * (embSU d a A) := by rw [hz]
      _ = embSU d a A := one_mul _
  have hmat : (ĥ : GL (Fin 6) F4) * ((embSU d a A : M6) : GL (Fin 6) F4) *
      (ĥ : GL (Fin 6) F4)⁻¹ = ((embSU d a A : M6) : GL (Fin 6) F4) := by
    rw [← conjM6_apply]
    exact congrArg (fun z : M6 => (z : GL (Fin 6) F4)) hconj_eq
  calc (ĥ : GL (Fin 6) F4) * ((embSU d a A : M6) : GL (Fin 6) F4)
      = ((ĥ : GL (Fin 6) F4) * ((embSU d a A : M6) : GL (Fin 6) F4) *
          (ĥ : GL (Fin 6) F4)⁻¹) * (ĥ : GL (Fin 6) F4) := by group
    _ = ((embSU d a A : M6) : GL (Fin 6) F4) * (ĥ : GL (Fin 6) F4) := by rw [hmat]



private theorem block_scalar_of_commute
    {d : Fin 6 → F4} {a b : F4} {i : Fin 6}
    (hdi : d i = b) (hdne : ∀ j : Fin 6, j ≠ i → d j = a) (hab : a ≠ b)
    (H : GL (Fin 6) F4)
    (hcomm : ∀ A : ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4),
      H * (((embSU d a A : M6) : GL (Fin 6) F4)) =
        (((embSU d a A : M6) : GL (Fin 6) F4)) * H) :
    ∃ ν c : F4, ((H : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => ν) i c) := by
  classical
  let M : Matrix (Fin 6) (Fin 6) F4 := ((H : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hcardW : Fintype.card (Blk d a) = 5 := by
    rw [Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun j : Fin 6 => d j = a) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · intro hj
        refine ⟨?_, trivial⟩
        rintro rfl
        rw [hdi] at hj
        exact hab hj.symm
      · intro hji
        exact hdne j hji.1
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨j0⟩ : Nonempty (Blk d a) := Fintype.card_pos_iff.mp (by rw [hcardW]; norm_num)
  let eW : Blk d a ≃ Fin 5 := Fintype.equivFinOfCardEq hcardW
  let A0 : ↥(StatedSU 5 (2 ^ 1) F4) :=
    ⟨unitaryDiagGL (diagOmega (eW j0)), diagOmega_mem (eW j0)⟩
  have hA0mat : ((A0 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
      Matrix.diagonal (fun x => (diagOmega (eW j0) x : F4)) :=
    CFSG.RankThree.Classical.coe_unitaryDiagGL _
  have hA0diag : ∀ p : Fin 5, ((A0 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) p p =
      (diagOmega (eW j0) p : F4) := by
    intro p
    rw [hA0mat, Matrix.diagonal_apply_eq]
  have hA0off : ∀ p q : Fin 5, p ≠ q →
      ((A0 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) p q = 0 := by
    intro p q hpq
    rw [hA0mat, Matrix.diagonal_apply_ne _ hpq]
  have hd0 : ∀ j : Blk d a, (diagOmega (eW j0) (eW j) : F4) ≠ 1 := by
    intro j
    by_cases h : eW j = eW j0
    · have h1 : diagOmega (eW j0) (eW j) = omegaU ^ 2 := by simp [diagOmega, h]
      rw [h1]
      exact omegaU_sq_ne_one
    · have h1 : diagOmega (eW j0) (eW j) = omegaU := by simp [diagOmega, h]
      rw [h1]
      exact omegaU_ne_one
  let A := liftSU eW A0
  let x := embSU d a A
  have hxentry : ∀ p q : Blk d a, mM6 x p q =
      ((A0 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) (eW p) (eW q) :=
    fun p q => mM6_embSU_liftSU_apply eW A0 p q
  have hxii : mM6 x i i = 1 := by
    rw [mM6_embSU, extMat_apply]
    rw [dif_neg (fun h => hab (h.1.symm.trans hdi))]
    exact Matrix.one_apply_eq i
  have hx_i_off : ∀ q : Fin 6, q ≠ i → mM6 x i q = 0 := by
    intro q hq
    rw [mM6_embSU, extMat_apply]
    rw [dif_neg (fun h => hab (h.1.symm.trans hdi))]
    exact Matrix.one_apply_ne (by rintro rfl; exact hq rfl)
  have hx_off_i : ∀ p : Fin 6, p ≠ i → mM6 x p i = 0 := by
    intro p hp
    rw [mM6_embSU, extMat_apply]
    rw [dif_neg (fun h => hab (h.2.symm.trans hdi))]
    exact Matrix.one_apply_ne (by rintro rfl; exact hp rfl)
  have hxoff : ∀ p q : Fin 6, p ≠ q → mM6 x p q = 0 := by
    intro p q hpq
    by_cases hpi : p = i
    · rw [hpi]
      exact hx_i_off q (by rintro rfl; exact hpq (by rw [hpi]))
    · by_cases hqi : q = i
      · rw [hqi]
        exact hx_off_i p hpi
      · have hp : d p = a := hdne p hpi
        have hq : d q = a := hdne q hqi
        have h1 := hxentry ⟨p, hp⟩ ⟨q, hq⟩
        rw [hA0off (eW ⟨p, hp⟩) (eW ⟨q, hq⟩) (by
          intro h
          exact hpq (by
            have := eW.injective h
            simpa using this))] at h1
        exact h1
  have hx_comm : M * mM6 x = mM6 x * M := by
    have := congrArg (fun z : GL (Fin 6) F4 => ((z : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4)) (hcomm A)
    simpa [M, x] using this
  have hrow : ∀ j : Blk d a, M i j.1 = 0 := by
    intro j
    have h := congrFun (congrFun hx_comm i) j.1
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    have hL : ∑ k, M i k * mM6 x k j.1 = M i j.1 * mM6 x j.1 j.1 := by
      rw [Finset.sum_eq_single j.1]
      · intro k _ hk
        rw [hxoff k j.1 hk, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j.1) hj
    have hR : ∑ k, mM6 x i k * M k j.1 = mM6 x i i * M i j.1 := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hxoff i k (Ne.symm hk), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hL, hR, hxii, one_mul, hxentry j j, hA0diag (eW j)] at h
    have h1 : ((diagOmega (eW j0) (eW j) : F4) - 1) * M i j.1 = 0 := by
      rw [sub_mul, one_mul, mul_comm (diagOmega (eW j0) (eW j) : F4) (M i j.1), h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (hd0 j))
  have hcol : ∀ j : Blk d a, M j.1 i = 0 := by
    intro j
    have h := congrFun (congrFun hx_comm j.1) i
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    have hL : ∑ k, M j.1 k * mM6 x k i = M j.1 i * mM6 x i i := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hxoff k i hk, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hR : ∑ k, mM6 x j.1 k * M k i = mM6 x j.1 j.1 * M j.1 i := by
      rw [Finset.sum_eq_single j.1]
      · intro k _ hk
        rw [hxoff j.1 k (Ne.symm hk), zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j.1) hj
    rw [hL, hR, hxii, mul_one, hxentry j j, hA0diag (eW j)] at h
    have h1 : (1 - (diagOmega (eW j0) (eW j) : F4)) * M j.1 i = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm (hd0 j)))
  let B : Matrix (Blk d a) (Blk d a) F4 := blkM d a M
  have hreindex_mul : ∀ P Q : Matrix (Blk d a) (Blk d a) F4,
      Matrix.reindex eW eW (P * Q) = Matrix.reindex eW eW P * Matrix.reindex eW eW Q := by
    intro P Q
    change (P * Q).submatrix eW.symm eW.symm =
      P.submatrix eW.symm eW.symm * Q.submatrix eW.symm eW.symm
    rw [Matrix.submatrix_mul_equiv P Q eW.symm eW.symm eW.symm]
  have hBcomm : ∀ A1 : ↥(StatedSU 5 (2 ^ 1) F4),
      (Matrix.reindex eW eW B) * ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
        ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) *
          (Matrix.reindex eW eW B) := by
    intro A1
    let A' := liftSU eW A1
    let x' := embSU d a A'
    have hx'comm : M * mM6 x' = mM6 x' * M := by
      have := congrArg (fun z : GL (Fin 6) F4 => ((z : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4)) (hcomm A')
      simpa [M, x'] using this
    have hx'entry : ∀ p q : Blk d a, mM6 x' p q =
        ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) (eW p) (eW q) :=
      fun p q => mM6_embSU_liftSU_apply eW A1 p q
    have hx'_off_i : ∀ p : Fin 6, p ≠ i → mM6 x' p i = 0 := by
      intro p hp
      rw [mM6_embSU, extMat_apply]
      rw [dif_neg (fun h => hab (h.2.symm.trans hdi))]
      exact Matrix.one_apply_ne (by rintro rfl; exact hp rfl)
    let Ab : Matrix (Blk d a) (Blk d a) F4 :=
      Matrix.reindex eW.symm eW.symm ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)
    have hAbentry : ∀ p q : Blk d a, Ab p q =
        ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) (eW p) (eW q) := by
      intro p q
      change Matrix.reindex eW.symm eW.symm
        ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) p q = _
      rw [Matrix.reindex_apply, Equiv.symm_symm]
      rfl
    have hBAb : B * Ab = Ab * B := by
      ext j k
      have h := congrFun (congrFun hx'comm j.1) k.1
      rw [Matrix.mul_apply, Matrix.mul_apply] at h
      have hji : j.1 ≠ i := by
        rintro rfl
        exact hab ((hdi.symm.trans j.2).symm)
      have hL : ∑ l : Fin 6, M j.1 l * mM6 x' l k.1 =
          ∑ l : Blk d a, B j l * Ab l k := by
        rw [sum_blk d a (fun l => M j.1 l * mM6 x' l k.1) ?_]
        · apply Finset.sum_congr rfl
          intro l _
          rw [hx'entry l k, hAbentry]
          rfl
        · intro l hl
          have hli : l = i := by
            by_contra hne
            exact hl (hdne l hne)
          rw [hli, hcol j, zero_mul]
      have hR : ∑ l : Fin 6, mM6 x' j.1 l * M l k.1 =
          ∑ l : Blk d a, Ab j l * B l k := by
        rw [sum_blk d a (fun l => mM6 x' j.1 l * M l k.1) ?_]
        · apply Finset.sum_congr rfl
          intro l _
          rw [hx'entry j l, hAbentry]
          rfl
        · intro l hl
          have hli : l = i := by
            by_contra hne
            exact hl (hdne l hne)
          rw [hli, hx'_off_i j.1 hji, zero_mul]
      rw [hL, hR] at h
      simpa [B, Ab, Matrix.mul_apply] using h
    have hreindex_Ab : Matrix.reindex eW eW Ab =
        ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) := by
      have hsymm : (Matrix.reindex eW eW).symm
          ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) = Ab := rfl
      rw [← hsymm]
      exact (Matrix.reindex eW eW).apply_symm_apply _
    calc (Matrix.reindex eW eW B) * ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)
        = (Matrix.reindex eW eW B) * (Matrix.reindex eW eW Ab) := by rw [hreindex_Ab]
      _ = Matrix.reindex eW eW (B * Ab) := (hreindex_mul B Ab).symm
      _ = Matrix.reindex eW eW (Ab * B) := by rw [hBAb]
      _ = (Matrix.reindex eW eW Ab) * (Matrix.reindex eW eW B) := hreindex_mul Ab B
      _ = ((A1 : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) *
            (Matrix.reindex eW eW B) := by rw [hreindex_Ab]
  obtain ⟨ν, hν⟩ := eq_scalar_of_commute_statedSU5 (Matrix.reindex eW eW B) hBcomm
  have hreindex_scalar : Matrix.reindex eW eW (Matrix.scalar (Blk d a) ν) =
      Matrix.scalar (Fin 5) ν := by
    ext p q
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · subst hpq
      simp
    · have h : eW.symm p ≠ eW.symm q := fun hh => hpq (eW.symm.injective hh)
      rw [if_neg h, if_neg hpq]
  have hBscalar : B = Matrix.scalar (Blk d a) ν := by
    apply (Matrix.reindex eW eW).injective
    rw [hν, hreindex_scalar]
  have hdiagW : ∀ j : Blk d a, M j.1 j.1 = ν := by
    intro j
    have hh := congrFun (congrFun hBscalar j) j
    simpa [B, CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.blkM, Matrix.scalar_apply] using hh
  have hoffW : ∀ j k : Blk d a, j ≠ k → M j.1 k.1 = 0 := by
    intro j k hjk
    have hval : M j.1 k.1 = (Matrix.scalar (Blk d a) ν) j k := by
      have hh := congrFun (congrFun hBscalar j) k
      simpa [B, CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.blkM, Matrix.scalar_apply] using hh
    rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hjk]
  refine ⟨ν, M i i, ?_⟩
  ext p q
  rw [Matrix.diagonal_apply]
  by_cases hpq : p = q
  · rw [if_pos hpq]
    by_cases hpi : p = i
    · have hqi : q = i := by rw [← hpq, hpi]
      rw [hpi, hqi, Function.update_self]
    · have hp : d p = a := hdne p hpi
      rw [show Function.update (fun _ => ν) i (M i i) p = ν by simp [Function.update, hpi]]
      rw [← hpq]
      change M p p = ν
      exact hdiagW ⟨p, hp⟩
  · rw [if_neg hpq]
    by_cases hpi : p = i
    · rw [hpi]
      change M i q = 0
      refine hrow ⟨q, ?_⟩
      exact hdne q (by rintro rfl; exact hpq (by rw [hpi]))
    · by_cases hqi : q = i
      · rw [hqi]
        change M p i = 0
        exact hcol ⟨p, hdne p hpi⟩
      · change M p q = 0
        refine hoffW ⟨p, hdne p hpi⟩ ⟨q, hdne q hqi⟩ ?_
        rintro h
        exact hpq (by simpa using congrArg Subtype.val h)


private theorem scalar_gu_mem (c : F4ˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) F4) ∈ Gu := by
  change ((↑(Matrix.GeneralLinearGroup.scalar (Fin 6) c) : Matrix (Fin 6) (Fin 6) F4).map
      hF4.bar)ᵀ * CFSG.RankThree.PartOne.KCUnitaryModel.idGram F4 6 *
        (↑(Matrix.GeneralLinearGroup.scalar (Fin 6) c) : Matrix (Fin 6) (Fin 6) F4) =
    CFSG.RankThree.PartOne.KCUnitaryModel.idGram F4 6
  rw [show CFSG.RankThree.PartOne.KCUnitaryModel.idGram F4 6 =
      ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) from rfl, Units.val_one,
    Matrix.mul_one]
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero hF4.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  have hbar : hF4.bar (c : F4) = (c : F4) ^ 2 := bar_apply c
  rw [hbar]
  calc (c : F4) ^ 2 * (c : F4) = (c : F4) ^ 3 := by ring
    _ = 1 := pow_three_of_units c

private theorem exists_pow_eq_of_ne_one (μ : F4ˣ) (hμ1 : μ ≠ 1) (hμ3 : μ ^ 3 = 1) :
    ∀ δ : F4ˣ, ∃ k : ℕ, μ ^ k = δ := by
  have horder : orderOf μ = 3 := by
    have hdvd : orderOf μ ∣ 3 := orderOf_dvd_of_pow_eq_one hμ3
    have hne : orderOf μ ≠ 1 := fun h => hμ1 ((orderOf_eq_one_iff).mp h)
    have hle : orderOf μ ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf μ := orderOf_pos μ
    interval_cases orderOf μ
    · exact absurd rfl hne
    · norm_num at hdvd
    · rfl
  have hcard : Fintype.card F4ˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card, F4.card]
  let f : Fin 3 → F4ˣ := fun k => μ ^ (k : ℕ)
  have hinj : Function.Injective f := by
    intro a b hab
    have hmod : (a : ℕ) ≡ (b : ℕ) [MOD orderOf μ] := (pow_eq_pow_iff_modEq).mp hab
    rw [horder] at hmod
    have hmod' : (a : ℕ) % 3 = (b : ℕ) % 3 := hmod
    rw [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at hmod'
    exact Fin.ext hmod'
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by rw [Fintype.card_fin, hcard]⟩
  intro δ
  obtain ⟨k, hk⟩ := hbij.surjective δ
  exact ⟨(k : ℕ), hk⟩


private theorem centralizer_zpowers_diag
    {D : GL (Fin 6) F4} {Dg : Gu} (hval : (Dg : GL (Fin 6) F4) = D)
    {a b : F4} {i : Fin 6} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => a) i b))
    (h : PGU6) (hfix : ∀ x ∈ fixSubgroup (Psi0 Dg), Psi h x = x) :
    h ∈ Subgroup.zpowers (QuotientGroup.mk Dg) := by
  let d : Fin 6 → F4 := Function.update (fun _ => a) i b
  have hdi : d i = b := by simp [d, Function.update]
  have hdne : ∀ j : Fin 6, j ≠ i → d j = a := by
    intro j hj
    simp [d, Function.update, hj]
  obtain ⟨ĥ, hĥ⟩ := QuotientGroup.mk'_surjective
    (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) h
  have hcomm := commute_embSU_of_fixing hval ha hb hab hD h ĥ hĥ hfix
  obtain ⟨ν, c, hHdiag⟩ := block_scalar_of_commute hdi hdne hab ĥ hcomm
  have hdet_ne : ((ĥ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det ≠ 0 := by
    have hunit : IsUnit (((ĥ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :=
      (ĥ : GL (Fin 6) F4).isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hdetdiag : (Matrix.diagonal (Function.update (fun _ => ν) i c)).det ≠ 0 := by
    rwa [← hHdiag]
  rw [Matrix.det_diagonal] at hdetdiag
  obtain ⟨j1, hj1⟩ : ∃ j : Fin 6, j ≠ i :=
    ⟨if i = 0 then 1 else 0, by
      split_ifs with h0
      · rw [h0]; decide
      · exact Ne.symm h0⟩
  have hν0 : ν ≠ 0 := by
    intro h0
    have hfac : Function.update (fun _ => ν) i c j1 = 0 := by
      rw [Function.update_apply, if_neg hj1]
      exact h0
    exact hdetdiag (Finset.prod_eq_zero (Finset.mem_univ j1) hfac)
  have hc0 : c ≠ 0 := by
    intro h0
    have hfac : Function.update (fun _ => ν) i c i = 0 := by
      rw [Function.update_self]
      exact h0
    exact hdetdiag (Finset.prod_eq_zero (Finset.mem_univ i) hfac)
  let aU : F4ˣ := Units.mk0 a ha
  let bU : F4ˣ := Units.mk0 b hb
  let μ : F4ˣ := bU * aU⁻¹
  let δ : F4ˣ := Units.mk0 (c * ν⁻¹) (mul_ne_zero hc0 (inv_ne_zero hν0))
  have hμ1 : μ ≠ 1 := by
    intro hμ
    have hvalμ : (μ : F4) = b * a⁻¹ := by simp [μ, aU, bU]
    have h1 : (μ : F4) = 1 := by rw [hμ]; rfl
    rw [hvalμ] at h1
    have h2 : b = a := by
      have := congrArg (fun x : F4 => x * a) h1
      simpa [mul_assoc, inv_mul_cancel₀ ha] using this
    exact hab h2.symm
  obtain ⟨k, hk⟩ := exists_pow_eq_of_ne_one μ hμ1 (units_cube μ) δ
  have hkval : (μ : F4) ^ k = c * ν⁻¹ := by
    have := congrArg (fun u : F4ˣ => (u : F4)) hk
    simpa [δ] using this
  let aG : Gu := ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) aU, scalar_gu_mem aU⟩
  let sG : Gu := aG⁻¹ * Dg
  have hsGval : (sG : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) aU⁻¹ * (Dg : GL (Fin 6) F4) := rfl
  have hsGmat : ((sG : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => 1) i (μ : F4)) := by
    rw [hsGval, hval]
    change (((Matrix.GeneralLinearGroup.scalar (Fin 6) aU⁻¹ : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) * (D : Matrix (Fin 6) (Fin 6) F4)) = _
    rw [hD, scalar_mul_eq_smul]
    ext p q
    rw [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · subst hpq
      by_cases hpi : p = i
      · simp [hpi, μ, aU, bU, mul_comm]
      · simp [hpi, aU, inv_mul_cancel₀ ha]
    · simp [hpq]
  have hsGpow_mat : (((sG ^ k : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update (fun _ => 1) i ((μ : F4) ^ k)) := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsGmat, Matrix.diagonal_pow]
    congr 1
    funext p
    by_cases hpi : p = i <;> simp [Function.update, hpi]
  let νU : F4ˣ := Units.mk0 ν hν0
  have hĥeq : (ĥ : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) νU * (sG ^ k : Gu) := by
    apply Units.ext
    change ((ĥ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (((Matrix.GeneralLinearGroup.scalar (Fin 6) νU : GL (Fin 6) F4) *
        ((sG ^ k : Gu) : GL (Fin 6) F4)) : Matrix (Fin 6) (Fin 6) F4)
    rw [hHdiag, scalar_mul_eq_smul, hsGpow_mat]
    ext p q
    rw [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · subst hpq
      by_cases hpi : p = i
      · have h1 : (ν : F4) * (μ : F4) ^ k = c := by
          calc (ν : F4) * (μ : F4) ^ k = (ν : F4) * (c * ν⁻¹) := by rw [hkval]
            _ = c := by field_simp
        simp [hpi, νU, h1]
      · simp [hpi, νU]
    · simp [hpq]
  have hmks : QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) sG =
    QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) Dg := by
    have hs : QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) sG =
    (QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) aG)⁻¹ *
      QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) Dg := by
      rw [show sG = aG⁻¹ * Dg from rfl, map_mul, map_inv]
    rw [hs]
    have ha1 : QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) aG = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_ZG.mpr ⟨aU, rfl⟩
    rw [ha1, inv_one, one_mul]
  have hmkν : QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG)
      (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) νU, scalar_gu_mem νU⟩ : Gu) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_ZG.mpr ⟨νU, rfl⟩
  have hĥeqGu : ĥ = (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) νU,
      scalar_gu_mem νU⟩ : Gu) * (sG ^ k : Gu) := Subtype.ext hĥeq
  have hmk : QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) ĥ =
    (QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) Dg) ^ k := by
    rw [hĥeqGu, map_mul, map_pow, hmkν, hmks, one_mul]
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  change (QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) Dg) ^ k = h
  rw [← hmk, hĥ]


private lemma fixSubgroup_mul_conj {K : Type*} [Group K] (φ α : MulAut K) :
    fixSubgroup (φ * α * φ⁻¹) = (fixSubgroup α).map φ.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_map.mpr ⟨φ⁻¹ x, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h := congrArg (fun z => φ⁻¹ z) hx
    simpa using h
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixSubgroup]
    simpa using (mem_fixSubgroup.mp hy)

private lemma mem_zpowers_conj {G : Type*} [Group G] {x y c : G}
    (h : x ∈ Subgroup.zpowers y) : c * x * c⁻¹ ∈ Subgroup.zpowers (c * y * c⁻¹) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  calc (c * y * c⁻¹) ^ k = ((MulAut.conj c) y) ^ k := by rw [MulAut.conj_apply]
    _ = (MulAut.conj c) (y ^ k) := (map_zpow (MulAut.conj c) y k).symm
    _ = c * y ^ k * c⁻¹ := by rw [MulAut.conj_apply]

private theorem card_blk_update {a b : F4} {i : Fin 6} (hab : a ≠ b) :
    Fintype.card (Blk (Function.update (fun _ => a) i b) a) = 5 := by
  rw [Fintype.card_subtype]
  have hfilter : Finset.univ.filter
      (fun j : Fin 6 => Function.update (fun _ => a) i b j = a) = Finset.univ.erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hj
      refine ⟨?_, trivial⟩
      rintro rfl
      rw [Function.update_self] at hj
      exact hab hj.symm
    · rintro ⟨hji, -⟩
      rw [Function.update_apply, if_neg hji]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

private theorem card_statedSU_five : Nat.card ↥(StatedSU 5 (2 ^ 1) F4) = 13685760 := by
  have h := CFSG.RankThree.PartOne.KFU.card_statedSU_eq hF4 (n := 5) (by norm_num)
  have hp : ∏ i ∈ Finset.Icc 2 5, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 13365 := by decide
  rw [hp] at h
  norm_num at h
  exact_mod_cast h

theorem prFix_holds : PRFix := by
  intro g hpr
  obtain ⟨ĝ, P, a, b, i, hg, hab, hdiag⟩ := hpr
  let Dg : Gu := P⁻¹ * ĝ * P
  have hval : (Dg : GL (Fin 6) F4) = (⟨((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4),
      (P⁻¹ * ĝ * P).2⟩ : Gu) := rfl
  have hDval : (Dg : GL (Fin 6) F4) =
      (⟨((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4), (P⁻¹ * ĝ * P).2⟩ : Gu) := rfl
  let d : Fin 6 → F4 := Function.update (fun _ => a) i b
  have hDd : ((Dg : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hdiag
  have hdi : d i = b := by simp [d, Function.update]
  have hdne : ∀ j : Fin 6, j ≠ i → d j = a := by
    intro j hj
    simp [d, Function.update, hj]
  have hdet_ne : ((Dg : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det ≠ 0 := by
    have hunit : IsUnit (((Dg : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :=
      (Dg : GL (Fin 6) F4).isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hprod : ∏ j, d j ≠ 0 := by
    rw [← Matrix.det_diagonal, ← hDd]
    exact hdet_ne
  obtain ⟨j1, hj1⟩ : ∃ j : Fin 6, j ≠ i :=
    ⟨if i = 0 then 1 else 0, by
      split_ifs with h0
      · rw [h0]; decide
      · exact Ne.symm h0⟩
  have ha : a ≠ 0 := by
    intro h0
    have hdj : d j1 = a := hdne j1 hj1
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ j1) (by rw [hdj]; exact h0))
  have hb : b ≠ 0 := by
    intro h0
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hdi]; exact h0))
  have hcardW : Fintype.card (Blk d a) = 5 := card_blk_update hab
  haveI hFdiagSimple : IsSimpleGroup ↥(fixSubgroup (Psi0 Dg)) := by
    haveI hSU : IsSimpleGroup ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4) := by
      rw [hcardW]
      exact isSimple_statedSU 5 (Or.inr rfl)
    exact (diagFixEquiv hDval ha hb hab hDd).symm.isSimpleGroup
  haveI hFdiagPerf : Group.IsPerfect ↥(fixSubgroup (Psi0 Dg)) := by
    haveI hSUperf : Group.IsPerfect ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4) := by
      rw [hcardW]
      exact isPerfect_statedSU_five
    exact Group.IsPerfect.ofSurjective (f := (diagFixEquiv hDval ha hb hab hDd).toMonoidHom)
      (diagFixEquiv hDval ha hb hab hDd).surjective
  let Pbar : PGU6 := QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) P
  let gs : PGU6 := QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG) Dg
  have hgmul : g = Pbar * gs * Pbar⁻¹ := by
    have hconj : ĝ = P * Dg * P⁻¹ := by
      simp [Dg]
      group
    rw [← hg]
    change (QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG)) ĝ = _
    rw [hconj]
    change (QuotientGroup.mk' (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.ZG)) (P * Dg * P⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hPsi : Psi g = Psi Pbar * Psi gs * (Psi Pbar)⁻¹ := by
    rw [hgmul, map_mul, map_mul, map_inv]
  have hPsiDg : Psi gs = Psi0 Dg := Psi_mk Dg
  have hFix : fixSubgroup (Psi g) = (fixSubgroup (Psi0 Dg)).map (Psi Pbar).toMonoidHom := by
    rw [hPsi, hPsiDg, fixSubgroup_mul_conj]
  let eMap : ↥(fixSubgroup (Psi0 Dg)) ≃* ↥(fixSubgroup (Psi g)) :=
    (Subgroup.equivMapOfInjective (fixSubgroup (Psi0 Dg)) (Psi Pbar).toMonoidHom
      (Psi Pbar).injective).trans (MulEquiv.subgroupCongr hFix.symm)
  haveI hFSimple : IsSimpleGroup ↥(fixSubgroup (Psi g)) := eMap.symm.isSimpleGroup
  haveI hFPerf : Group.IsPerfect ↥(fixSubgroup (Psi g)) :=
    Group.IsPerfect.ofSurjective (f := eMap.toMonoidHom) eMap.surjective
  have hFPerfComm : ⁅fixSubgroup (Psi g), fixSubgroup (Psi g)⁆ = fixSubgroup (Psi g) :=
    Subgroup.isPerfect_iff.mp hFPerf
  have hcardF : Nat.card ↥(fixSubgroup (Psi g)) = 13685760 := by
    calc Nat.card ↥(fixSubgroup (Psi g)) = Nat.card ↥(fixSubgroup (Psi0 Dg)) :=
          (Nat.card_congr eMap.toEquiv).symm
      _ = Nat.card ↥(StatedSU (Fintype.card (Blk d a)) (2 ^ 1) F4) :=
          (Nat.card_congr (diagFixEquiv hDval ha hb hab hDd).toEquiv).symm
      _ = 13685760 := by rw [hcardW]; exact card_statedSU_five
  have hEleven : 11 ∣ Nat.card ↥(fixSubgroup (Psi g)) := by
    rw [hcardF]
    norm_num
  refine ⟨hFSimple, hFPerfComm, hEleven, ?_⟩
  intro h hfixF
  let h' : PGU6 := Pbar⁻¹ * h * Pbar
  have hfixD : ∀ x ∈ fixSubgroup (Psi0 Dg), Psi h' x = x := by
    intro x hx
    have hxmap : Psi Pbar x ∈ fixSubgroup (Psi g) := by
      rw [hFix]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h1 := hfixF _ hxmap
    have h2 : Psi h' x = (Psi Pbar)⁻¹ (Psi h (Psi Pbar x)) := by
      simp [h', map_mul, map_inv]
    rw [h2, h1]
    simp
  have hz : h' ∈ Subgroup.zpowers gs :=
    centralizer_zpowers_diag hval ha hb hab hDd h' hfixD
  have hzg : Pbar * h' * Pbar⁻¹ ∈ Subgroup.zpowers (Pbar * gs * Pbar⁻¹) :=
    mem_zpowers_conj hz
  have hh : h = Pbar * h' * Pbar⁻¹ := by
    simp [h']
    group
  rwa [hh, hgmul]

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
