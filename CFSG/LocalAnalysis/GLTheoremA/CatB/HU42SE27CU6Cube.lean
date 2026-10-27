module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Defs
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUComp
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.ClassicalGroups.UnitaryFlag
open Matrix

private theorem cube_roots_sum_zero {c u v : F4} (hc : c ^ 3 = 1) (hu : u ^ 3 = 1)
    (hv : v ^ 3 = 1) (hcu : c ≠ u) (hcv : c ≠ v) (huv : u ≠ v) : c + u + v = 0 := by
  revert c u v
  decide

private theorem cube_root_ne_zero {x : F4} (hx : x ^ 3 = 1) : x ≠ 0 := by
  rintro rfl
  exact zero_ne_one (α := F4) (by simpa using hx)

private theorem exists_pow_mul (u v ω x y : F4) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (huv : u ≠ v) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    ∃ n m : Fin 3, u ^ (n : ℕ) * ω ^ (m : ℕ) = x ∧ v ^ (n : ℕ) * ω ^ (m : ℕ) = y := by
  revert u v ω x y
  decide

private theorem omega_cube : (F4.ω : F4) ^ 3 = 1 := by
  decide

private theorem omega_ne_one : (F4.ω : F4) ≠ 1 := by
  decide

private theorem diagonal_inv_eq (v : Fin 6 → F4) (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hv i)

private theorem trace_conj (A B : GL (Fin 6) F4) :
    (((A * B * A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).trace =
      ((B : Matrix (Fin 6) (Fin 6) F4)).trace := by
  calc (((A * B * A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).trace
      = ((A : Matrix (Fin 6) (Fin 6) F4) * (B : Matrix (Fin 6) (Fin 6) F4) *
          ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).trace := by
        rw [Units.val_mul, Units.val_mul]
    _ = ((A : Matrix (Fin 6) (Fin 6) F4) * ((B : Matrix (Fin 6) (Fin 6) F4) *
          ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))).trace := by rw [mul_assoc]
    _ = (((B : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4)) * (A : Matrix (Fin 6) (Fin 6) F4)).trace :=
        Matrix.trace_mul_comm _ _
    _ = ((B : Matrix (Fin 6) (Fin 6) F4) * (((A⁻¹ : GL (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4) * (A : Matrix (Fin 6) (Fin 6) F4))).trace := by
        rw [mul_assoc]
    _ = ((B : Matrix (Fin 6) (Fin 6) F4)).trace := by
        rw [show (((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
          (A : Matrix (Fin 6) (Fin 6) F4)) = 1 from by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one], mul_one]

private theorem mul_diagonal_const_eq_smul (B : Matrix (Fin 6) (Fin 6) F4) (lam : F4) :
    B * Matrix.diagonal (fun _ : Fin 6 => lam) = lam • B := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.smul_apply]
  exact mul_comm _ _

private theorem trace_mul_diagonal_const (B : Matrix (Fin 6) (Fin 6) F4) (lam : F4) :
    (B * Matrix.diagonal (fun _ : Fin 6 => lam)).trace = lam * B.trace := by
  rw [mul_diagonal_const_eq_smul, Matrix.trace_smul, smul_eq_mul]

private theorem mem_Z6_iff {z : M6} :
    z ∈ Z6 ↔ ∃ c : F4ˣ, (z : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  rw [Z6, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩

private theorem conjM6_mem_Z6 (P : primeFormUnitary hF4 (idGram F4 6)) {z : M6} (hz : z ∈ Z6) :
    conjM6 P z ∈ Z6 := by
  obtain ⟨c, hc⟩ := mem_Z6_iff.1 hz
  rw [mem_Z6_iff]
  refine ⟨c, ?_⟩
  rw [conjM6_apply, hc, (commute_scalar c (P : GL (Fin 6) F4)).eq, mul_inv_cancel_right]

private theorem conjM6_symm (P : primeFormUnitary hF4 (idGram F4 6)) :
    (conjM6 P).symm = conjM6 P⁻¹ := by
  apply MulEquiv.ext
  intro x
  apply (conjM6 P).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [conjM6_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  group

private theorem CenD_single_cube {d : Fin 6 → F4} {Dm : M6}
    (hD : mM6 Dm = Matrix.diagonal d) (x : ↥(CenD (Dm : GL (Fin 6) F4)))
    {i : Fin 6} (hi : ∀ k, d k = d i → k = i) : (mM6 (x : M6) i i) ^ 3 = 1 := by
  have h := congrFun (congrFun (M6_unitary (x : M6)) i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply,
    if_pos rfl] at h
  have hsum : ∑ k, bar (mM6 (x : M6) k i) * mM6 (x : M6) k i =
      bar (mM6 (x : M6) i i) * mM6 (x : M6) i i := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      have hd : d k ≠ d i := fun h' => hk (hi k h')
      rw [CenD_zero hD x hd]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hsum, bar_apply] at h
  calc (mM6 (x : M6) i i) ^ 3 = (mM6 (x : M6) i i) ^ 2 * mM6 (x : M6) i i := by ring
    _ = 1 := h

private theorem big_structure {d : Fin 6 → F4} (hdet : ∏ i, d i = 1)
    (hcube : ∀ i, d i ^ 3 = 1) (c : F4) (hc4 : 4 ≤ Fintype.card (Blk d c))
    (hc5 : Fintype.card (Blk d c) ≤ 5) :
    c ^ 3 = 1 ∧ Fintype.card (Blk d c) = 4 ∧ (∑ i, d i = c) ∧
      ∃ a b : Fin 6, a ≠ b ∧ d a ≠ c ∧ d b ≠ c ∧ d a ≠ d b ∧
        Finset.univ.filter (fun i : Fin 6 => d i ≠ c) = {a, b} := by
  let S : Finset (Fin 6) := Finset.univ.filter (fun i : Fin 6 => d i = c)
  let Sc : Finset (Fin 6) := Finset.univ.filter (fun i : Fin 6 => d i ≠ c)
  have hSprod : (S.prod d) = c ^ Fintype.card (Blk d c) := by
    rw [show S = Finset.univ.filter (fun i : Fin 6 => d i = c) from rfl]
    rw [Finset.prod_subtype (p := fun i : Fin 6 => d i = c)
      (s := Finset.univ.filter (fun i : Fin 6 => d i = c)) (by simp) (fun i => d i)]
    rw [Finset.prod_congr rfl (fun x _ => x.2)]
    rw [Finset.prod_const, Finset.card_univ]
  have hprod_split : (S.prod d) * (Sc.prod d) = Finset.univ.prod d := by
    rw [show S = Finset.univ.filter (fun i : Fin 6 => d i = c) from rfl]
    rw [show Sc = Finset.univ.filter (fun i : Fin 6 => ¬ d i = c) from rfl]
    exact Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
      (p := fun i : Fin 6 => d i = c) (f := d)
  have hScard : Sc.card = 6 - Fintype.card (Blk d c) := by
    have h1 : Sc.card = Fintype.card {i : Fin 6 // d i ≠ c} := by
      rw [Fintype.card_subtype]
    rw [h1, Fintype.card_subtype_compl (fun i : Fin 6 => d i = c)]
    simp
  have hcpos : 0 < Fintype.card (Blk d c) := by omega
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.1 hcpos
  have hc3 : c ^ 3 = 1 := by
    have := hcube i₀
    rwa [i₀.2] at this
  have hcard_ne_five : Fintype.card (Blk d c) ≠ 5 := by
    intro h5
    have hScard1 : Sc.card = 1 := by
      rw [hScard, h5]
    obtain ⟨j, hSj⟩ := Finset.card_eq_one.1 hScard1
    have hdj : d j ≠ c := by
      have hmem : j ∈ Sc := by
        rw [hSj]
        simp
      simpa [Sc] using hmem
    have hprod : Finset.univ.prod d = c ^ 5 * d j := by
      rw [← hprod_split, hSprod, h5, hSj, Finset.prod_singleton]
    rw [show ∏ i, d i = c ^ 5 * d j from hprod] at hdet
    have hc5eq : c ^ 5 = c ^ 2 := by
      rw [show (5 : ℕ) = 2 + 3 by norm_num, pow_add, hc3, mul_one]
    rw [hc5eq] at hdet
    have hdj_eq : d j = c := by
      have h := congrArg (fun x : F4 => c * x) hdet
      have h1 : c * (c ^ 2 * d j) = d j := by
        rw [← mul_assoc, show c * c ^ 2 = c ^ 3 from by ring, hc3, one_mul]
      rw [h1, mul_one] at h
      exact h
    exact hdj hdj_eq
  have hcard4 : Fintype.card (Blk d c) = 4 := by omega
  have hScard2 : Sc.card = 2 := by
    rw [hScard, hcard4]
  obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.1 hScard2
  have hda : d a ≠ c := by
    have hmem : a ∈ Sc := by
      rw [hSab]
      simp
    simpa [Sc] using hmem
  have hdb : d b ≠ c := by
    have hmem : b ∈ Sc := by
      rw [hSab]
      simp
    simpa [Sc] using hmem
  have hdab : d a ≠ d b := by
    intro heq
    have hprod4 : Finset.univ.prod d = c ^ 4 * d a * d b := by
      rw [← hprod_split, hSprod, hcard4, hSab, Finset.prod_pair hab]
      ring
    rw [show ∏ i, d i = c ^ 4 * d a * d b from hprod4, heq] at hdet
    have hc4eq : c ^ 4 = c := by
      rw [show (4 : ℕ) = 1 + 3 by norm_num, pow_add, hc3, mul_one, pow_one]
    rw [hc4eq] at hdet
    have hdb_eq : d b = c := by
      have h := congrArg (fun x : F4 => c ^ 2 * x) hdet
      have h1 : c ^ 2 * (c * d b * d b) = (d b) ^ 2 := by
        calc c ^ 2 * (c * d b * d b) = (c ^ 2 * c) * (d b * d b) := by ring
          _ = (d b) ^ 2 := by
              rw [show c ^ 2 * c = c ^ 3 from by ring, hc3, one_mul]
              ring
      rw [h1, mul_one] at h
      calc d b = ((d b) ^ 2) ^ 2 := (CFSG.Fischer.F4.sq_sq (d b)).symm
        _ = (c ^ 2) ^ 2 := by rw [h]
        _ = c := CFSG.Fischer.F4.sq_sq c
    exact hdb hdb_eq
  have hSsum : S.sum d = (Fintype.card (Blk d c) : F4) * c := by
    rw [show S = Finset.univ.filter (fun i : Fin 6 => d i = c) from rfl]
    rw [Finset.sum_subtype (p := fun i : Fin 6 => d i = c)
      (s := Finset.univ.filter (fun i : Fin 6 => d i = c)) (by simp) (fun i => d i)]
    rw [Finset.sum_congr rfl (fun x _ => x.2)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hScsum : Sc.sum d = d a + d b := by
    rw [show Sc = {a, b} from hSab, Finset.sum_pair hab]
  have hsplit' : S.sum d + Sc.sum d = ∑ i, d i := by
    rw [show S = Finset.univ.filter (fun i : Fin 6 => d i = c) from rfl]
    rw [show Sc = Finset.univ.filter (fun i : Fin 6 => ¬ d i = c) from rfl]
    exact Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i : Fin 6 => d i = c) (f := d)
  have h4zero : ((Fintype.card (Blk d c) : ℕ) : F4) = 0 := by
    rw [hcard4]
    decide
  have hsum_eq : ∑ i, d i = c := by
    have hzero : c + d a + d b = 0 := cube_roots_sum_zero hc3 (hcube a) (hcube b)
      (Ne.symm hda) (Ne.symm hdb) hdab
    have hcc : c + c = 0 := by
      rw [← two_mul, F4.two_eq_zero, zero_mul]
    have h1 : c + (d a + d b) = 0 := by
      rw [← add_assoc]
      exact hzero
    have h2 : d a + d b = c := by
      calc d a + d b = (c + c) + (d a + d b) := by rw [hcc, zero_add]
        _ = c + (c + (d a + d b)) := by rw [add_assoc]
        _ = c + 0 := by rw [h1]
        _ = c := add_zero c
    rw [← hsplit', hSsum, hScsum, h4zero, zero_mul, zero_add, h2]
  exact ⟨hc3, hcard4, hsum_eq, a, b, hab, hda, hdb, hdab, hSab⟩

private theorem card_statedSU_four : Nat.card ↥(StatedSU 4 (2 ^ 1) F4) = 25920 := by
  have h4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.statedProj_equiv_statedSU_four
    (E := F4) F4.card
  calc Nat.card ↥(StatedSU 4 (2 ^ 1) F4)
      = Nat.card ↥(StatedSU 4 2 F4) := by rw [show (2 ^ 1 : ℕ) = 2 from rfl]
    _ = Nat.card (StatedProj (StatedSU 4 2 F4)) := (Nat.card_congr eP.toEquiv).symm
    _ = 25920 := CFSG.LocalAnalysis.GLTheoremA.HSubT.natCard_statedProj_statedSU_four h4

private theorem not_isMulCommutative_statedSU_four :
    ¬ IsMulCommutative ↥(StatedSU 4 (2 ^ 1) F4) := by
  intro h
  apply CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.not_comm_range
  refine isMulCommutative_iff.2 fun x y => ?_
  obtain ⟨x', rfl⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.PhiEquiv.surjective x
  obtain ⟨y', rfl⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.PhiEquiv.surjective y
  rw [← map_mul, ← map_mul, isMulCommutative_iff.1 h x' y']

section BigCase

variable {Dm : M6} {d : Fin 6 → F4} {c : F4} {a b : Fin 6}

private theorem big_range_le_CenD (hD : mM6 Dm = Matrix.diagonal d) :
    (embSU d c).range ≤ CenD (Dm : GL (Fin 6) F4) := by
  rintro _ ⟨A, rfl⟩
  exact embSU_mem_CenD d c hD A

private theorem big_range_simple (hcard4 : Fintype.card (Blk d c) = 4) :
    IsSimpleGroup ↥(embSU d c).range := by
  haveI : IsSimpleGroup ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) := by
    rw [hcard4]
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.isSimple_M4
  exact (MonoidHom.ofInjective (embSU_injective d c)).symm.isSimpleGroup

private theorem big_range_notcomm (hcard4 : Fintype.card (Blk d c) = 4) :
    ¬ IsMulCommutative ↥(embSU d c).range := by
  have hncSU4 : ¬ IsMulCommutative ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) := by
    rw [hcard4]
    exact not_isMulCommutative_statedSU_four
  intro hcomm
  apply hncSU4
  exact isMulCommutative_iff.2 fun x y =>
    (MonoidHom.ofInjective (embSU_injective d c)).injective (by
      rw [map_mul, map_mul]
      exact isMulCommutative_iff.1 hcomm _ _)

private theorem big_range_card (hcard4 : Fintype.card (Blk d c) = 4) :
    Nat.card ↥(embSU d c).range = 25920 := by
  have hcardSU : Nat.card ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) = 25920 := by
    rw [hcard4]
    exact card_statedSU_four
  rw [← Nat.card_congr (MonoidHom.ofInjective (embSU_injective d c)).toEquiv]
  exact hcardSU

private theorem big_range_inf (hda : d a ≠ c) :
    (embSU d c).range ⊓ Z6 = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzR, hzZ⟩
  rw [Subgroup.mem_bot]
  obtain ⟨A, hA⟩ := hzR
  obtain ⟨lam, hlam⟩ := mem_Z6_iff.1 hzZ
  have h1 : mM6 z a a = 1 := by
    rw [← hA, mM6_embSU, extMat_apply]
    rw [dif_neg (show ¬ (d a = c ∧ d a = c) from fun h => hda h.1)]
    exact Matrix.one_apply_eq a
  have hzmat : mM6 z = ((Matrix.GeneralLinearGroup.scalar (Fin 6) lam : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) := by
    change ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
    rw [hlam]
  have h2 : mM6 z a a = (lam : F4) := by
    rw [hzmat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq]
  have hlam1 : (lam : F4) = 1 := by rw [← h2, h1]
  apply Subtype.ext
  rw [hlam, show lam = 1 from Units.ext hlam1, map_one]
  rfl

private theorem big_fusion (hD : mM6 Dm = Matrix.diagonal d)
    (hc3 : c ^ 3 = 1) (hsum_d : ∑ i, d i = c) :
    ∀ g : M6, ∀ z ∈ Z6, g * Dm * g⁻¹ = Dm * z → g ∈ CenD (Dm : GL (Fin 6) F4) := by
  have htraceD : (mM6 Dm).trace = c := by
    rw [hD, Matrix.trace_diagonal]
    exact hsum_d
  intro g z hzZ hgs
  obtain ⟨lam, hlam⟩ := mem_Z6_iff.1 hzZ
  have htr : (mM6 (g * Dm * g⁻¹)).trace = (mM6 (Dm * z)).trace := by rw [hgs]
  have hL : (mM6 (g * Dm * g⁻¹)).trace = (mM6 Dm).trace := by
    change ((((g : GL (Fin 6) F4) * (Dm : GL (Fin 6) F4) *
      (g : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).trace = _
    exact trace_conj _ _
  have hR : (mM6 (Dm * z)).trace = (lam : F4) * (mM6 Dm).trace := by
    change ((((Dm : GL (Fin 6) F4) * (z : GL (Fin 6) F4) : GL (Fin 6) F4)) :
      Matrix (Fin 6) (Fin 6) F4).trace = _
    rw [Units.val_mul, hlam, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact trace_mul_diagonal_const (mM6 Dm) (lam : F4)
  rw [hL, hR, htraceD] at htr
  have hc0 : c ≠ 0 := cube_root_ne_zero hc3
  have hlam1 : (lam : F4) = 1 := by
    have h0 : ((lam : F4) - 1) * c = 0 := by
      rw [sub_mul, one_mul, show (lam : F4) * c = c from htr.symm, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hc0)
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [hlam, show lam = 1 from Units.ext hlam1, map_one]
    rfl
  rw [mem_CenD]
  have hcomm : g * Dm = Dm * g := by
    have h := congrArg (fun x : M6 => x * g) hgs
    rw [hz1, mul_one] at h
    simpa [mul_assoc] using h
  simpa using congrArg (fun x : M6 => (x : GL (Fin 6) F4)) hcomm


private theorem big_generation (hD : mM6 Dm = Matrix.diagonal d) (hd0 : ∀ i, d i ≠ 0)
    (hcube : ∀ i, d i ^ 3 = 1) (hda : d a ≠ c) (hdb : d b ≠ c) (hdab : d a ≠ d b)
    (hSab : Finset.univ.filter (fun i : Fin 6 => d i ≠ c) = {a, b}) :
    ∀ g ∈ CenD (Dm : GL (Fin 6) F4), ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ (embSU d c).range,
      g = Dm ^ n * z * r := by
  have hcover : ∀ k, d k ≠ c → k = a ∨ k = b := by
    intro k hk
    have hmem : k ∈ Finset.univ.filter (fun i : Fin 6 => d i ≠ c) := by simpa using hk
    rw [hSab] at hmem
    simpa using hmem
  have hsingle_a : ∀ k, d k = d a → k = a := by
    intro k hk
    have hkc : d k ≠ c := by rw [hk]; exact hda
    rcases hcover k hkc with h | h
    · exact h
    · exfalso
      exact hdab (by rw [← hk, h])
  have hsingle_b : ∀ k, d k = d b → k = b := by
    intro k hk
    have hkc : d k ≠ c := by rw [hk]; exact hdb
    rcases hcover k hkc with h | h
    · exfalso
      exact hdab (by rw [← hk, h])
    · exact h
  intro g hgC
  set M : Matrix (Fin 6) (Fin 6) F4 := mM6 g with hMdef
  have hMoff : ∀ i j, d i ≠ d j → M i j = 0 := fun i j hij => CenD_zero hD ⟨g, hgC⟩ hij
  have hx3 : (M a a) ^ 3 = 1 := CenD_single_cube hD ⟨g, hgC⟩ hsingle_a
  have hy3 : (M b b) ^ 3 = 1 := CenD_single_cube hD ⟨g, hgC⟩ hsingle_b
  obtain ⟨n, m, hnx, hny⟩ := exists_pow_mul (d a) (d b) F4.ω (M a a) (M b b)
    (hcube a) (hcube b) omega_cube omega_ne_one hdab hx3 hy3
  have hωm3 : (F4.ω ^ (m : ℕ)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_cube, one_pow]
  have hωm0 : F4.ω ^ (m : ℕ) ≠ 0 := cube_root_ne_zero hωm3
  let ωU : F4ˣ := Units.mk0 F4.ω (cube_root_ne_zero omega_cube)
  have hval : ((ωU ^ (m : ℕ) : F4ˣ) : F4) = F4.ω ^ (m : ℕ) := by
    simp [ωU, Units.val_pow_eq_pow_val]
  have hzmem : Matrix.GeneralLinearGroup.scalar (Fin 6) (ωU ^ (m : ℕ)) ∈
      StatedSU 6 (2 ^ 1) F4 := by
    apply scalar_mem_unitarySU (h := hF4) (n := 6) (by norm_num)
    · rw [UnitaryFieldData.norm_eq_pow]
      rw [hval, show 2 ^ 1 + 1 = 3 from rfl]
      exact hωm3
    · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
      have h3 : (ωU ^ (m : ℕ)) ^ 3 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, hval]
        exact hωm3
      rw [h3, one_pow]
  let z : M6 := ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) (ωU ^ (m : ℕ)), hzmem⟩
  have hzZ : z ∈ Z6 := by
    rw [mem_Z6_iff]
    exact ⟨ωU ^ (m : ℕ), rfl⟩
  have hzmatrix : mM6 z = Matrix.diagonal (fun _ : Fin 6 => F4.ω ^ (m : ℕ)) := by
    change ((Matrix.GeneralLinearGroup.scalar (Fin 6) (ωU ^ (m : ℕ)) : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) = _
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hfun : (fun _ : Fin 6 => ((ωU ^ (m : ℕ) : F4ˣ) : F4)) =
        (fun _ : Fin 6 => F4.ω ^ (m : ℕ)) := funext (fun _ => hval)
    rw [hfun]
  let vfun : Fin 6 → F4 := fun i => d i ^ (n : ℕ) * F4.ω ^ (m : ℕ)
  have hvfun0 : ∀ i, vfun i ≠ 0 := fun i =>
    mul_ne_zero (pow_ne_zero _ (hd0 i)) hωm0
  have hpow : mM6 (Dm ^ (n : ℕ)) = Matrix.diagonal (fun i => d i ^ (n : ℕ)) := by
    have h : mM6 (Dm ^ (n : ℕ)) = (mM6 Dm) ^ (n : ℕ) := by
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg (fun x : GL (Fin 6) F4 => ((x : Matrix (Fin 6) (Fin 6) F4)))
        (Subgroup.coe_pow _ Dm (n : ℕ))
    rw [h, hD, Matrix.diagonal_pow]
    rfl
  have hV : mM6 (Dm ^ (n : ℕ) * z) = Matrix.diagonal vfun := by
    rw [mM6_mul, hpow, hzmatrix, Matrix.diagonal_mul_diagonal]
  have hVinv : mM6 ((Dm ^ (n : ℕ) * z)⁻¹) = Matrix.diagonal (fun i => (vfun i)⁻¹) := by
    rw [mM6_inv, hV, diagonal_inv_eq vfun hvfun0]
  have hDmC : Dm ∈ CenD (Dm : GL (Fin 6) F4) := mem_CenD.2 rfl
  have hzCen : z ∈ CenD (Dm : GL (Fin 6) F4) := by
    obtain ⟨lam, hlam⟩ := mem_Z6_iff.1 hzZ
    rw [mem_CenD, hlam]
    exact ((commute_scalar lam (Dm : GL (Fin 6) F4)).eq).symm
  let r : M6 := (Dm ^ (n : ℕ) * z)⁻¹ * g
  have hrC : r ∈ CenD (Dm : GL (Fin 6) F4) :=
    mul_mem (inv_mem (mul_mem (pow_mem hDmC (n : ℕ)) hzCen)) hgC
  have hrM : mM6 r = Matrix.diagonal (fun i => (vfun i)⁻¹) * M := by
    change mM6 ((Dm ^ (n : ℕ) * z)⁻¹ * g) = _
    rw [mM6_mul, hVinv]
  have hentry : ∀ i j, mM6 r i j = (vfun i)⁻¹ * M i j := by
    intro i j
    rw [hrM, Matrix.diagonal_mul]
  have hblk : mM6 r = extMat d c (blkM d c (mM6 r)) := by
    symm
    apply extMat_blkM
    intro i j hij
    rw [hentry]
    by_cases hEq : i = j
    · subst hEq
      have hdi : d i ≠ c := fun h => hij ⟨h, h⟩
      rcases hcover i hdi with hia | hib
      · rw [Matrix.one_apply_eq]
        have hv : vfun i = M i i := by rw [hia]; exact hnx
        have hx3' : (M i i) ^ 3 = 1 := by rw [hia]; exact hx3
        rw [hv]
        exact inv_mul_cancel₀ (cube_root_ne_zero hx3')
      · rw [Matrix.one_apply_eq]
        have hv : vfun i = M i i := by rw [hib]; exact hny
        have hy3' : (M i i) ^ 3 = 1 := by rw [hib]; exact hy3
        rw [hv]
        exact inv_mul_cancel₀ (cube_root_ne_zero hy3')
    · rw [Matrix.one_apply_ne hEq]
      have hdij : d i ≠ d j := by
        intro heq
        have hdi : d i ≠ c := fun h => hij ⟨h, heq ▸ h⟩
        have hdj : d j ≠ c := fun h => hij ⟨heq ▸ h, h⟩
        rcases hcover i hdi with hia | hib <;> rcases hcover j hdj with hja | hjb
        · exact hEq (hia.trans hja.symm)
        · exact hdab (by rw [← hia, ← hjb]; exact heq)
        · exact hdab (by rw [← hib, ← hja]; exact heq.symm)
        · exact hEq (hib.trans hjb.symm)
      rw [hMoff i j hdij, mul_zero]
  let eW := Fintype.equivFin (Blk d c)
  let Ab : GL (Blk d c) F4 := blkHom hD c ⟨r, hrC⟩
  have hAbval : ((Ab : GL (Blk d c) F4) : Matrix (Blk d c) (Blk d c) F4) =
      blkM d c (mM6 r) := blkHom_val hD c ⟨r, hrC⟩
  have hA4mem : reindexGL eW Ab ∈ StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4 := by
    apply mem_statedSU_of
    · rw [reindexGL_val, Matrix.det_reindex_self, hAbval]
      have hdetr : (mM6 r).det = 1 := det_one_of_mem_statedSU (by norm_num) _ r.2
      rw [hblk, det_extMat] at hdetr
      exact hdetr
    · rw [reindexGL_val, hAbval]
      have hU : ((blkM d c (mM6 r)).map bar).transpose * blkM d c (mM6 r) = 1 :=
        blkM_unitary d c (fun i j hij => by rw [hentry, hMoff i j hij, mul_zero])
          (M6_unitary r)
      exact reindex_unitary eW (blkM d c (mM6 r)) hU
  have hrEq : r = embSU d c ⟨reindexGL eW Ab, hA4mem⟩ := by
    apply Subtype.ext
    apply Units.ext
    change mM6 r = extMat d c ((Matrix.reindex eW.symm eW.symm)
      (((reindexGL eW Ab : GL (Fin (Fintype.card (Blk d c))) F4) :
        Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4)))
    rw [reindexGL_val]
    have hround : (Matrix.reindex eW.symm eW.symm) ((Matrix.reindex eW eW)
        ((Ab : GL (Blk d c) F4) : Matrix (Blk d c) (Blk d c) F4)) =
        ((Ab : GL (Blk d c) F4) : Matrix (Blk d c) (Blk d c) F4) := by
      rw [← Matrix.reindex_symm]
      exact (Matrix.reindex eW eW).symm_apply_apply _
    rw [hround, hAbval]
    exact hblk
  refine ⟨(n : ℕ), z, hzZ, embSU d c ⟨reindexGL eW Ab, hA4mem⟩,
    ⟨⟨reindexGL eW Ab, hA4mem⟩, rfl⟩, ?_⟩
  have hgr : g = Dm ^ (n : ℕ) * z * r := by
    change g = Dm ^ (n : ℕ) * z * ((Dm ^ (n : ℕ) * z)⁻¹ * g)
    group
  rw [hgr, hrEq]

private theorem big_notin (hD : mM6 Dm = Matrix.diagonal d) (hda : d a ≠ c) (hdb : d b ≠ c)
    (hdab : d a ≠ d b) :
    ∀ z ∈ Z6, ∀ r ∈ (embSU d c).range, Dm ≠ z * r := by
  intro z hzZ r hrR heq
  obtain ⟨lam, hlam⟩ := mem_Z6_iff.1 hzZ
  obtain ⟨A, hA⟩ := hrR
  have hDa : mM6 Dm a a = d a := by rw [hD, Matrix.diagonal_apply_eq]
  have hDb : mM6 Dm b b = d b := by rw [hD, Matrix.diagonal_apply_eq]
  have hRa : mM6 (z * r) a a = (lam : F4) := by
    rw [mM6_mul, ← hA, mM6_embSU]
    have hzmat : mM6 z = ((Matrix.GeneralLinearGroup.scalar (Fin 6) lam : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) := by
      change ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
      rw [hlam]
    rw [hzmat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_mul, extMat_apply]
    rw [dif_neg (show ¬ (d a = c ∧ d a = c) from fun h => hda h.1)]
    rw [Matrix.one_apply_eq, mul_one]
  have hRb : mM6 (z * r) b b = (lam : F4) := by
    rw [mM6_mul, ← hA, mM6_embSU]
    have hzmat : mM6 z = ((Matrix.GeneralLinearGroup.scalar (Fin 6) lam : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) := by
      change ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
      rw [hlam]
    rw [hzmat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_mul, extMat_apply]
    rw [dif_neg (show ¬ (d b = c ∧ d b = c) from fun h => hdb h.1)]
    rw [Matrix.one_apply_eq, mul_one]
  have e1 : d a = (lam : F4) := by rw [← hDa, heq, hRa]
  have e2 : d b = (lam : F4) := by rw [← hDb, heq, hRb]
  exact hdab (e1.trans e2.symm)

end BigCase

private theorem cubeFact_diag_big (Dm : M6) (d : Fin 6 → F4) (c : F4) (a b : Fin 6)
    (hD : mM6 Dm = Matrix.diagonal d) (hd0 : ∀ i, d i ≠ 0)
    (hcube : ∀ i, d i ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hcard4 : Fintype.card (Blk d c) = 4)
    (hab : a ≠ b) (hda : d a ≠ c) (hdb : d b ≠ c) (hdab : d a ≠ d b)
    (hSab : Finset.univ.filter (fun i : Fin 6 => d i ≠ c) = {a, b})
    (hsum_d : ∑ i, d i = c) :
    ∃ R : Subgroup M6, R ≤ CenD (Dm : GL (Fin 6) F4) ∧ IsSimpleGroup ↥R ∧
      ¬ IsMulCommutative ↥R ∧ Nat.card ↥R = 25920 ∧ R ⊓ Z6 = ⊥ ∧
      (∀ g : M6, ∀ z ∈ Z6, g * Dm * g⁻¹ = Dm * z → g ∈ CenD (Dm : GL (Fin 6) F4)) ∧
      (∀ g ∈ CenD (Dm : GL (Fin 6) F4), ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ R,
        g = Dm ^ n * z * r) ∧
      (∀ z ∈ Z6, ∀ r ∈ R, Dm ≠ z * r) :=
  ⟨(embSU d c).range, big_range_le_CenD hD, big_range_simple hcard4,
    big_range_notcomm hcard4, big_range_card hcard4, big_range_inf hda,
    big_fusion hD hc3 hsum_d, big_generation hD hd0 hcube hda hdb hdab hSab,
    big_notin hD hda hdb hdab⟩



private theorem cubeFact_diag (Dm : M6) (d : Fin 6 → F4)
    (hD : mM6 Dm = Matrix.diagonal d) (hd0 : ∀ i, d i ≠ 0)
    (hdet : ∏ i, d i = 1) (hcube : ∀ i, d i ^ 3 = 1)
    (hns : ¬ ∃ c : F4ˣ, (Dm : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    (∀ J : Subgroup M6, J ≤ CenD (Dm : GL (Fin 6) F4) → ⁅J, J⁆ = J → J = ⊥) ∨
      ∃ R : Subgroup M6, R ≤ CenD (Dm : GL (Fin 6) F4) ∧ IsSimpleGroup ↥R ∧
        ¬ IsMulCommutative ↥R ∧ Nat.card ↥R = 25920 ∧ R ⊓ Z6 = ⊥ ∧
        (∀ g : M6, ∀ z ∈ Z6, g * Dm * g⁻¹ = Dm * z → g ∈ CenD (Dm : GL (Fin 6) F4)) ∧
        (∀ g ∈ CenD (Dm : GL (Fin 6) F4), ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ R,
          g = Dm ^ n * z * r) ∧
        (∀ z ∈ Z6, ∀ r ∈ R, Dm ≠ z * r) := by
  have hnc : ¬ ∀ i, d i = d 0 := by
    intro hconst
    apply hns
    refine ⟨Units.mk0 (d 0) (hd0 0), ?_⟩
    apply Units.ext
    show ((Dm : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) (hd0 0)) :
        GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
    rw [show ((Dm : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d from hD,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hconst i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  by_cases hbig : ∃ c : F4, 4 ≤ Fintype.card (Blk d c)
  · obtain ⟨c, hc4⟩ := hbig
    have hc5 : Fintype.card (Blk d c) ≤ 5 := card_blk_le_five d hnc c
    obtain ⟨hc3, hcard4, hsum_d, a, b, hab, hda, hdb, hdab, hSab⟩ :=
      big_structure hdet hcube c hc4 hc5
    exact Or.inr (cubeFact_diag_big Dm d c a b hD hd0 hcube hc3 hcard4 hab hda hdb hdab
      hSab hsum_d)
  · push Not at hbig
    exact Or.inl fun J hJ hperf =>
      eq_bot_of_perfect_of_small hD (fun c => by have := hbig c; omega) hJ hperf

private theorem transport_small (e : M6 ≃* M6) {Dm s : M6}
    (hmapCen_s : (CenD (s : GL (Fin 6) F4)).map e.symm.toMonoidHom =
      CenD (Dm : GL (Fin 6) F4))
    (hsmall : ∀ J : Subgroup M6, J ≤ CenD (Dm : GL (Fin 6) F4) → ⁅J, J⁆ = J → J = ⊥) :
    ∀ J : Subgroup M6, J ≤ CenD (s : GL (Fin 6) F4) → ⁅J, J⁆ = J → J = ⊥ := by
  intro J hJ hperf
  have hmap_le : J.map e.symm.toMonoidHom ≤ CenD (Dm : GL (Fin 6) F4) := by
    rw [← hmapCen_s]
    exact Subgroup.map_mono hJ
  have hperf' : ⁅J.map e.symm.toMonoidHom, J.map e.symm.toMonoidHom⁆ =
      J.map e.symm.toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have hbot := hsmall _ hmap_le hperf'
  rw [Subgroup.map_eq_bot_iff] at hbot
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 (hbot hx))

private theorem transport_big (e : M6 ≃* M6) {Dm s : M6}
    (hDm_s : e Dm = s)
    (hmapCen_D : (CenD (Dm : GL (Fin 6) F4)).map e.toMonoidHom =
      CenD (s : GL (Fin 6) F4))
    (hmapCen_s : (CenD (s : GL (Fin 6) F4)).map e.symm.toMonoidHom =
      CenD (Dm : GL (Fin 6) F4))
    (hZ : ∀ z : M6, z ∈ Z6 → e z ∈ Z6)
    (hZs : ∀ z : M6, z ∈ Z6 → e.symm z ∈ Z6)
    (R_D : Subgroup M6) (hRD : R_D ≤ CenD (Dm : GL (Fin 6) F4))
    (hsimple : IsSimpleGroup ↥R_D) (hnc : ¬ IsMulCommutative ↥R_D)
    (hcard : Nat.card ↥R_D = 25920) (hinf : R_D ⊓ Z6 = ⊥)
    (hfusion : ∀ g : M6, ∀ z ∈ Z6, g * Dm * g⁻¹ = Dm * z →
      g ∈ CenD (Dm : GL (Fin 6) F4))
    (hgen : ∀ g ∈ CenD (Dm : GL (Fin 6) F4), ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ R_D,
      g = Dm ^ n * z * r)
    (hnotin : ∀ z ∈ Z6, ∀ r ∈ R_D, Dm ≠ z * r) :
    ∃ R : Subgroup M6, R ≤ CenD (s : GL (Fin 6) F4) ∧ IsSimpleGroup ↥R ∧
      ¬ IsMulCommutative ↥R ∧ Nat.card ↥R = 25920 ∧ R ⊓ Z6 = ⊥ ∧
      (∀ g : M6, ∀ z ∈ Z6, g * s * g⁻¹ = s * z → g ∈ CenD (s : GL (Fin 6) F4)) ∧
      (∀ g ∈ CenD (s : GL (Fin 6) F4), ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ R,
        g = s ^ n * z * r) ∧
      (∀ z ∈ Z6, ∀ r ∈ R, s ≠ z * r) := by
  refine ⟨R_D.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmapCen_D]
    exact Subgroup.map_mono hRD
  · haveI := hsimple
    exact (Subgroup.equivMapOfInjective R_D e.toMonoidHom e.injective).symm.isSimpleGroup
  · intro hcomm
    apply hnc
    exact isMulCommutative_iff.2 fun x y =>
      (Subgroup.equivMapOfInjective R_D e.toMonoidHom e.injective).injective (by
        rw [map_mul, map_mul]
        exact isMulCommutative_iff.1 hcomm _ _)
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R_D e.toMonoidHom e.injective).toEquiv]
    exact hcard
  · rw [eq_bot_iff]
    rintro z ⟨hzR, hzZ⟩
    obtain ⟨z', hz'R, rfl⟩ := hzR
    have hz'Z : z' ∈ Z6 := by
      have h := hZs (e z') hzZ
      rwa [MulEquiv.symm_apply_apply] at h
    have hmem : z' ∈ R_D ⊓ Z6 := ⟨hz'R, hz'Z⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, hmem, map_one]
  · intro g z hzZ hgs
    have hz'Z : e.symm z ∈ Z6 := hZs z hzZ
    have hgs' : e.symm g * Dm * (e.symm g)⁻¹ = Dm * e.symm z := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hDm_s, hgs]
    have hmem := hfusion (e.symm g) (e.symm z) hz'Z hgs'
    have h1 : e (e.symm g) ∈ (CenD (Dm : GL (Fin 6) F4)).map e.toMonoidHom :=
      ⟨e.symm g, hmem, rfl⟩
    rw [hmapCen_D, MulEquiv.apply_symm_apply] at h1
    exact h1
  · intro g hgC
    have hg'C : e.symm g ∈ CenD (Dm : GL (Fin 6) F4) := by
      rw [← hmapCen_s]
      exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hgC
    obtain ⟨n, z', hz'Z, r', hr'R, hEq⟩ := hgen (e.symm g) hg'C
    refine ⟨n, e z', hZ z' hz'Z, e r', ⟨r', hr'R, rfl⟩, ?_⟩
    calc g = e (e.symm g) := (MulEquiv.apply_symm_apply e g).symm
      _ = e (Dm ^ n * z' * r') := by rw [hEq]
      _ = (e Dm) ^ n * e z' * e r' := by rw [map_mul, map_mul, map_pow]
      _ = s ^ n * e z' * e r' := by rw [hDm_s]
  · intro z hzZ r hrR hs
    have hz'Z : e.symm z ∈ Z6 := hZs z hzZ
    obtain ⟨r', hr'R, hrEq⟩ := hrR
    have h1 : e.symm s = e.symm z * e.symm r := by rw [hs, map_mul]
    have hDs : e.symm s = Dm := by rw [← hDm_s, MulEquiv.symm_apply_apply]
    have hr'symm : e.symm r = r' := by
      rw [← hrEq]
      exact MulEquiv.symm_apply_apply e r'
    exact hnotin (e.symm z) hz'Z r' hr'R (by rw [← hDs, h1, hr'symm])

theorem u6CubeFact_holds : U6CubeFact := by
  intro s hs3 hns
  have hBgram : (s : GL (Fin 6) F4) ∈ gramSU hF4 (idGram F4 6) := by
    rw [gramSU_idGram_six]
    exact s.2
  let B : primeFormUnitary hF4 (idGram F4 6) :=
    ⟨(s : GL (Fin 6) F4), ((mem_gramSU_iff_unitary hF4).1 hBgram).1⟩
  have hB3 : B ^ 3 = 1 := by
    apply Subtype.ext
    show (s : GL (Fin 6) F4) ^ 3 = (1 : GL (Fin 6) F4)
    simpa using congrArg (fun x : M6 => (x : GL (Fin 6) F4)) hs3
  obtain ⟨P, d, hd⟩ := exists_diag6 B hB3
  let Q : primeFormUnitary hF4 (idGram F4 6) := P⁻¹ * B * P
  have hQeq : (Q : GL (Fin 6) F4) = (P : GL (Fin 6) F4)⁻¹ * (B : GL (Fin 6) F4) *
      (P : GL (Fin 6) F4) := rfl
  have hdiag : ((Q : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hd
  have hQgram : (Q : GL (Fin 6) F4) ∈ gramSU hF4 (idGram F4 6) := by
    rw [hQeq]
    have h := conj_mem_gramSU hF4 (idGram F4 6) (A := (P : GL (Fin 6) F4)⁻¹)
      (g := (s : GL (Fin 6) F4)) (inv_mem P.2) hBgram
    simpa [inv_inv] using h
  have hQmem : (Q : GL (Fin 6) F4) ∈ StatedSU 6 (2 ^ 1) F4 := by
    rw [gramSU_idGram_six] at hQgram
    exact hQgram
  let Dm : M6 := ⟨(Q : GL (Fin 6) F4), hQmem⟩
  have hDm : mM6 Dm = Matrix.diagonal d := by
    show ((Q : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d
    exact hdiag
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    have hQinv : ((Q : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        (((Q : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := congrFun (congrFun hQinv i) i
    rw [hdiag, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h1
    exact zero_ne_one (α := F4) h1
  have hdetSU : ((Q : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 :=
    det_one_of_mem_statedSU (by norm_num) _ hQmem
  have hdet : ∏ i, d i = 1 := by
    rw [hdiag, Matrix.det_diagonal] at hdetSU
    exact hdetSU
  have hQ3 : (Q : GL (Fin 6) F4) ^ 3 = 1 := by
    rw [hQeq]
    have hB3gl : (B : GL (Fin 6) F4) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hB3
    have hconj : (P : GL (Fin 6) F4)⁻¹ * (B : GL (Fin 6) F4) * (P : GL (Fin 6) F4) =
        (MulAut.conj (P : GL (Fin 6) F4)⁻¹) (B : GL (Fin 6) F4) := by
      rw [MulAut.conj_apply]
      simp
    rw [hconj, ← map_pow, hB3gl, map_one]
  have hcube : ∀ i, d i ^ 3 = 1 := by
    have hdiag3 : (Matrix.diagonal d) ^ 3 = 1 := by
      rw [← hdiag, ← Units.val_pow_eq_pow_val, hQ3, Units.val_one]
    rw [Matrix.diagonal_pow] at hdiag3
    intro i
    have := congrFun (congrFun hdiag3 i) i
    simpa using this
  have hB_eq_s : (B : GL (Fin 6) F4) = (s : GL (Fin 6) F4) := rfl
  have hDm_eq : (Dm : GL (Fin 6) F4) = (P : GL (Fin 6) F4)⁻¹ * (s : GL (Fin 6) F4) *
      (P : GL (Fin 6) F4) := by
    rw [show (Dm : GL (Fin 6) F4) = (Q : GL (Fin 6) F4) from rfl, hQeq, hB_eq_s]
  have hPsP : (s : GL (Fin 6) F4) = (P : GL (Fin 6) F4) * (Dm : GL (Fin 6) F4) *
      (P : GL (Fin 6) F4)⁻¹ := by
    rw [hDm_eq]
    group
  have hnsD : ¬ ∃ cc : F4ˣ, (Dm : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) cc := by
    rintro ⟨cc, hcc⟩
    apply hns
    rw [mem_Z6_iff]
    refine ⟨cc, ?_⟩
    rw [hPsP, hcc, (commute_scalar cc (P : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  let e := conjM6 P
  have hmapCen_s : (CenD (s : GL (Fin 6) F4)).map e.symm.toMonoidHom =
      CenD (Dm : GL (Fin 6) F4) := by
    have h := map_CenD_conj (Q := P⁻¹) (B := (s : GL (Fin 6) F4))
    rw [conjM6_symm, h]
    congr 1
  have hmapCen_D : (CenD (Dm : GL (Fin 6) F4)).map e.toMonoidHom =
      CenD (s : GL (Fin 6) F4) := by
    have h := map_CenD_conj (Q := P) (B := (Dm : GL (Fin 6) F4))
    rw [h]
    congr 1
    rw [hDm_eq]
    group
  have hDm_s : e Dm = s := by
    apply Subtype.ext
    show ((P : GL (Fin 6) F4) * (Dm : GL (Fin 6) F4) * (P : GL (Fin 6) F4)⁻¹ :
      GL (Fin 6) F4) = (s : GL (Fin 6) F4)
    rw [hDm_eq]
    group
  have hZ : ∀ z : M6, z ∈ Z6 → e z ∈ Z6 := fun z hz => conjM6_mem_Z6 P hz
  have hZs : ∀ z : M6, z ∈ Z6 → e.symm z ∈ Z6 := by
    intro z hz
    have h := conjM6_mem_Z6 P⁻¹ hz
    rwa [← conjM6_symm] at h
  rcases cubeFact_diag Dm d hDm hd0 hdet hcube hnsD with hsmall | hbig
  · left
    exact transport_small e hmapCen_s hsmall
  · right
    obtain ⟨R_D, hRD, hsimple, hnc, hcard, hinf, hfusion, hgen, hnotin⟩ := hbig
    exact transport_big e hDm_s hmapCen_D hmapCen_s hZ hZs R_D hRD hsimple hnc hcard hinf
      hfusion hgen hnotin

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
