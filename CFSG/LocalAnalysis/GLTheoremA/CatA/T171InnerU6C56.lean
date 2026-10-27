module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Nine
import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
import all CFSG.Fischer.F4
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped BigOperators commutatorElement

private theorem f4_cube_eq_one {x : F4} (hx : x ≠ 0) : x ^ 3 = 1 := by
  simpa using pow_three_of_units (Units.mk0 x hx)

private theorem f4_mul_three_eq_one {x y z : F4} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hz : z ^ 3 = 1) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : x * y * z = 1 := by
  revert x y z
  decide +kernel

private theorem transpGL_aux (i j : Fin 6) :
    (Equiv.swap i j).permMatrix F4 * (Equiv.swap i j).permMatrix F4 = 1 := by
  have h := Matrix.permMatrix_mul (n := Fin 6) (R := F4)
    (σ := Equiv.swap i j) (τ := Equiv.swap i j)
  rw [Equiv.swap_mul_self, Matrix.permMatrix_one] at h
  exact h.symm

private def transpGL (i j : Fin 6) : GL (Fin 6) F4 :=
  ⟨(Equiv.swap i j).permMatrix F4, (Equiv.swap i j).permMatrix F4,
    transpGL_aux i j, transpGL_aux i j⟩

private theorem transpGL_val (i j : Fin 6) :
    ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (Equiv.swap i j).permMatrix F4 := rfl

private theorem transpGL_mul_self (i j : Fin 6) : transpGL i j * transpGL i j = 1 := by
  apply Units.ext
  show ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1
  rw [transpGL_val]
  exact transpGL_aux i j

private theorem transpGL_apply (i j : Fin 6) (a b : Fin 6) :
    ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) a b =
      if Equiv.swap i j a = b then 1 else 0 := by
  rw [transpGL_val]
  exact CFSG.RankThree.Classical.permMatrix_apply' (Equiv.swap i j) a b

private theorem transpGL_mem_SU (i j : Fin 6) (hij : i ≠ j) :
    (transpGL i j : GL (Fin 6) F4) ∈ StatedSU 6 (2 ^ 1) F4 := by
  rw [mem_unitarySU_iff hF4]
  constructor
  · rw [transpGL_val, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
    simp [CharTwo.neg_eq]
  · have hbar : ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).map hF4.bar =
        ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
      ext a b
      rw [Matrix.map_apply, transpGL_apply]
      split_ifs <;> simp
    rw [hbar, transpGL_val, Matrix.transpose_permMatrix, Equiv.swap_inv,
      ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

private theorem transpGL_not_scalar (i j : Fin 6) (hij : i ≠ j) :
    ¬ ∃ c : F4ˣ, (transpGL i j : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) i j) hc
  rw [transpGL_apply, Equiv.swap_apply_left, if_pos rfl,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij] at h
  exact one_ne_zero h

private theorem diagonal_mul_transpGL (d : Fin 6 → F4) {i j : Fin 6} (hij : i ≠ j)
    (hd : d i = d j) :
    Matrix.diagonal d * ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal d := by
  have hda : ∀ a : Fin 6, d (Equiv.swap i j a) = d a := by
    intro a
    by_cases hai : a = i
    · rw [hai, Equiv.swap_apply_left, hd]
    · by_cases haj : a = j
      · rw [haj, Equiv.swap_apply_right]
        exact hd
      · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, transpGL_apply]
  by_cases h : Equiv.swap i j a = b
  · rw [if_pos h, mul_one, one_mul, ← h, hda]
  · rw [if_neg h, mul_zero, zero_mul]

private theorem transpGL_comm_of_blocks {d : Fin 6 → F4} {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    {i j : Fin 6} (hij : i ≠ j) (hd : d i = d j) {y : M6} (hy : y ∈ CenD D)
    (hyid : ∀ a b : Fin 6, d a = d i → d b = d i → mM6 y a b = if a = b then 1 else 0)
    (hout : ∀ k : Fin 6, k ≠ i → k ≠ j → d k ≠ d i) :
    mM6 y * ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * mM6 y := by
  have hswap : ∀ k : Fin 6, Equiv.swap i j (Equiv.swap i j k) = k := by
    intro k
    rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply]
  have hswapd : ∀ k : Fin 6, d (Equiv.swap i j k) = d k := by
    intro k
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left, hd]
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right]
        exact hd
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hL : ∀ a b : Fin 6, (mM6 y * ((transpGL i j : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4)) a b = mM6 y a (Equiv.swap i j b) := by
    intro a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap i j b)]
    · rw [transpGL_apply, if_pos (hswap b), mul_one]
    · intro k _ hk
      rw [transpGL_apply]
      rw [if_neg, mul_zero]
      intro hkb
      exact hk (by rw [← hkb, hswap])
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  have hR : ∀ a b : Fin 6, (((transpGL i j : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) * mM6 y) a b = mM6 y (Equiv.swap i j a) b := by
    intro a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap i j a)]
    · rw [transpGL_apply, if_pos rfl, one_mul]
    · intro k _ hk
      rw [transpGL_apply]
      rw [if_neg, zero_mul]
      intro hka
      exact hk hka.symm
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  ext a b
  rw [hL, hR]
  have hzero : ∀ p q : Fin 6, d p ≠ d q → mM6 y p q = 0 :=
    fun p q hpq => CenD_zero hD ⟨y, hy⟩ hpq
  by_cases hda : d a = d i
  · by_cases hdb : d b = d i
    · rw [hyid a (Equiv.swap i j b) hda (by rw [hswapd b]; exact hdb),
        hyid (Equiv.swap i j a) b (by rw [hswapd a]; exact hda) hdb]
      have hiff : (a = Equiv.swap i j b) ↔ (Equiv.swap i j a = b) := by
        constructor
        · intro h; rw [h, hswap]
        · intro h; rw [← h, hswap]
      by_cases h : a = Equiv.swap i j b
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]
    · rw [hzero a (Equiv.swap i j b) (by rw [hswapd b, hda]; exact fun h => hdb h.symm),
        hzero (Equiv.swap i j a) b (by rw [hswapd a, hda]; exact fun h => hdb h.symm)]
  · by_cases hdb : d b = d i
    · rw [hzero a (Equiv.swap i j b) (by rw [hswapd b, hdb]; exact hda),
        hzero (Equiv.swap i j a) b (by rw [hswapd a, hdb]; exact hda)]
    · have hai : a ≠ i := fun h => hda (by rw [h])
      have haj : a ≠ j := fun h => hda (by rw [h]; exact hd.symm)
      have hbi : b ≠ i := fun h => hdb (by rw [h])
      have hbj : b ≠ j := fun h => hdb (by rw [h]; exact hd.symm)
      rw [Equiv.swap_apply_of_ne_of_ne hai haj, Equiv.swap_apply_of_ne_of_ne hbi hbj]

private theorem eq_update_of_card_blk_eq_five (d : Fin 6 → F4) (c : F4)
    (h5 : Fintype.card (Blk d c) = 5) :
    ∃ (i : Fin 6) (b : F4), b ≠ c ∧ d = Function.update (fun _ => c) i b := by
  have hcompl : Fintype.card {k : Fin 6 // ¬ d k = c} = 1 := by
    have h := Fintype.card_subtype_compl (fun k : Fin 6 => d k = c)
    rw [Fintype.card_fin] at h
    have h5' : Fintype.card {k : Fin 6 // d k = c} = 5 := h5
    rw [h5'] at h
    omega
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcompl
  refine ⟨a.1, d a.1, a.2, ?_⟩
  funext k
  by_cases hk : k = a.1
  · rw [hk, Function.update_self]
  · rw [Function.update_of_ne hk]
    by_contra hkc
    have hmem : (⟨k, hkc⟩ : {k : Fin 6 // ¬ d k = c}) = a := ha ⟨k, hkc⟩
    exact hk (congrArg Subtype.val hmem)

private theorem exists_two_eq_or_prod_eq_one (d : Fin 6 → F4) (c : F4)
    (hcube : ∀ k, d k ^ 3 = 1) (h4 : Fintype.card (Blk d c) = 4) :
    (∃ i j : Fin 6, i ≠ j ∧ d i = d j ∧ d i ≠ c) ∨ (∏ k : Fin 6, d k = 1) := by
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Fintype.card_pos_iff.mp (by rw [h4]; norm_num)
    rw [← hk]
    exact hcube k
  have h4' : Fintype.card {k : Fin 6 // d k = c} = 4 := h4
  have hTcard : Fintype.card {k : Fin 6 // ¬ d k = c} = 2 := by
    have h := Fintype.card_subtype_compl (fun k : Fin 6 => d k = c)
    rw [Fintype.card_fin, h4'] at h
    omega
  have hcard' : (Finset.univ.filter (fun k : Fin 6 => d k = c)).card = 4 := by
    rw [← Fintype.card_subtype (fun k : Fin 6 => d k = c)]
    exact h4'
  have hTcard' : (Finset.univ.filter (fun k : Fin 6 => ¬ d k = c)).card = 2 := by
    rw [← Fintype.card_subtype (fun k : Fin 6 => ¬ d k = c)]
    exact hTcard
  obtain ⟨k0⟩ := Fintype.card_pos_iff.mp
    (by rw [hTcard]; norm_num : 0 < Fintype.card {k : Fin 6 // ¬ d k = c})
  obtain ⟨k1, hk1⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hTcard]; norm_num) k0
  have hij : k0.1 ≠ k1.1 := fun h => hk1 (Subtype.ext h.symm)
  by_cases heq : d k0.1 = d k1.1
  · exact Or.inl ⟨k0.1, k1.1, hij, heq, k0.2⟩
  · refine Or.inr ?_
    have hTset : (Finset.univ.filter (fun k : Fin 6 => ¬ d k = c)) = {k0.1, k1.1} := by
      have hsub : ({k0.1, k1.1} : Finset (Fin 6)) ⊆
          Finset.univ.filter (fun k : Fin 6 => ¬ d k = c) := by
        intro k hk
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ k, ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact k0.2
        · exact k1.2
      have hle : (Finset.univ.filter (fun k : Fin 6 => ¬ d k = c)).card ≤
          ({k0.1, k1.1} : Finset (Fin 6)).card := by
        rw [Finset.card_pair hij, hTcard']
      exact (Finset.eq_of_subset_of_card_le hsub hle).symm
    have hsplit : (∏ k : Fin 6, d k) =
        (∏ k ∈ Finset.univ.filter (fun k : Fin 6 => d k = c), d k) *
        (∏ k ∈ Finset.univ.filter (fun k : Fin 6 => ¬ d k = c), d k) :=
      (Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
        (p := fun k : Fin 6 => d k = c) (f := d)).symm
    have h1 : (∏ k ∈ Finset.univ.filter (fun k : Fin 6 => d k = c), d k) = c ^ 4 := by
      rw [Finset.prod_congr rfl (fun k hk => (Finset.mem_filter.mp hk).2)]
      rw [Finset.prod_const, hcard']
    have h2 : (∏ k ∈ Finset.univ.filter (fun k : Fin 6 => ¬ d k = c), d k) =
        d k0.1 * d k1.1 := by
      rw [hTset]
      exact Finset.prod_pair hij
    rw [hsplit, h1, h2]
    have hc4 : c ^ 4 = c := by
      calc c ^ 4 = c ^ 3 * c := by ring
        _ = 1 * c := by rw [hc3]
        _ = c := one_mul c
    rw [hc4, ← mul_assoc]
    exact f4_mul_three_eq_one hc3 (hcube k0.1) (hcube k1.1) (fun h => k0.2 h.symm)
      (fun h => k1.2 h.symm) heq

theorem exists_perfect_lift_CenD (ĝ : Gu) {J : Subgroup S6}
    (hJle : J ≤ fixSubgroup (Psi0 ĝ)) (hJperf : ⁅J, J⁆ = J) :
    ∃ J' : Subgroup M6, J' ≤ CenD (ĝ : GL (Fin 6) F4) ∧
      Group.IsPerfect ↥J' ∧ J'.map pi6 = J := by
  classical
  have hαβ : ∀ k : M6, pi6 (conjM6 ĝ k) = Psi0 ĝ (pi6 k) := by
    intro k
    have h : Psi0 ĝ (QuotientGroup.mk k) = QuotientGroup.mk (conjM6 ĝ k) :=
      Psi0_mk ĝ k (conjM6 ĝ k) (conjM6_apply ĝ k)
    show QuotientGroup.mk (conjM6 ĝ k) = Psi0 ĝ (QuotientGroup.mk k)
    exact h.symm
  have hJimg : J ≤ (CenD (ĝ : GL (Fin 6) F4)).map pi6 := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.le_map_fixSubgroup_of_perfect
      pi6 ker_pi6_le_center (conjM6 ĝ) (Psi0 ĝ) hαβ
      (QuotientGroup.mk_surjective) hJle hJperf
    rwa [fixSubgroup_conjM6] at h
  by_cases hJbot : J = ⊥
  · exact ⟨⊥, bot_le, Subgroup.isPerfect_iff.mpr (by simp), by simp [hJbot]⟩
  · have hJnt : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 hJbot
    let Psub : Subgroup M6 := CenD (ĝ : GL (Fin 6) F4) ⊓ J.comap pi6
    let φ : ↥Psub →* ↥J := (pi6.comp Psub.subtype).codRestrict J (fun p => p.2.2)
    have hφ : Function.Surjective φ := by
      intro k
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp (hJimg k.2)
      refine ⟨⟨x, ⟨hx, ?_⟩⟩, Subtype.ext hxπ⟩
      show pi6 x ∈ J
      rw [hxπ]
      exact k.2
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
    obtain ⟨K', hK'map, hK'perf, -⟩ := i7_exists_perfect_cover φ hφ
    refine ⟨K'.map Psub.subtype, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.2.1
    · haveI : Group.IsPerfect ↥K' := hK'perf
      exact Group.IsPerfect.map (H := K') Psub.subtype
    · apply le_antisymm
      · intro x hx
        obtain ⟨y, hyJ, hyx⟩ := Subgroup.mem_map.mp hx
        obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hyJ
        rw [← hyx]
        exact z.2.2
      · intro x hx
        have hmem : (⟨x, hx⟩ : ↥J) ∈ K'.map φ := by
          rw [hK'map]
          exact Subgroup.mem_top _
        obtain ⟨z, hzK', hz⟩ := Subgroup.mem_map.mp hmem
        exact Subgroup.mem_map.mpr
          ⟨Psub.subtype z, Subgroup.mem_map.mpr ⟨z, hzK', rfl⟩, congrArg Subtype.val hz⟩

theorem pat4OfSmall_holds : Pat4OfSmall := by
  intro g J hg3 hg1 hnPR hJle hJperf h5
  obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk_surjective (s := ZG) g
  have hJle' : J ≤ fixSubgroup (Psi0 ĝ) := by
    rw [← hĝ, Psi_mk] at hJle
    exact hJle
  obtain ⟨J', hJ'le, hJ'perf, hJ'map⟩ := exists_perfect_lift_CenD ĝ hJle' hJperf
  have hmem : ĝ ^ 3 ∈ ZG := by
    refine (QuotientGroup.eq_one_iff (ĝ ^ 3)).mp ?_
    show ((QuotientGroup.mk' ZG) (ĝ ^ 3) : PGU6) = 1
    rw [map_pow, show ((QuotientGroup.mk' ZG) ĝ : PGU6) = g from hĝ, hg3]
  obtain ⟨c, hc⟩ := mem_ZG.1 hmem
  have hcube : (ĝ : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← Subgroup.coe_pow]
    exact hc.symm
  by_cases hc1 : c = 1
  · have hĝ3 : ĝ ^ 3 = 1 := by
      apply Subtype.ext
      show ((ĝ ^ 3 : Gu) : GL (Fin 6) F4) = ((1 : Gu) : GL (Fin 6) F4)
      rw [Subgroup.coe_pow, hcube, hc1, map_one, Subgroup.coe_one]
    obtain ⟨P, d, hPd⟩ := exists_diag6 ĝ hĝ3
    set D : GL (Fin 6) F4 := ((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) with hDdef
    have hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hPd
    have hDeq : D = (P : GL (Fin 6) F4)⁻¹ * (ĝ : GL (Fin 6) F4) * (P : GL (Fin 6) F4) := rfl
    have hĝ_eq : (ĝ : GL (Fin 6) F4) =
        (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ := by
      rw [hDeq]
      group
    have hĝns : ¬ ∃ c' : F4ˣ, (ĝ : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c' := by
      rintro ⟨c', hc'⟩
      exact hg1 (by rw [← hĝ]; exact (QuotientGroup.eq_one_iff ĝ).mpr (mem_ZG.2 ⟨c', hc'.symm⟩))
    have hdetD : (D : Matrix (Fin 6) (Fin 6) F4).det ≠ 0 := by
      have h := (Matrix.GeneralLinearGroup.det D).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
    have hd0 : d 0 ≠ 0 := by
      have hprod : (∏ i : Fin 6, d i) ≠ 0 := by
        rw [← Matrix.det_diagonal]
        rwa [← hD]
      exact Finset.prod_ne_zero_iff.mp hprod 0 (Finset.mem_univ 0)
    have hnc : ¬ ∀ i, d i = d 0 := by
      intro hconst
      apply hĝns
      have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) hd0) := by
        apply Units.ext
        rw [hD, Matrix.GeneralLinearGroup.coe_scalar]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hconst i]
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      refine ⟨Units.mk0 (d 0) hd0, ?_⟩
      rw [hĝ_eq, hDs, (commute_scalar (Units.mk0 (d 0) hd0) (P : GL (Fin 6) F4)).eq,
        mul_inv_cancel_right]
    have hbig : ∃ c₀ : F4, 4 ≤ Fintype.card (Blk d c₀) := by
      by_contra h
      push Not at h
      have hcnt : ∀ c₀ : F4, Fintype.card (Blk d c₀) ≤ 3 := fun c₀ => by
        have := h c₀
        omega
      have hJ''le : J'.map (conjM6 P⁻¹).toMonoidHom ≤ CenD D := by
        have hmap := map_CenD_conj P⁻¹ (ĝ : GL (Fin 6) F4)
        have hR : ((P⁻¹ : Gu) : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4) *
            (((P⁻¹ : Gu) : GL (Fin 6) F4))⁻¹ = D := by
          rw [hDdef]
          simp
        rw [← hR, ← hmap]
        exact Subgroup.map_mono hJ'le
      haveI : Group.IsPerfect ↥J' := hJ'perf
      have hperf'' : ⁅J'.map (conjM6 P⁻¹).toMonoidHom,
          J'.map (conjM6 P⁻¹).toMonoidHom⁆ = J'.map (conjM6 P⁻¹).toMonoidHom :=
        Subgroup.isPerfect_iff.mp (Group.IsPerfect.map (H := J') (conjM6 P⁻¹).toMonoidHom)
      have hbot : J'.map (conjM6 P⁻¹).toMonoidHom = ⊥ :=
        eq_bot_of_perfect_of_small hD hcnt hJ''le hperf''
      have hJ'bot : J' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective J' (conjM6 P⁻¹).injective).mp hbot
      have hJbot : J = ⊥ := by rw [← hJ'map, hJ'bot, Subgroup.map_bot]
      rw [hJbot] at h5
      simp at h5
    obtain ⟨c₀, hc₀4⟩ := hbig
    have hc₀5 : Fintype.card (Blk d c₀) ≤ 5 := card_blk_le_five d hnc c₀
    have hc₀ : Fintype.card (Blk d c₀) = 4 := by
      rcases Nat.lt_or_ge (Fintype.card (Blk d c₀)) 5 with hlt | hge
      · omega
      · have h5c : Fintype.card (Blk d c₀) = 5 := by omega
        obtain ⟨i, b, hbc, hdu⟩ := eq_update_of_card_blk_eq_five d c₀ h5c
        exact absurd ⟨ĝ, P, c₀, b, i, hĝ, hbc.symm, by rw [hPd, hdu]⟩ hnPR
    have hsmall : ∀ c' : F4, c' ≠ c₀ → Fintype.card (Blk d c') ≤ 2 := by
      intro c' hc'
      have h := card_blk_add_le d (c := c₀) (c' := c') (Ne.symm hc')
      omega
    exact ⟨ĝ, P, d, c₀, hĝ, hĝ3, hPd, hc₀, hsmall⟩
  · have hJ'dvd : Nat.card ↥J' ∣ 504 :=
      u6NineFact_holds ĝ c hc1 hcube J' hJ'le (Subgroup.isPerfect_iff.mp hJ'perf)
    have hJdvd : Nat.card ↥J ∣ Nat.card ↥J' := by
      rw [← hJ'map]
      exact Subgroup.card_map_dvd J' pi6
    have h504 : (5 : ℕ) ∣ 504 := h5.trans (dvd_trans hJdvd hJ'dvd)
    norm_num at h504

theorem pat4Inv_holds : Pat4Inv := by
  intro g h4 hnot
  obtain ⟨ĝ, P, d, c, hĝ, hĝ3, hPd, hcard4, hsmall⟩ := h4
  set D : GL (Fin 6) F4 := ((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) with hDdef
  have hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hPd
  have hDeq : D = (P : GL (Fin 6) F4)⁻¹ * (ĝ : GL (Fin 6) F4) * (P : GL (Fin 6) F4) := rfl
  have hĝ_eq : (ĝ : GL (Fin 6) F4) =
      (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ := by
    rw [hDeq]
    group
  have hdet : ((Matrix.GeneralLinearGroup.det (ĝ : GL (Fin 6) F4) : F4ˣ) : F4) ≠ 1 := by
    intro hdet1
    have hdetmat : ((ĝ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
      rwa [← Matrix.GeneralLinearGroup.val_det_apply]
    have hSU : (ĝ : GL (Fin 6) F4) ∈ StatedSU 6 (2 ^ 1) F4 := by
      rw [← gramSU_idGram_six]
      exact ⟨ĝ.2, hdetmat⟩
    exact hnot ⟨QuotientGroup.mk ⟨(ĝ : GL (Fin 6) F4), hSU⟩, by
      rw [iota_mk, ← hĝ]
      rfl⟩
  have hdetD : (D : Matrix (Fin 6) (Fin 6) F4).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det D).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hd0 : ∀ k : Fin 6, d k ≠ 0 := by
    have hprod : (∏ k : Fin 6, d k) ≠ 0 := by
      rw [← Matrix.det_diagonal]
      rwa [← hD]
    intro k
    exact Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ k)
  have hdcube : ∀ k : Fin 6, d k ^ 3 = 1 := fun k => f4_cube_eq_one (hd0 k)
  have hdetProd : (∏ k : Fin 6, d k) ≠ 1 := by
    have hDdet : Matrix.GeneralLinearGroup.det D =
        Matrix.GeneralLinearGroup.det (ĝ : GL (Fin 6) F4) := by
      rw [hDeq, map_mul, map_mul, map_inv,
        mul_comm ((Matrix.GeneralLinearGroup.det (P : GL (Fin 6) F4))⁻¹)
          (Matrix.GeneralLinearGroup.det (ĝ : GL (Fin 6) F4)),
        mul_assoc, inv_mul_cancel, mul_one]
    have hchain : (∏ k : Fin 6, d k) =
        ((Matrix.GeneralLinearGroup.det (ĝ : GL (Fin 6) F4) : F4ˣ) : F4) := by
      calc (∏ k : Fin 6, d k) = ((Matrix.GeneralLinearGroup.det D : F4ˣ) : F4) := by
            rw [← Matrix.det_diagonal, ← hD, ← Matrix.GeneralLinearGroup.val_det_apply]
        _ = ((Matrix.GeneralLinearGroup.det (ĝ : GL (Fin 6) F4) : F4ˣ) : F4) := by rw [hDdet]
    intro h1
    exact hdet (hchain.symm.trans h1)
  obtain hcase | hprod1 := exists_two_eq_or_prod_eq_one d c hdcube hcard4
  · obtain ⟨i, j, hij, hdij, hdi⟩ := hcase
    have hTcard : (Finset.univ.filter (fun k : Fin 6 => ¬ d k = c)).card = 2 := by
      rw [← Fintype.card_subtype (fun k : Fin 6 => ¬ d k = c)]
      have h := Fintype.card_subtype_compl (fun k : Fin 6 => d k = c)
      rw [Fintype.card_fin] at h
      have h4' : Fintype.card {k : Fin 6 // d k = c} = 4 := hcard4
      rw [h4'] at h
      omega
    have hTset : (Finset.univ.filter (fun k : Fin 6 => ¬ d k = c)) = {i, j} := by
      have hsub : ({i, j} : Finset (Fin 6)) ⊆
          Finset.univ.filter (fun k : Fin 6 => ¬ d k = c) := by
        intro k hk
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ k, ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hdi
        · rw [← hdij]
          exact hdi
      have hle : (Finset.univ.filter (fun k : Fin 6 => ¬ d k = c)).card ≤
          ({i, j} : Finset (Fin 6)).card := by
        rw [Finset.card_pair hij, hTcard]
      exact (Finset.eq_of_subset_of_card_le hsub hle).symm
    have hout : ∀ k : Fin 6, k ≠ i → k ≠ j → d k ≠ d i := by
      intro k hki hkj hk
      have hmem : k ∈ Finset.univ.filter (fun k : Fin 6 => ¬ d k = c) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ k, by rw [hk]; exact hdi⟩
      rw [hTset, Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem.elim hki hkj
    let σ : M6 := ⟨transpGL i j, transpGL_mem_SU i j hij⟩
    have hσval : ((σ : M6) : GL (Fin 6) F4) = transpGL i j := rfl
    have hσ2 : σ ^ 2 = 1 := by
      apply Subtype.ext
      show ((σ ^ 2 : M6) : GL (Fin 6) F4) = ((1 : M6) : GL (Fin 6) F4)
      rw [Subgroup.coe_pow, hσval, Subgroup.coe_one, pow_two]
      exact transpGL_mul_self i j
    have hσns : ¬ ∃ c' : F4ˣ, ((σ : M6) : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c' := by
      rintro ⟨c', hc'⟩
      exact transpGL_not_scalar i j hij ⟨c', by rwa [hσval] at hc'⟩
    have hDσmat : (D : Matrix (Fin 6) (Fin 6) F4) *
        ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
          (D : Matrix (Fin 6) (Fin 6) F4) := by
      rw [hD]
      exact diagonal_mul_transpGL d hij hdij
    have hDσ : D * transpGL i j = transpGL i j * D := by
      apply Units.ext
      show (D : Matrix (Fin 6) (Fin 6) F4) *
          ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
          ((transpGL i j : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
            (D : Matrix (Fin 6) (Fin 6) F4)
      exact hDσmat
    set tup : M6 := conjM6 P σ with htupdef
    set t : S6 := pi6 tup with htdef
    have htupmat : ((tup : M6) : GL (Fin 6) F4) =
        (P : GL (Fin 6) F4) * transpGL i j * (P : GL (Fin 6) F4)⁻¹ := by
      rw [htupdef, conjM6_apply, hσval]
    have hcommĝ : (ĝ : GL (Fin 6) F4) * (tup : GL (Fin 6) F4) =
        (tup : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4) := by
      rw [hĝ_eq, htupmat]
      calc (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ *
            ((P : GL (Fin 6) F4) * transpGL i j * (P : GL (Fin 6) F4)⁻¹)
          = (P : GL (Fin 6) F4) * (D * transpGL i j) * (P : GL (Fin 6) F4)⁻¹ := by group
        _ = (P : GL (Fin 6) F4) * (transpGL i j * D) * (P : GL (Fin 6) F4)⁻¹ := by rw [hDσ]
        _ = ((P : GL (Fin 6) F4) * transpGL i j * (P : GL (Fin 6) F4)⁻¹) *
              ((P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹) := by group
    have hfix : ((tup : M6) : GL (Fin 6) F4) =
        (ĝ : GL (Fin 6) F4) * (tup : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4)⁻¹ := by
      rw [hcommĝ]
      group
    have ht2 : t ^ 2 = 1 := by
      have h : tup ^ 2 = 1 := by
        rw [htupdef, ← map_pow, hσ2, map_one]
      rw [htdef]
      calc (pi6 tup) ^ 2 = pi6 (tup ^ 2) := (map_pow pi6 tup 2).symm
        _ = 1 := by rw [h, map_one]
    have ht1 : t ≠ 1 := by
      intro h1
      rw [htdef] at h1
      have hmem : tup ∈ CFSG.LocalAnalysis.GLTheoremA.KU6Cent.Z6 :=
        (QuotientGroup.eq_one_iff tup).mp h1
      obtain ⟨c', hc'⟩ := mem_Z6.1 hmem
      have hσeq : ((σ : M6) : GL (Fin 6) F4) =
          (P : GL (Fin 6) F4)⁻¹ * (tup : GL (Fin 6) F4) * (P : GL (Fin 6) F4) := by
        rw [hσval, htupmat]
        group
      have hscalar : (transpGL i j : GL (Fin 6) F4) =
          Matrix.GeneralLinearGroup.scalar (Fin 6) c' := by
        rw [← hσval, hσeq, ← hc']
        rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc,
          inv_mul_cancel, one_mul]
      exact hσns ⟨c', by rw [hσval]; exact hscalar⟩
    have hPsi : Psi g t = t := by
      rw [htdef, ← hĝ, Psi_mk]
      exact Psi0_mk ĝ tup tup hfix
    refine ⟨t, ht2, ht1, hPsi, ?_⟩
    intro J hJle hJperf s hs
    have hJle' : J ≤ fixSubgroup (Psi0 ĝ) := by
      rw [← hĝ, Psi_mk] at hJle
      exact hJle
    obtain ⟨J', hJ'le, hJ'perf, hJ'map⟩ := exists_perfect_lift_CenD ĝ hJle' hJperf
    have hJ''le : J'.map (conjM6 P⁻¹).toMonoidHom ≤ CenD D := by
      have hmap := map_CenD_conj P⁻¹ (ĝ : GL (Fin 6) F4)
      have hR : ((P⁻¹ : Gu) : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4) *
          (((P⁻¹ : Gu) : GL (Fin 6) F4))⁻¹ = D := by
        rw [hDdef]
        simp
      rw [← hR, ← hmap]
      exact Subgroup.map_mono hJ'le
    haveI : Group.IsPerfect ↥J' := hJ'perf
    have hJ''perf : ⁅J'.map (conjM6 P⁻¹).toMonoidHom,
        J'.map (conjM6 P⁻¹).toMonoidHom⁆ = J'.map (conjM6 P⁻¹).toMonoidHom :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.map (H := J') (conjM6 P⁻¹).toMonoidHom)
    have hs' : s ∈ J'.map pi6 := by rw [hJ'map]; exact hs
    obtain ⟨x, hxJ', hx⟩ := Subgroup.mem_map.mp hs'
    rw [← hx, ← map_mul, ← map_mul]
    congr 1
    set y : M6 := conjM6 P⁻¹ x with hydef
    have hyJ'' : y ∈ J'.map (conjM6 P⁻¹).toMonoidHom := Subgroup.mem_map.mpr ⟨x, hxJ', rfl⟩
    have hycen : y ∈ CenD D := hJ''le hyJ''
    have hc'3 : Fintype.card (Blk d (d i)) ≤ 3 := by
      have := hsmall (d i) hdi
      omega
    have hblk1 : blkHom hD (d i) ⟨y, hycen⟩ = 1 :=
      blk_eq_one_of_small hD hJ''le hJ''perf (d i) hc'3 hyJ''
    have hyid : ∀ a b : Fin 6, d a = d i → d b = d i →
        mM6 y a b = if a = b then 1 else 0 := by
      intro a b ha hb
      have h1 := congrArg (fun g : GL (Blk d (d i)) F4 =>
        (g : Matrix (Blk d (d i)) (Blk d (d i)) F4)) hblk1
      rw [Units.val_one, blkHom_val] at h1
      have h := congrFun (congrFun h1 ⟨a, ha⟩) ⟨b, hb⟩
      simpa [blkM, Matrix.one_apply, Subtype.ext_iff] using h
    have hyσmat := transpGL_comm_of_blocks hD hij hdij hycen hyid hout
    have hyσ : y * σ = σ * y := by
      apply Subtype.ext
      show ((y * σ : M6) : GL (Fin 6) F4) = ((σ * y : M6) : GL (Fin 6) F4)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hσval]
      exact Units.ext hyσmat
    have hPP : conjM6 P (conjM6 P⁻¹ x) = x := by
      apply Subtype.ext
      rw [conjM6_apply, conjM6_apply, Subgroup.coe_inv, inv_inv]
      group
    have hxcomm : x * tup = tup * x := by
      have h := congrArg (conjM6 P) hyσ
      rw [map_mul, map_mul] at h
      rw [hPP] at h
      simpa only [htupdef] using h
    exact hxcomm
  · exact absurd hprod1 hdetProd

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
