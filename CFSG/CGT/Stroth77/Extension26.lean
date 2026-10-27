module

public import CFSG.CGT.Stroth77.Extension23

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

namespace Type201

noncomputable abbrev PhiUV (m : ℕ) : Torus (Type201.k m) →+ Torus (Type201.k m) :=
  (Type201.action m).φuv

noncomputable abbrev PhiT (m : ℕ) : Torus (Type201.k m) →+ Torus (Type201.k m) :=
  (Type201.action m).φt

noncomputable abbrev PhiU (m : ℕ) : Torus (Type201.k m) →+ Torus (Type201.k m) :=
  (Type201.action m).φu

noncomputable abbrev PhiR (m : ℕ) : Torus (Type201.k m) →+ Torus (Type201.k m) :=
  (Type201.action m).φρ

theorem PhiU_eq (m : ℕ) :
    PhiU m = matAct (Type201.k m) (Type201.uM m) (Type201.compat_u m) := rfl

theorem PhiR_eq (m : ℕ) :
    PhiR m = matAct (Type201.k m) (Type201.ρM m) (Type201.compat_rho m) := rfl

theorem PhiUV_eq (m : ℕ) :
    PhiUV m = matAct (Type201.k m) (Type201.uvM m) (Type201.compat_uv m) := rfl

theorem PhiT_eq (m : ℕ) :
    PhiT m = matAct (Type201.k m) (Type201.tM m) (Type201.compat_t m) := rfl

end Type201

namespace StrothTypeData

variable {D : StrothTypeData B (StrothTypeIndex.t201 m)}

theorem ec_conj_u_t201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (x : B) :
    D.ec (conjBy D.u_mem x) = Type201.PhiU m (D.ec x) :=
  D.u_conj x

theorem ec_conj_t_t201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (x : B) :
    D.ec (conjBy D.t_mem x) = Type201.PhiT m (D.ec x) :=
  D.t_conj x

theorem ec_conj_ρ_t201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (x : B) :
    D.ec (conjBy D.ρ_mem x) = Type201.PhiR m (D.ec x) :=
  D.ρ_conj x

theorem ec_conj_uv_t201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (x : B) :
    D.ec (conjBy D.uv_mem x) = Type201.PhiUV m (D.ec x) :=
  D.uv_conj x

end StrothTypeData

namespace Type201

theorem PhiU_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiU m (a • gen (Type201.k m) 0 + b • gen (Type201.k m) 1 +
        c • gen (Type201.k m) 2) =
      a • gen (Type201.k m) 0 + c • gen (Type201.k m) 1 +
        b • gen (Type201.k m) 2 := by
  rw [PhiU_eq, matAct_zsmul_gens]
  have hu00 : (Type201.uM m) 0 0 = 1 := rfl
  have hu01 : (Type201.uM m) 0 1 = 0 := rfl
  have hu02 : (Type201.uM m) 0 2 = 0 := rfl
  have hu10 : (Type201.uM m) 1 0 = 0 := rfl
  have hu11 : (Type201.uM m) 1 1 = 0 := rfl
  have hu12 : (Type201.uM m) 1 2 = 1 := rfl
  have hu20 : (Type201.uM m) 2 0 = 0 := rfl
  have hu21 : (Type201.uM m) 2 1 = 1 := rfl
  have hu22 : (Type201.uM m) 2 2 = 0 := rfl
  rw [hu00, hu01, hu02, hu10, hu11, hu12, hu20, hu21, hu22]
  simp only [zero_mul, one_mul, zero_add, add_zero]

theorem PhiR_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiR m (a • gen (Type201.k m) 0 + b • gen (Type201.k m) 1 +
        c • gen (Type201.k m) 2) =
      (a - c) • gen (Type201.k m) 0 + (-c) • gen (Type201.k m) 1 +
        (b - c) • gen (Type201.k m) 2 := by
  rw [PhiR_eq, matAct_zsmul_gens]
  have hr00 : (Type201.ρM m) 0 0 = 1 := rfl
  have hr01 : (Type201.ρM m) 0 1 = 0 := rfl
  have hr02 : (Type201.ρM m) 0 2 = -1 := rfl
  have hr10 : (Type201.ρM m) 1 0 = 0 := rfl
  have hr11 : (Type201.ρM m) 1 1 = 0 := rfl
  have hr12 : (Type201.ρM m) 1 2 = -1 := rfl
  have hr20 : (Type201.ρM m) 2 0 = 0 := rfl
  have hr21 : (Type201.ρM m) 2 1 = 1 := rfl
  have hr22 : (Type201.ρM m) 2 2 = -1 := rfl
  rw [hr00, hr01, hr02, hr10, hr11, hr12, hr20, hr21, hr22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

end Type201

theorem t201_square_section
    {m : ℕ} {B : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t201 m)) (x : B)
    (hu : SquareIn B ((conjBy D.u_mem x * x⁻¹ : B) : S))
    (hr : SquareIn B ((conjBy D.ρ_mem x * x⁻¹ : B) : S)) :
    ∃ i : ℤ, SquareIn B ((x : S) * (D.c : S) ^ (-i)) := by
  classical
  let y : Torus (StrothTypeIndex.t201 m).k := D.e (Additive.ofMul x)
  obtain ⟨i, j, k, hy⟩ := torus_eq_zsmul_gens ((StrothTypeIndex.t201 m).k) y
  have hmemu : ((conjBy D.u_mem x * x⁻¹ : B) : S) ∈ B := (conjBy D.u_mem x * x⁻¹).2
  have hmemr : ((conjBy D.ρ_mem x * x⁻¹ : B) : S) ∈ B := (conjBy D.ρ_mem x * x⁻¹).2
  obtain ⟨zu, hzu⟩ := (isSquareInSubgroup_iff_even_of_type D hmemu).1 hu
  obtain ⟨zr, hzr⟩ := (isSquareInSubgroup_iff_even_of_type D hmemr).1 hr
  have hmapu : D.e (Additive.ofMul (conjBy D.u_mem x * x⁻¹ : B)) =
      (StrothTypeIndex.t201 m).action.φu y - y := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have hc : D.e (Additive.ofMul (conjBy D.u_mem x)) =
        (StrothTypeIndex.t201 m).action.φu y := by
      simpa [y, StrothTypeIndex.action, StrothTypeIndex.k] using D.u_conj x
    rw [hc, sub_eq_add_neg]
  have hmapp : D.e (Additive.ofMul (conjBy D.ρ_mem x * x⁻¹ : B)) =
      (StrothTypeIndex.t201 m).action.φρ y - y := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have hc : D.e (Additive.ofMul (conjBy D.ρ_mem x)) =
        (StrothTypeIndex.t201 m).action.φρ y := by
      simpa [y, StrothTypeIndex.action, StrothTypeIndex.k] using D.ρ_conj x
    rw [hc, sub_eq_add_neg]
  have hzu' : (StrothTypeIndex.t201 m).action.φu y - y = 2 • zu := hmapu.symm.trans hzu
  have hzr' : (StrothTypeIndex.t201 m).action.φρ y - y = 2 • zr := hmapp.symm.trans hzr
  have hφu : (StrothTypeIndex.t201 m).action.φu y =
      i • gen (StrothTypeIndex.t201 m).k 0 + k • gen (StrothTypeIndex.t201 m).k 1 +
        j • gen (StrothTypeIndex.t201 m).k 2 := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    have h0 : (StrothTypeIndex.t201 m).action.φu
        (gen (StrothTypeIndex.t201 m).k 0) = gen (StrothTypeIndex.t201 m).k 0 := by
      show (Type201.action m).φu (gen (Type201.k m) 0) = gen (Type201.k m) 0
      simpa [Torus.c, one_zsmul] using Type201.u_c m
    have h1 : (StrothTypeIndex.t201 m).action.φu
        (gen (StrothTypeIndex.t201 m).k 1) = gen (StrothTypeIndex.t201 m).k 2 := by
      show (Type201.action m).φu (gen (Type201.k m) 1) = gen (Type201.k m) 2
      simpa [Torus.a, one_zsmul] using Type201.u_a m
    have h2 : (StrothTypeIndex.t201 m).action.φu
        (gen (StrothTypeIndex.t201 m).k 2) = gen (StrothTypeIndex.t201 m).k 1 := by
      show (Type201.action m).φu (gen (Type201.k m) 2) = gen (Type201.k m) 1
      simpa [Torus.b, one_zsmul] using Type201.u_b m
    rw [h0, h1, h2]
    abel
  have hy1 : y 1 = (j : ZMod (2 ^ (StrothTypeIndex.t201 m).k 1)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  have hy2 : y 2 = (k : ZMod (2 ^ (StrothTypeIndex.t201 m).k 2)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  have h1u : ((k - j : ℤ) : ZMod (2 ^ (StrothTypeIndex.t201 m).k 1)) = 2 * zu 1 := by
    have h := congrFun hzu' 1
    rw [hφu, hy] at h
    simpa [gen, Pi.single_apply, zsmul_eq_mul] using h
  have hkj : Even (k - j) :=
    even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t201 m).k 1)
      (by simp [StrothTypeIndex.k, Type201.k]) h1u
  have hρ0 : (StrothTypeIndex.t201 m).action.φρ
      (gen (StrothTypeIndex.t201 m).k 0) = gen (StrothTypeIndex.t201 m).k 0 := by
    show (Type201.action m).φρ (gen (Type201.k m) 0) = gen (Type201.k m) 0
    simpa [Torus.c, one_zsmul] using Type201.rho_c m
  have hρ1 : (StrothTypeIndex.t201 m).action.φρ
      (gen (StrothTypeIndex.t201 m).k 1) = gen (StrothTypeIndex.t201 m).k 2 := by
    show (Type201.action m).φρ (gen (Type201.k m) 1) = gen (Type201.k m) 2
    simpa [Torus.a, one_zsmul] using Type201.rho_a m
  have hρ2 : (StrothTypeIndex.t201 m).action.φρ
      (gen (StrothTypeIndex.t201 m).k 2) =
      (-1 : ℤ) • gen (StrothTypeIndex.t201 m).k 0 +
        (-1 : ℤ) • gen (StrothTypeIndex.t201 m).k 1 +
        (-1 : ℤ) • gen (StrothTypeIndex.t201 m).k 2 := by
    show (Type201.action m).φρ (gen (Type201.k m) 2) =
      (-1 : ℤ) • gen (Type201.k m) 0 + (-1 : ℤ) • gen (Type201.k m) 1 +
        (-1 : ℤ) • gen (Type201.k m) 2
    simpa only [Torus.c, Torus.a, Torus.b] using Type201.rho_b m
  have hφρ1 : ((StrothTypeIndex.t201 m).action.φρ y) 1 =
      -(k : ZMod (2 ^ (StrothTypeIndex.t201 m).k 1)) := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    rw [hρ0, hρ1, hρ2]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
  have hφρ2 : ((StrothTypeIndex.t201 m).action.φρ y) 2 =
      (j : ZMod (2 ^ (StrothTypeIndex.t201 m).k 2)) -
        (k : ZMod (2 ^ (StrothTypeIndex.t201 m).k 2)) := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    rw [hρ0, hρ1, hρ2]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
    ring
  have h2r : ((j - 2 * k : ℤ) : ZMod (2 ^ (StrothTypeIndex.t201 m).k 2)) = 2 * zr 2 := by
    have h := congrFun hzr' 2
    simp only [Pi.sub_apply] at h
    rw [hφρ2, hy2] at h
    simp only [Pi.smul_apply, zsmul_eq_mul] at h
    convert h using 2 <;> push_cast <;> ring
  have hj2k : Even (j - 2 * k) :=
    even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t201 m).k 2)
      (by simp [StrothTypeIndex.k, Type201.k]) h2r
  have h1r : ((-(k + j) : ℤ) : ZMod (2 ^ (StrothTypeIndex.t201 m).k 1)) = 2 * zr 1 := by
    have h := congrFun hzr' 1
    simp only [Pi.sub_apply] at h
    rw [hφρ1, hy1] at h
    simp only [Pi.smul_apply, zsmul_eq_mul] at h
    push_cast
    ring_nf at h ⊢
    exact h
  have hkjsum : Even (k + j) := by
    have hneg : Even (-(k + j)) :=
      even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t201 m).k 1)
        (by simp [StrothTypeIndex.k, Type201.k]) h1r
    rcases hneg with ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    have hneg' := congrArg Neg.neg ht
    simp only [neg_neg, neg_mul] at hneg'
    rw [hneg']
    ring
  have hj : Even j := by
    have h2k : Even (2 * k) := ⟨k, by ring⟩
    exact (Int.even_sub.mp hj2k).mpr h2k
  have hk : Even k := by
    exact (Int.even_add.mp hkjsum).mpr hj
  obtain ⟨j', hj'⟩ := hj
  obtain ⟨k', hk'⟩ := hk
  have hj2 : j = 2 * j' := by rw [hj']; ring
  have hk2 : k = 2 * k' := by rw [hk']; ring
  have hxsplit : y - i • gen (StrothTypeIndex.t201 m).k 0 =
      2 • (j' • gen (StrothTypeIndex.t201 m).k 1 +
        k' • gen (StrothTypeIndex.t201 m).k 2) := by
    rw [hy, hj2, hk2, mul_zsmul, mul_zsmul]
    simp only [smul_add]
    abel
  have hmem : (x : S) * (D.c : S) ^ (-i) ∈ B :=
    B.mul_mem x.2 (B.zpow_mem D.c.2 _)
  refine ⟨i, (isSquareInSubgroup_iff_even_of_type D hmem).2 ?_⟩
  refine ⟨j' • gen (StrothTypeIndex.t201 m).k 1 +
    k' • gen (StrothTypeIndex.t201 m).k 2, ?_⟩
  have hcgen : D.e (Additive.ofMul D.c) = gen (StrothTypeIndex.t201 m).k 0 := by
    simp [StrothTypeData.c, Torus.c, gen]
  have hxci : D.e (Additive.ofMul (x * D.c ^ (-i))) =
      y - i • gen (StrothTypeIndex.t201 m).k 0 := by
    rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul, hcgen]
    rw [show D.e (Additive.ofMul x) = y from rfl, sub_eq_add_neg, neg_zsmul]
  have hsub : (⟨(x : S) * (D.c : S) ^ (-i), hmem⟩ : B) = x * D.c ^ (-i) := rfl
  rw [hsub]
  exact hxci.trans hxsplit

theorem exists_square_root_c_t201
    {m : ℕ} {B C S' : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (huC : D.u ∈ Subgroup.normalizer C) (hρC : D.ρ ∈ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) := by
  classical
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  have hlt : B < C := lt_of_le_of_ne hBC hne.symm
  obtain ⟨d, hdC, hdB⟩ := SetLike.exists_of_lt hlt
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  let dC : C := ⟨d, hdC⟩
  have hd2B : d * d ∈ B := by
    have h := sq_mem_of_index_two (B := B) (C := C) (x := dC) hindex
    simpa [dC] using h
  let xB : B := ⟨d * d, hd2B⟩
  have hnotsquare : ¬ SquareIn B (d * d) := by
    rintro ⟨b, hb2⟩
    let bC : C := ⟨b, hBC b.2⟩
    let zC : C := dC * bC⁻¹
    have hb2C : bC * bC = dC * dC := by
      apply Subtype.ext
      simpa [bC, dC] using hb2
    have hz2C : zC * zC = 1 := by
      calc
        zC * zC = (dC * bC⁻¹) * (dC * bC⁻¹) := rfl
        _ = (dC * dC) * (bC⁻¹ * bC⁻¹) := by rw [mul_mul_mul_comm]
        _ = (dC * dC) * (bC * bC)⁻¹ := by rw [_root_.mul_inv_rev]
        _ = 1 := by rw [hb2C]; group
    have hz2 : (zC : S) * (zC : S) = 1 := by
      simpa using congrArg (fun z : C => (z : S)) hz2C
    have hzC : (zC : S) ∈ C := zC.2
    have hzB : (zC : S) ∉ B := by
      intro hz
      have hd_eq : dC = zC * bC := by
        simp [zC, dC, bC]
      have hmem : dC ∈ B.subgroupOf C := by
        rw [hd_eq]
        exact (B.subgroupOf C).mul_mem (by simpa [Subgroup.mem_subgroupOf] using hz)
          (by simpa [Subgroup.mem_subgroupOf, bC] using b.2)
      exact hdB (by simpa [Subgroup.mem_subgroupOf] using hmem)
    exact hzB (hH (zC : S) (hCS hzC) hz2 (hC hzC))
  have square_conj (g : S) (hgB : g ∈ Subgroup.normalizer B)
      (hgC : g ∈ Subgroup.normalizer C) :
      SquareIn B ((conjBy hgB xB * xB⁻¹ : B) : S) := by
    have hconjC : g⁻¹ * d * g ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp hgC d).mp hdC
    have hconjB : g⁻¹ * d * g ∉ B := by
      intro hconj
      exact hdB ((Subgroup.mem_normalizer_iff''.mp hgB d).mpr hconj)
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex hconjC with hconjBinB | ⟨b, hbB, hb_eq⟩
    · exact (hconjB hconjBinB).elim
    let bB : B := ⟨b, hbB⟩
    let bC : C := ⟨b, hBC hbB⟩
    let xC : C := ⟨(xB : S), hBC xB.2⟩
    have hxC : xC = dC * dC := by
      apply Subtype.ext
      simp [xC, dC, xB]
    have hconj_eq : conjBy hgC dC = dC * bC := by
      apply Subtype.ext
      change g⁻¹ * d * g = d * b
      exact hb_eq
    refine ⟨bB, ?_⟩
    have hcoerce : ((conjBy hgB xB * xB⁻¹ : B) : S) =
        ((conjBy hgC xC * xC⁻¹ : C) : S) := rfl
    rw [hcoerce]
    change (bC : S) * (bC : S) = ((conjBy hgC xC * xC⁻¹ : C) : S)
    have hCeq : conjBy hgC xC * xC⁻¹ = bC * bC := by
      have hconj_sq : conjBy hgC xC = conjBy hgC dC * conjBy hgC dC := by
        apply Subtype.ext
        simp only [conjBy, hxC, Subgroup.coe_mul]
        group
      rw [hconj_sq, hconj_eq, hxC]
      calc
        (dC * bC) * (dC * bC) * (dC * dC)⁻¹ =
            (dC * dC) * (bC * bC) * (dC * dC)⁻¹ := by
          rw [mul_mul_mul_comm]
        _ = (bC * bC) * ((dC * dC) * (dC * dC)⁻¹) := by
          rw [mul_comm (dC * dC) (bC * bC), mul_assoc]
        _ = bC * bC := by
          have h : (dC * dC) * (dC * dC)⁻¹ = (1 : C) := mul_inv_cancel _
          rw [h, mul_one]
    exact (congrArg (fun z : C => (z : S)) hCeq).symm
  have hu : SquareIn B ((conjBy D.u_mem xB * xB⁻¹ : B) : S) :=
    square_conj D.u D.u_mem huC
  have hr : SquareIn B ((conjBy D.ρ_mem xB * xB⁻¹ : B) : S) :=
    square_conj D.ρ D.ρ_mem hρC
  obtain ⟨i, hi⟩ := t201_square_section D xB hu hr
  have hx : (xB : S) = d * d := rfl
  rw [hx] at hi
  by_cases heven : Even i
  · have hci := isSquareInSubgroup_zpow_of_even_of_type D heven
    have hx_sq : SquareIn B (d * d) := by
      have hmul := isSquareInSubgroup_mul_of_type D hi hci
      convert hmul using 1
      group
    exact (hnotsquare hx_sq).elim
  · have hodd : Odd i := by simpa using heven
    obtain ⟨t, ht⟩ := hodd
    have hi1 : Even (i - (1 : ℤ)) := ⟨t, by rw [ht]; ring⟩
    have hci1 := isSquareInSubgroup_zpow_of_even_of_type D hi1
    have hxci : SquareIn B ((d * d) * (D.c : S) ^ (-1 : ℤ)) := by
      have hmul := isSquareInSubgroup_mul_of_type D hi hci1
      have hEq : (d * d) * (D.c : S) ^ (-i) * (D.c : S) ^ (i - 1) =
          (d * d) * (D.c : S) ^ (-1 : ℤ) := by
        rw [mul_assoc, ← _root_.zpow_add]
        rw [show -i + (i - 1) = (-1 : ℤ) by ring]
      rwa [hEq] at hmul
    obtain ⟨s, hs2⟩ := hxci
    refine ⟨d * (s : S)⁻¹, C.mul_mem hdC (C.inv_mem (hBC s.2)), ?_, ?_⟩
    · intro hd'B
      apply hdB
      have hd_eq : d = (d * (s : S)⁻¹) * (s : S) := by group
      rw [hd_eq]
      exact B.mul_mem hd'B s.2
    · let sC : C := ⟨s, hBC s.2⟩
      let cC : C := ⟨(D.c : S), hBC D.c.2⟩
      have hs2C : sC * sC = dC * dC * cC⁻¹ := by
        apply Subtype.ext
        simpa [sC, dC, cC] using hs2
      let d'C : C := dC * sC⁻¹
      have hd'C : d'C * d'C = cC := by
        calc
          d'C * d'C = (dC * dC) * (sC * sC)⁻¹ := by
            simp only [d'C]
            rw [mul_mul_mul_comm, _root_.mul_inv_rev]
          _ = (dC * dC) * (dC * dC * cC⁻¹)⁻¹ := by rw [hs2C]
          _ = cC := by
            rw [_root_.mul_inv_rev, inv_inv, ← mul_assoc, mul_comm (dC * dC) cC]
            group
      have := congrArg (fun z : C => (z : S)) hd'C
      simpa [d'C, dC, sC, cC] using this

theorem exists_square_root_c_of_data_t201
    {m : ℕ} {B C S' : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) :=
  exists_square_root_c_t201 D hBC hC hrel (hL D.u_mem_L) (hL D.ρ_mem_L)
    hH hCS hne

theorem exists_square_root_c_of_hasStrothType_t201
    {m : ℕ} {B C S' : Subgroup S}
    (hB : HasStrothType B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (hB.data.c : S) :=
  exists_square_root_c_of_data_t201 hB.data hBC hC hrel hL hH hCS hne

theorem one_le_of_noInvolutionsCentralizing_t201_of_data
    {B C S' : Subgroup S} {m : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    1 ≤ m := by
  by_contra hlt
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_of_data_t201 D hBC hC hrel hL hH hcS hne
  have hc1 : (D.c : S) = 1 := by
    rw [← orderOf_eq_one_iff]
    have h := D.orderOf_c
    have hk : (StrothTypeIndex.t201 0).m = 0 := by
      have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t201 0)) 0
      simpa [StrothTypeIndex.k, Type201.k] using h.symm
    rw [hk] at h
    simpa using h
  exact hdB (hH d (hcS hdC) (by rw [hd2, hc1]) (hC hdC))

theorem one_le_of_noInvolutionsCentralizing_t201
    {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t201 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    1 ≤ m :=
  one_le_of_noInvolutionsCentralizing_t201_of_data hB.data hBC hC hrel hL hH hcS hne

namespace Type201

theorem PhiUV_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiUV m (a • gen (Type201.k m) 0 + b • gen (Type201.k m) 1 +
        c • gen (Type201.k m) 2) =
      (-3 * a + b + c) • gen (Type201.k m) 0 +
        (-4 * a + b + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * c) • gen (Type201.k m) 1 +
        (-4 * a + (2 + 2 ^ (m + 1)) * b + c) • gen (Type201.k m) 2 := by
  rw [PhiUV_eq, matAct_zsmul_gens]
  have hv00 : (Type201.uvM m) 0 0 = -3 := rfl
  have hv01 : (Type201.uvM m) 0 1 = 1 := rfl
  have hv02 : (Type201.uvM m) 0 2 = 1 := by
    simp [Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]
    ring
  have hv10 : (Type201.uvM m) 1 0 = -4 := rfl
  have hv11 : (Type201.uvM m) 1 1 = 1 := rfl
  have hv12 : (Type201.uvM m) 1 2 = 4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2 := by
    simp [Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]
    ring
  have hv20 : (Type201.uvM m) 2 0 = -4 := rfl
  have hv21 : (Type201.uvM m) 2 1 = 2 + 2 ^ (m + 1) := rfl
  have hv22 : (Type201.uvM m) 2 2 = 1 := by
    simp [Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]
    ring
  rw [hv00, hv01, hv02, hv10, hv11, hv12, hv20, hv21, hv22]
  simp only [zero_mul, one_mul, zero_add, add_zero]

theorem PhiT_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiT m (a • gen (Type201.k m) 0 + b • gen (Type201.k m) 1 +
        c • gen (Type201.k m) 2) =
      (a - (2 * 2 ^ m + 1) * c) • gen (Type201.k m) 0 +
        (4 * a + (-1 + 2 ^ (m + 1)) * b - (2 * 2 ^ m + 2) * c) • gen (Type201.k m) 1 +
        (-(2 * 2 ^ m + 1) * c) • gen (Type201.k m) 2 := by
  rw [PhiT_eq, matAct_zsmul_gens]
  have ht00 : (Type201.tM m) 0 0 = 1 := rfl
  have ht01 : (Type201.tM m) 0 1 = 0 := rfl
  have ht02 : (Type201.tM m) 0 2 = -(2 * 2 ^ m + 1) := by
    simp [Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    ring
  have ht10 : (Type201.tM m) 1 0 = 4 := rfl
  have ht11 : (Type201.tM m) 1 1 = -1 + 2 ^ (m + 1) := rfl
  have ht12 : (Type201.tM m) 1 2 = -(2 * 2 ^ m + 2) := by
    simp [Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    ring
  have ht20 : (Type201.tM m) 2 0 = 0 := rfl
  have ht21 : (Type201.tM m) 2 1 = 0 := rfl
  have ht22 : (Type201.tM m) 2 2 = -(2 * 2 ^ m + 1) := by
    simp [Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    ring
  rw [ht00, ht01, ht02, ht10, ht11, ht12, ht20, ht21, ht22]
  congr 1 <;> congr 1 <;> ring

end Type201

theorem k201_zero (m : ℕ) : Type201.k m 0 = m := by
  simp only [Type201.k, Matrix.cons_val_zero]

theorem k201_one (m : ℕ) : Type201.k m 1 = m + 2 := by
  simp only [Type201.k, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]

theorem k201_two (m : ℕ) : Type201.k m 2 = m + 2 := by
  simp only [Type201.k, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem form_bu_t201 {m : ℕ} (hm : 1 ≤ m) {x : Torus (Type201.k m)}
    (h2 : (2 : ℤ) • x = 0) (hφ : x + Type201.PhiU m x = 0) :
    ∃ ε δ : ℕ, ε ≤ 1 ∧ δ ≤ 1 ∧
      x = ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type201.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 := by
  classical
  obtain ⟨i, j, l, hx⟩ := torus_eq_zsmul_gens (Type201.k m) x
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_zero_of_eq_zero h
    rw [k201_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k201_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_two_of_eq_zero h
    rw [k201_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hφ1 : (j : ZMod (2 ^ (m + 2))) + (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h := hφ
    rw [hx, Type201.PhiU_eq, matAct_zsmul_gens, gens_add] at h
    have h10 : (Type201.uM m) 1 0 = 0 := rfl
    have h11 : (Type201.uM m) 1 1 = 0 := rfl
    have h12 : (Type201.uM m) 1 2 = 1 := rfl
    rw [h10, h11, h12] at h
    simp only [zero_mul, mul_one, one_mul, add_zero, zero_add] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k201_one] at h'
    rw [Int.cast_add] at h'
    exact h'
  have hjl : (l : ZMod (2 ^ (m + 2))) = (j : ZMod (2 ^ (m + 2))) := by
    have h1 : (l : ZMod (2 ^ (m + 2))) = -(j : ZMod (2 ^ (m + 2))) := by
      linear_combination hφ1
    have h3 : -(j : ZMod (2 ^ (m + 2))) = (j : ZMod (2 ^ (m + 2))) := by
      linear_combination -h2j
    rw [h1, h3]
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℕ, ε ≤ 1 ∧
      (i : ZMod (2 ^ m)) = (((ε : ℤ) * 2 ^ (m - 1) : ℤ) : ZMod (2 ^ m)) := by
    rcases (zmod_two_mul_eq_zero_iff hm (i : ZMod (2 ^ m))).1 h2i with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : ℕ, δ ≤ 1 ∧
      (j : ZMod (2 ^ (m + 2))) = (((δ : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (j : ZMod (2 ^ (m + 2)))).1 h2j with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hl : (l : ZMod (2 ^ (m + 2))) = (((δ : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    rw [hjl, hδ]
  refine ⟨ε, δ, hε1, hδ1, ?_⟩
  rw [hx]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k201_zero]
    exact hε
  · rw [k201_one]
    exact hδ
  · rw [k201_two]
    exact hl

theorem form_bt_t201 {m : ℕ} (hm : 1 ≤ m) {y : Torus (Type201.k m)}
    (h2 : (2 : ℤ) • y = (4 : ℤ) • gen (Type201.k m) 1)
    (hφ : y + Type201.PhiT m y = 0) :
    ∃ α q : ℕ, α ≤ 1 ∧ q ≤ 1 ∧
      y = (0 : ℤ) • gen (Type201.k m) 0 +
        ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 := by
  classical
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (Type201.k m) y
  have h2' : (2 * i) • gen (Type201.k m) 0 + (2 * j) • gen (Type201.k m) 1 +
      (2 * l) • gen (Type201.k m) 2 =
      (0 : ℤ) • gen (Type201.k m) 0 + (4 : ℤ) • gen (Type201.k m) 1 +
        (0 : ℤ) • gen (Type201.k m) 2 := by
    rw [← zsmul_gens, ← hy, h2]
    simp
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h' := gens_coord_zero h2'
    rw [k201_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = 4 := by
    have h' := gens_coord_one h2'
    rw [k201_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h' := gens_coord_two h2'
    rw [k201_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨q, hq1, hq⟩ : ∃ q : ℕ, q ≤ 1 ∧
      (l : ZMod (2 ^ (m + 2))) = (q : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (l : ZMod (2 ^ (m + 2)))).1 h2l with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have hφ1 : ((4 * i - 2 * l : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    have h := hφ
    rw [hy, Type201.PhiT_apply_gens, gens_add] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k201_one] at h'
    have hzero : (2 : ZMod (2 ^ (m + 2))) ^ (m + 2) = 0 := by
      rw [show (2 : ZMod (2 ^ (m + 2))) = ((2 : ℕ) : ZMod (2 ^ (m + 2))) by norm_num,
        ← Nat.cast_pow, ZMod.natCast_self]
    have hj0 : (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) * (j : ZMod (2 ^ (m + 2))) = 0 := by
      calc (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) * (j : ZMod (2 ^ (m + 2))) =
            2 ^ m * (2 * (j : ZMod (2 ^ (m + 2)))) := by ring
        _ = 2 ^ m * 4 := by rw [h2j]
        _ = 2 ^ (m + 2) := by ring
        _ = 0 := hzero
    have hl0 : (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) * (l : ZMod (2 ^ (m + 2))) = 0 := by
      rw [hq]
      calc (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) * ((q : ZMod (2 ^ (m + 2))) *
            ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2)))) =
            (q : ZMod (2 ^ (m + 2))) * 2 ^ m * 2 ^ (m + 2) := by push_cast; ring
        _ = 0 := by rw [hzero, mul_zero]
    push_cast at h' ⊢
    linear_combination h' - hj0 + hl0
  have h2lz : ((2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2)))) = 0 := by
    rw [hq]
    rw [show (2 : ZMod (2 ^ (m + 2))) * ((q : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2)))) =
        ((q : ℤ) * 2 ^ (m + 2) : ℤ) by push_cast; ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨(q : ℤ), by push_cast; ring⟩
  have h2lzi : ((2 * l : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    simpa using h2lz
  have h4i : ((4 * i : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    have h := hφ1
    rw [Int.cast_sub] at h
    linear_combination h + h2lzi
  have hdvd4 : ((2 : ℤ) ^ (m + 2)) ∣ 4 * i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * i) (2 ^ (m + 2))).1 h4i
  have hdvd2 : ((2 : ℤ) ^ (m + 1)) ∣ 2 * i := by
    apply dvd_of_dvd_two_mul (k := m + 1)
    simpa [show m + 1 + 1 = m + 2 by omega, show (2 : ℤ) * (2 * i) = 4 * i by ring] using hdvd4
  have hdvd : ((2 : ℤ) ^ m) ∣ i := by
    apply dvd_of_dvd_two_mul (k := m)
    simpa using hdvd2
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  obtain ⟨α, hα1, hα⟩ : ∃ α : ℕ, α ≤ 1 ∧
      (j : ZMod (2 ^ (m + 2))) = 2 + (α : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    have h2j' : (2 : ZMod (2 ^ (m + 2))) * ((j : ZMod (2 ^ (m + 2))) - 2) = 0 := by
      linear_combination h2j
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      ((j : ZMod (2 ^ (m + 2))) - 2)).1 h2j' with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have h1 : (((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      2 + (α : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  have h2q : (((q : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      (q : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  refine ⟨α, q, hα1, hq1, ?_⟩
  rw [hy]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k201_zero, Int.cast_zero]
    exact hi
  · rw [k201_one, h1]
    exact hα
  · rw [k201_two, h2q]
    exact hq

theorem form_br_t201 {m : ℕ} (hm : 1 ≤ m) {z : Torus (Type201.k m)}
    (h2 : (2 : ℤ) • z = 0)
    (hφ : z + Type201.PhiR m z + Type201.PhiR m (Type201.PhiR m z) = 0) :
    ∃ θ η : ℕ, η ≤ 1 ∧ θ ≤ 1 ∧
      z = (0 : ℤ) • gen (Type201.k m) 0 + ((η : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 := by
  classical
  obtain ⟨i, j, l, hz⟩ := torus_eq_zsmul_gens (Type201.k m) z
  have h2' : (2 * i) • gen (Type201.k m) 0 + (2 * j) • gen (Type201.k m) 1 +
      (2 * l) • gen (Type201.k m) 2 = (0 : Torus (Type201.k m)) := by
    rw [← zsmul_gens, ← hz, h2]
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h' := gens_coord_zero_of_eq_zero h2'
    rw [k201_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = 0 := by
    have h' := gens_coord_one_of_eq_zero h2'
    rw [k201_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h' := gens_coord_two_of_eq_zero h2'
    rw [k201_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hdvdj : ((2 : ℤ) ^ (m + 1)) ∣ j :=
    dvd_of_dvd_two_mul (k := m + 1) (dvd_two_mul_of_two_mul_cast_eq_zero h2j)
  have hdvdl : ((2 : ℤ) ^ (m + 1)) ∣ l :=
    dvd_of_dvd_two_mul (k := m + 1) (dvd_two_mul_of_two_mul_cast_eq_zero h2l)
  have hj0 : (j : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (pow_dvd_pow 2 (by omega : m ≤ m + 1)) hdvdj
  have hl0 : (l : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (pow_dvd_pow 2 (by omega : m ≤ m + 1)) hdvdl
  have hφ1 : ((3 * i - j - l : ℤ) : ZMod (2 ^ m)) = 0 := by
    have h := hφ
    rw [hz, Type201.PhiR_apply_gens, Type201.PhiR_apply_gens] at h
    have h0 := congrFun h 0
    simp [gen, Pi.single_apply, zsmul_eq_mul] at h0
    have hk : Type201.k m 0 = m := k201_zero m
    have h0' : (↑i + (↑i - ↑l) + (↑i - ↑j) : ZMod (2 ^ m)) = 0 := hk ▸ h0
    have hcast : (((i + (i - l) + (i - j) : ℤ)) : ZMod (2 ^ m)) = 0 := by
      simpa only [Int.cast_add, Int.cast_sub] using h0'
    have hEq : (((i + (i - l) + (i - j) : ℤ)) : ZMod (2 ^ m)) =
        (((3 * i - j - l : ℤ)) : ZMod (2 ^ m)) := by
      congr 1
      ring
    rwa [hEq] at hcast
  have h3i : (3 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h := hφ1
    rw [Int.cast_sub, Int.cast_sub, Int.cast_mul] at h
    linear_combination h + hj0 + hl0
  have hdvd3 : ((2 : ℤ) ^ m) ∣ 3 * i := by
    have h3i' : (((3 : ℤ) : ZMod (2 ^ m))) * (i : ZMod (2 ^ m)) = 0 := by
      simpa using h3i
    exact dvd_of_cast_mul_eq_zero h3i'
  have hcop : IsCoprime ((2 : ℤ) ^ m) (3 : ℤ) :=
    ((show Odd (3 : ℤ) by norm_num).isCoprime_two).symm.pow_left
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    have hd : ((2 : ℤ) ^ m) ∣ i :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hdvd3 (Int.isCoprime_iff_gcd_eq_one.mp hcop)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨η, hη1, hη⟩ : ∃ η : ℕ, η ≤ 1 ∧
      (j : ZMod (2 ^ (m + 2))) = (η : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (j : ZMod (2 ^ (m + 2)))).1 h2j with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  obtain ⟨θ, hθ1, hθ⟩ : ∃ θ : ℕ, θ ≤ 1 ∧
      (l : ZMod (2 ^ (m + 2))) = (θ : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (l : ZMod (2 ^ (m + 2)))).1 h2l with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have h2q : (((η : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      (η : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  have h3q : (((θ : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      (θ : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  refine ⟨θ, η, hη1, hθ1, ?_⟩
  rw [hz]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k201_zero, Int.cast_zero]
    exact hi
  · rw [k201_one, h2q]
    exact hη
  · rw [k201_two, h3q]
    exact hθ

theorem form_buv_t201 {m : ℕ} (hm : 1 ≤ m) {z : Torus (Type201.k m)}
    (h2 : (2 : ℤ) • z =
      (-4 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
        (-4 : ℤ) • gen (Type201.k m) 2)
    (hφ : z + Type201.PhiUV m z = 0) :
    ∃ p r : ℕ, p ≤ 1 ∧ r ≤ 1 ∧
      z = (-2 : ℤ) • gen (Type201.k m) 0 +
        ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 := by
  classical
  obtain ⟨i, j, l, hz⟩ := torus_eq_zsmul_gens (Type201.k m) z
  have h2' : (2 * i) • gen (Type201.k m) 0 + (2 * j) • gen (Type201.k m) 1 +
      (2 * l) • gen (Type201.k m) 2 =
      (-4 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
        (-4 : ℤ) • gen (Type201.k m) 2 := by
    rw [← zsmul_gens, ← hz, h2]
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = -4 := by
    have h' := gens_coord_zero h2'
    rw [k201_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = -4 := by
    have h' := gens_coord_one h2'
    rw [k201_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = -4 := by
    have h' := gens_coord_two h2'
    rw [k201_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2i' : (2 : ZMod (2 ^ m)) * ((i + 2 : ℤ) : ZMod (2 ^ m)) = 0 := by
    rw [Int.cast_add]
    linear_combination h2i
  obtain ⟨ev, hev1, hev⟩ : ∃ ev : ℕ, ev ≤ 1 ∧
      ((i + 2 : ℤ) : ZMod (2 ^ m)) = (((ev : ℤ) * 2 ^ (m - 1) : ℤ) : ZMod (2 ^ m)) := by
    rcases (zmod_two_mul_eq_zero_iff hm ((i + 2 : ℤ) : ZMod (2 ^ m))).1 h2i' with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨p, hp1, hp⟩ : ∃ p : ℕ, p ≤ 1 ∧
      ((j + 2 : ℤ) : ZMod (2 ^ (m + 2))) = (((p : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    have h2j' : (2 : ZMod (2 ^ (m + 2))) * ((j + 2 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      rw [Int.cast_add]
      linear_combination h2j
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      ((j + 2 : ℤ) : ZMod (2 ^ (m + 2)))).1 h2j' with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  obtain ⟨r, hr1, hr⟩ : ∃ r : ℕ, r ≤ 1 ∧
      ((l + 2 : ℤ) : ZMod (2 ^ (m + 2))) = (((r : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    have h2l' : (2 : ZMod (2 ^ (m + 2))) * ((l + 2 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      rw [Int.cast_add]
      linear_combination h2l
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      ((l + 2 : ℤ) : ZMod (2 ^ (m + 2)))).1 h2l' with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  let i0 : ℤ := -2 + (ev : ℤ) * 2 ^ (m - 1)
  let j0 : ℤ := -2 + (p : ℤ) * 2 ^ (m + 1)
  let l0 : ℤ := -2 + (r : ℤ) * 2 ^ (m + 1)
  have hi0 : (i0 : ZMod (2 ^ m)) = (i : ZMod (2 ^ m)) := by
    have h := hev
    simp only [i0] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hj0 : (j0 : ZMod (2 ^ (m + 2))) = (j : ZMod (2 ^ (m + 2))) := by
    have h := hp
    simp only [j0] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hl0 : (l0 : ZMod (2 ^ (m + 2))) = (l : ZMod (2 ^ (m + 2))) := by
    have h := hr
    simp only [l0] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hz0 : z = i0 • gen (Type201.k m) 0 + j0 • gen (Type201.k m) 1 +
      l0 • gen (Type201.k m) 2 := by
    rw [hz]
    refine gens_eq_of_coord ?_ ?_ ?_
    · exact hi0.symm
    · exact hj0.symm
    · exact hl0.symm
  have hφ' : (i0 • gen (Type201.k m) 0 + j0 • gen (Type201.k m) 1 +
      l0 • gen (Type201.k m) 2) +
      Type201.PhiUV m (i0 • gen (Type201.k m) 0 + j0 • gen (Type201.k m) 1 +
        l0 • gen (Type201.k m) 2) = 0 := by
    rwa [← hz0]
  rw [Type201.PhiUV_apply_gens, gens_add] at hφ'
  have hφa : ((-4 * i0 + 2 * j0 + 2 * l0 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    have hcast := gens_coord_one_of_eq_zero hφ'
    rw [k201_one] at hcast
    have hdiv : ((2 : ℤ) ^ (m + 2)) ∣ (j0 + (-4 * i0 + j0 +
        (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * l0)) - (-4 * i0 + 2 * j0 + 2 * l0) := by
      refine ⟨(2 ^ (m + 1) + 3) * (-1 + (r : ℤ) * 2 ^ m), ?_⟩
      simp only [l0]
      ring
    have hdiv' : (((j0 + (-4 * i0 + j0 + (4 * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) * l0)) -
        (-4 * i0 + 2 * j0 + 2 * l0) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hdiv
    push_cast at hcast hdiv' ⊢
    linear_combination hcast - hdiv'
  have hev0 : ev = 0 := by
    have hpow4 : (4 : ℤ) * 2 ^ (m - 1) = 2 ^ (m + 1) := by
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
      ring
    have hid : (-4 * i0 + 2 * j0 + 2 * l0 : ℤ) =
        -((ev : ℤ) * 2 ^ (m + 1)) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) := by
      dsimp only [i0, j0, l0]
      calc
        -4 * (-2 + (ev : ℤ) * 2 ^ (m - 1)) +
            2 * (-2 + (p : ℤ) * 2 ^ (m + 1)) +
            2 * (-2 + (r : ℤ) * 2 ^ (m + 1)) =
            -((ev : ℤ) * (4 * 2 ^ (m - 1))) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) := by
          ring
        _ = -((ev : ℤ) * 2 ^ (m + 1)) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) := by
          rw [hpow4]
    have h' : ((-((ev : ℤ) * 2 ^ (m + 1)) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) : ℤ) :
        ZMod (2 ^ (m + 2))) = 0 := by
      rwa [hid] at hφa
    have hpr : ((((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      push_cast
      rw [show ((2 : ZMod (2 ^ (m + 2))) ^ (m + 2)) = 0 by
        rw [show (2 : ZMod (2 ^ (m + 2))) = ((2 : ℕ) : ZMod (2 ^ (m + 2))) by norm_num,
          ← Nat.cast_pow, ZMod.natCast_self]]
      simp
    have hev : ((-((ev : ℤ) * 2 ^ (m + 1)) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have h1 := h'
      rw [Int.cast_add, Int.cast_neg] at h1
      rw [hpr, add_zero] at h1
      simpa only [Int.cast_neg] using h1
    have h : (((ev : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have hev' : (-(((ev : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2)))) = 0 := by
        rw [← Int.cast_neg]
        exact hev
      exact neg_eq_zero.mp hev'
    interval_cases ev
    · rfl
    · exfalso
      have h' : (((2 ^ (m + 1) : ℕ)) : ZMod (2 ^ (m + 2))) = 0 := by
        simpa using h
      have hdvd : ((2 : ℕ) ^ (m + 2)) ∣ 2 ^ (m + 1) :=
        (ZMod.natCast_eq_zero_iff _ _).1 h'
      have hle := Nat.le_of_dvd (by positivity) hdvd
      have hlt : 2 ^ (m + 1) < 2 ^ (m + 2) :=
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m + 1 < m + 2)
      omega
  have hi0' : i0 = -2 := by simp [i0, hev0]
  refine ⟨p, r, hp1, hr1, ?_⟩
  rw [hz0, hi0']

namespace Type201

theorem PhiU_c (m : ℕ) : PhiU m Torus.c = (1 : ℤ) • Torus.c :=
  Type201.u_c m

theorem PhiT_c (m : ℕ) : PhiT m Torus.c = (1 : ℤ) • Torus.c + (4 : ℤ) • Torus.a :=
  Type201.t_c m

theorem PhiR_c (m : ℕ) : PhiR m Torus.c = (1 : ℤ) • Torus.c :=
  Type201.rho_c m

theorem PhiUV_c (m : ℕ) :
    PhiUV m Torus.c = (-3 : ℤ) • Torus.c + (-4 : ℤ) • Torus.a + (-4 : ℤ) • Torus.b :=
  Type201.uv_c m

end Type201
section Concrete

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))

noncomputable def bU201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem)

noncomputable def bT201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem)

noncomputable def bR201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem)

noncomputable def bUV201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem)

theorem conj_eq_bU201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU201 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem)

theorem conj_eq_bT201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bT201 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem)

theorem conj_eq_bR201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR201 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem)

theorem conj_eq_bUV201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bUV201 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem)

noncomputable abbrev xU201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type201.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bU201 D hBC hrel hdC hdB hL)

noncomputable abbrev yT201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type201.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bT201 D hBC hrel hdC hdB hL)

noncomputable abbrev zR201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type201.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bR201 D hBC hrel hdC hdB hL)

noncomputable abbrev wUV201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type201.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bUV201 D hBC hrel hdC hdB hL)

theorem sq_bU201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • xU201 D hBC hrel hdC hdB hL = 0 := by
  let β : B := D.c⁻¹ * conjBy D.u_mem D.c
  have hβ : conjBy D.u_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.u_mem_L) D.u_mem
    (conj_eq_bU201 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.u_mem D.c) = Torus.c := by
    rw [StrothTypeData.ec_conj_u_t201, hc]
    simpa only [StrothTypeIndex.k, one_smul] using Type201.PhiU_c m
  have hβ0 : D.ec β = 0 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    abel
  change (2 : ℤ) • D.ec (bU201 D hBC hrel hdC hdB hL) = 0
  rw [h, hβ0]

theorem sq_bT201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • yT201 D hBC hrel hdC hdB hL = (4 : ℤ) • gen (Type201.k m) 1 := by
  let β : B := D.c⁻¹ * conjBy D.t_mem D.c
  have hβ : conjBy D.t_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.t_mem_L) D.t_mem
    (conj_eq_bT201 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.t_mem D.c) =
      (1 : ℤ) • Torus.c + (4 : ℤ) • Torus.a := by
    rw [StrothTypeData.ec_conj_t_t201, hc]
    exact Type201.PhiT_c m
  have hβ0 : D.ec β = (4 : ℤ) • gen (Type201.k m) 1 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    show (-(gen (Type201.k m) 0) +
        ((1 : ℤ) • gen (Type201.k m) 0 + (4 : ℤ) • gen (Type201.k m) 1)) =
      (4 : ℤ) • gen (Type201.k m) 1
    module
  change (2 : ℤ) • D.ec (bT201 D hBC hrel hdC hdB hL) = (4 : ℤ) • gen (Type201.k m) 1
  rw [h, hβ0]

theorem sq_bR201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • zR201 D hBC hrel hdC hdB hL = 0 := by
  let β : B := D.c⁻¹ * conjBy D.ρ_mem D.c
  have hβ : conjBy D.ρ_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.ρ_mem_L) D.ρ_mem
    (conj_eq_bR201 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.ρ_mem D.c) = Torus.c := by
    rw [StrothTypeData.ec_conj_ρ_t201, hc]
    simpa only [StrothTypeIndex.k, one_smul] using Type201.PhiR_c m
  have hβ0 : D.ec β = 0 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    abel
  change (2 : ℤ) • D.ec (bR201 D hBC hrel hdC hdB hL) = 0
  rw [h, hβ0]

theorem sq_bUV201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • wUV201 D hBC hrel hdC hdB hL =
      (-4 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
        (-4 : ℤ) • gen (Type201.k m) 2 := by
  let β : B := D.c⁻¹ * conjBy D.uv_mem D.c
  have hβ : conjBy D.uv_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.uv_mem_L) D.uv_mem
    (conj_eq_bUV201 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.uv_mem D.c) =
      (-3 : ℤ) • Torus.c + (-4 : ℤ) • Torus.a + (-4 : ℤ) • Torus.b := by
    rw [StrothTypeData.ec_conj_uv_t201, hc]
    exact Type201.PhiUV_c m
  have hβ0 : D.ec β =
      (-4 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
        (-4 : ℤ) • gen (Type201.k m) 2 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    show (-(gen (Type201.k m) 0) +
        ((-3 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
          (-4 : ℤ) • gen (Type201.k m) 2)) =
      (-4 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
        (-4 : ℤ) • gen (Type201.k m) 2
    module
  change (2 : ℤ) • D.ec (bUV201 D hBC hrel hdC hdB hL) =
    (-4 : ℤ) • gen (Type201.k m) 0 + (-4 : ℤ) • gen (Type201.k m) 1 +
      (-4 : ℤ) • gen (Type201.k m) 2
  rw [h, hβ0]

theorem phi_bU201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    xU201 D hBC hrel hdC hdB hL + Type201.PhiU m (xU201 D hBC hrel hdC hdB hL) = 0 :=
  inv_rel_of_type D hBC hdC (hL D.u_mem_L) D.u_mem
    (conj_eq_bU201 D hBC hrel hdC hdB hL) D.u_sq (Type201.PhiU m)
    (fun x => StrothTypeData.ec_conj_u_t201 D x)

theorem phi_bT201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    yT201 D hBC hrel hdC hdB hL + Type201.PhiT m (yT201 D hBC hrel hdC hdB hL) = 0 :=
  inv_rel_of_type D hBC hdC (hL D.t_mem_L) D.t_mem
    (conj_eq_bT201 D hBC hrel hdC hdB hL) D.t_sq (Type201.PhiT m)
    (fun x => StrothTypeData.ec_conj_t_t201 D x)

theorem phi_bR201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    zR201 D hBC hrel hdC hdB hL + Type201.PhiR m (zR201 D hBC hrel hdC hdB hL) +
      Type201.PhiR m (Type201.PhiR m (zR201 D hBC hrel hdC hdB hL)) = 0 :=
  inv_rel_three_of_type D hBC hdC (hL D.ρ_mem_L) D.ρ_mem
    (conj_eq_bR201 D hBC hrel hdC hdB hL) D.rho_cube (Type201.PhiR m)
    (fun x => StrothTypeData.ec_conj_ρ_t201 D x)

theorem phi_bUV201 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    wUV201 D hBC hrel hdC hdB hL + Type201.PhiUV m (wUV201 D hBC hrel hdC hdB hL) = 0 :=
  inv_rel_of_type D hBC hdC (hL D.uv_mem_L) D.uv_mem
    (conj_eq_bUV201 D hBC hrel hdC hdB hL) D.uv_sq (Type201.PhiUV m)
    (fun x => StrothTypeData.ec_conj_uv_t201 D x)

theorem form_xU201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ ε δ : ℕ, ε ≤ 1 ∧ δ ≤ 1 ∧
      xU201 D hBC hrel hdC hdB hL = ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type201.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 :=
  form_bu_t201 hm (sq_bU201 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bU201 D hBC hrel hdC hdB hL)

theorem form_yT201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ α q : ℕ, α ≤ 1 ∧ q ≤ 1 ∧
      yT201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
        ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((q : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 :=
  form_bt_t201 hm (sq_bT201 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bT201 D hBC hrel hdC hdB hL)

theorem form_zR201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ θ η : ℕ, η ≤ 1 ∧ θ ≤ 1 ∧
      zR201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
        ((η : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 :=
  form_br_t201 hm (sq_bR201 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bR201 D hBC hrel hdC hdB hL)

theorem form_wUV201 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ p r : ℕ, p ≤ 1 ∧ r ≤ 1 ∧
      wUV201 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type201.k m) 0 +
        ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2 :=
  form_buv_t201 hm (sq_bUV201 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bUV201 D hBC hrel hdC hdB hL)

end Concrete
section Cross201

variable (D : StrothTypeData B (StrothTypeIndex.t201 m))
variable (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
  (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
  (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m)

theorem bit_eps_201 (hm : 1 ≤ m) {ε δ p r : ℕ} (hε : ε ≤ 1) (hδ : δ ≤ 1)
    (hp : p ≤ 1) (hr : r ≤ 1)
    (hX : xU201 D hBC hrel hdC hdB hL =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type201.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2)
    (hW : wUV201 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type201.k m) 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    ε = (p + r) % 2 := by
  have h := rel_uv_comm_u_of_type D hBC hdC (hL D.u_mem_L) (hL D.uv_mem_L)
    (conj_eq_bU201 D hBC hrel hdC hdB hL) (conj_eq_bUV201 D hBC hrel hdC hdB hL)
    (Type201.PhiU m) (Type201.PhiUV m)
    (fun x => StrothTypeData.ec_conj_u_t201 D x)
    (fun x => StrothTypeData.ec_conj_uv_t201 D x)
  change xU201 D hBC hrel hdC hdB hL +
      Type201.PhiU m (wUV201 D hBC hrel hdC hdB hL) =
    wUV201 D hBC hrel hdC hdB hL +
      Type201.PhiUV m (xU201 D hBC hrel hdC hdB hL) at h
  rw [hX, hW, Type201.PhiU_apply_gens, Type201.PhiUV_apply_gens] at h
  have h1 := congrFun h 1
  simp [gen, Pi.single_apply, zsmul_eq_mul] at h1
  have hNpos : 1 ≤ Type201.k m 1 := by rw [k201_one m]; omega
  have hN1 : Type201.k m 1 - 1 = m + 1 := by rw [k201_one m]; omega
  have hcast : ((((r : ℤ) - (p : ℤ) + (ε : ℤ)) * 2 ^ (Type201.k m 1 - 1) : ℤ) :
      ZMod (2 ^ (Type201.k m 1))) = 0 := by
    rw [hN1]
    have hpow2 : (2 : ZMod (2 ^ Type201.k m 1)) ^ m * 2 = 2 ^ (m + 1) := by
      rw [← pow_succ]
    have hpow4 : (4 : ZMod (2 ^ Type201.k m 1)) * 2 ^ (m - 1) = 2 ^ (m + 1) := by
      rw [show (4 : ZMod (2 ^ Type201.k m 1)) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      rw [Nat.add_comm]
      rw [show (2 : ℕ) = 1 + 1 by norm_num, ← Nat.add_assoc, Nat.sub_add_cancel hm]
    have hpow6 : (4 : ZMod (2 ^ Type201.k m 1)) * (↑ε * 2 ^ (m - 1)) =
        ↑ε * 2 ^ (m + 1) := by
      calc
        (4 : ZMod (2 ^ Type201.k m 1)) * (↑ε * 2 ^ (m - 1)) =
            ↑ε * ((4 : ZMod (2 ^ Type201.k m 1)) * 2 ^ (m - 1)) := by ring
        _ = ↑ε * 2 ^ (m + 1) := by rw [hpow4]
    have hpow5 : ((4 : ZMod (2 ^ Type201.k m 1)) * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) *
        (↑δ * 2 ^ (m + 1)) = 0 := by
      have hz : (2 : ZMod (2 ^ Type201.k m 1)) ^ (m + 2) = 0 := by
        rw [show m + 2 = Type201.k m 1 by rw [k201_one m]]
        rw [show (2 : ZMod (2 ^ Type201.k m 1)) = ((2 : ℕ) : ZMod (2 ^ Type201.k m 1))
          by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
      calc ((4 : ZMod (2 ^ Type201.k m 1)) * (2 ^ m) ^ 2 + 6 * 2 ^ m + 2) *
            (↑δ * 2 ^ (m + 1)) =
            ↑δ * ((2 ^ (m + 1) + 3) * 2 ^ m + 1) * 2 ^ (m + 2) := by ring
        _ = 0 := by rw [hz, mul_zero]
    push_cast at h1 ⊢
    rw [hpow6] at h1
    linear_combination h1 + hpow5
  have he : Even ((r : ℤ) - (p : ℤ) + (ε : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos hcast
  exact bit_eps_of_even hε hp hr he

theorem bit_alpha_q_201 (hm : 1 ≤ m) {ε δ p r α q η θ : ℕ}
    (hα : α ≤ 1) (hq : q ≤ 1) (hp : p ≤ 1) (hr : r ≤ 1)
    (hY : yT201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
      ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2)
    (hZ : zR201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2)
    (hW : wUV201 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type201.k m) 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    α = r ∧ q = (p + r) % 2 := by
  have h := rel_t_rho_of_type D hBC hdC (hL D.t_mem_L) (hL D.ρ_mem_L) (hL D.uv_mem_L)
    (conj_eq_bT201 D hBC hrel hdC hdB hL) (conj_eq_bR201 D hBC hrel hdC hdB hL)
    (conj_eq_bUV201 D hBC hrel hdC hdB hL)
    (Type201.PhiT m) (Type201.PhiR m) (Type201.PhiUV m)
    (fun x => StrothTypeData.ec_conj_t_t201 D x)
    (fun x => StrothTypeData.ec_conj_ρ_t201 D x)
    (fun x => StrothTypeData.ec_conj_uv_t201 D x)
  change zR201 D hBC hrel hdC hdB hL +
      Type201.PhiR m (yT201 D hBC hrel hdC hdB hL) =
    yT201 D hBC hrel hdC hdB hL +
      Type201.PhiT m (wUV201 D hBC hrel hdC hdB hL) +
        Type201.PhiT m (Type201.PhiUV m (zR201 D hBC hrel hdC hdB hL)) at h
  rw [hY, hZ, hW, Type201.PhiR_apply_gens, Type201.PhiT_apply_gens,
    Type201.PhiUV_apply_gens, Type201.PhiT_apply_gens] at h
  have hN1 : Type201.k m 1 - 1 = m + 1 := by rw [k201_one m]; omega
  have hN2 : Type201.k m 2 - 1 = m + 1 := by rw [k201_two m]; omega
  have hNpos1 : 1 ≤ Type201.k m 1 := by rw [k201_one m]; omega
  have hNpos2 : 1 ≤ Type201.k m 2 := by rw [k201_two m]; omega
  have hpow0a : (2 : ZMod (2 ^ Type201.k m 1)) ^ m * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ Type201.k m 1)) = 2 ^ 2 by norm_num, ← pow_add]
    rw [show m + 2 = Type201.k m 1 by rw [k201_one m]]
    rw [show (2 : ZMod (2 ^ Type201.k m 1)) = ((2 : ℕ) : ZMod (2 ^ Type201.k m 1))
      by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
  have hpow0b : (2 : ZMod (2 ^ Type201.k m 2)) ^ m * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ Type201.k m 2)) = 2 ^ 2 by norm_num, ← pow_add]
    rw [show m + 2 = Type201.k m 2 by rw [k201_two m]]
    rw [show (2 : ZMod (2 ^ Type201.k m 2)) = ((2 : ℕ) : ZMod (2 ^ Type201.k m 2))
      by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
  have ha := congrFun h 1
  simp [gen, Pi.single_apply, zsmul_eq_mul] at ha
  have hcasta : ((((p : ℤ) + (q : ℤ) + (α : ℤ)) * 2 ^ (Type201.k m 1 - 1) : ℤ) :
      ZMod (2 ^ Type201.k m 1)) = 0 := by
    rw [hN1]
    push_cast at ha ⊢
    linear_combination ha +
      (4 * ((2 : ZMod (2 ^ Type201.k m 1)) ^ m) ^ 3 * (θ : ZMod (2 ^ Type201.k m 1)) -
        2 * ((2 : ZMod (2 ^ Type201.k m 1)) ^ m) ^ 2 * (η : ZMod (2 ^ Type201.k m 1)) +
        4 * ((2 : ZMod (2 ^ Type201.k m 1)) ^ m) ^ 2 * (θ : ZMod (2 ^ Type201.k m 1)) +
        (2 : ZMod (2 ^ Type201.k m 1)) ^ m * (p : ZMod (2 ^ Type201.k m 1)) -
        (2 : ZMod (2 ^ Type201.k m 1)) ^ m * (r : ZMod (2 ^ Type201.k m 1)) -
        3 * (2 : ZMod (2 ^ Type201.k m 1)) ^ m * (η : ZMod (2 ^ Type201.k m 1)) -
        2 * (2 : ZMod (2 ^ Type201.k m 1)) ^ m * (θ : ZMod (2 ^ Type201.k m 1)) +
        (q : ZMod (2 ^ Type201.k m 1)) - (r : ZMod (2 ^ Type201.k m 1)) +
        (α : ZMod (2 ^ Type201.k m 1)) - (η : ZMod (2 ^ Type201.k m 1))) * hpow0a
  have hb := congrFun h 2
  simp [gen, Pi.single_apply, zsmul_eq_mul] at hb
  have hcastb : ((((r : ℤ) + (α : ℤ)) * 2 ^ (Type201.k m 2 - 1) : ℤ) :
      ZMod (2 ^ Type201.k m 2)) = 0 := by
    rw [hN2]
    push_cast at hb ⊢
    linear_combination hb +
      (-2 * ((2 : ZMod (2 ^ Type201.k m 2)) ^ m) ^ 2 * (η : ZMod (2 ^ Type201.k m 2)) -
        (2 : ZMod (2 ^ Type201.k m 2)) ^ m * (r : ZMod (2 ^ Type201.k m 2)) -
        3 * (2 : ZMod (2 ^ Type201.k m 2)) ^ m * (η : ZMod (2 ^ Type201.k m 2)) -
        (2 : ZMod (2 ^ Type201.k m 2)) ^ m * (θ : ZMod (2 ^ Type201.k m 2)) +
        (q : ZMod (2 ^ Type201.k m 2)) - (η : ZMod (2 ^ Type201.k m 2)) -
        (θ : ZMod (2 ^ Type201.k m 2)) + 1) * hpow0b
  have hea : Even ((p : ℤ) + (q : ℤ) + (α : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos1 hcasta
  have heb : Even ((r : ℤ) + (α : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos2 hcastb
  have hαr : α = r := bit_eq_of_even_add hα hr (by simpa [add_comm] using heb)
  refine ⟨hαr, ?_⟩
  have hqpa : q = (p + α) % 2 := bit_q_of_even hq hp hα hea
  rw [hαr] at hqpa
  exact hqpa

theorem bit_delta_201 (hm : 1 ≤ m) {ε δ p r η θ : ℕ}
    (hε : ε ≤ 1) (hδ : δ ≤ 1) (hη : η ≤ 1) (hθ : θ ≤ 1)
    (hX : xU201 D hBC hrel hdC hdB hL =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type201.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2)
    (hZ : zR201 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type201.k m) 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type201.k m) 2) :
    δ = η := by
  have h := rel_u_rho_of_type D hBC hdC (hL D.u_mem_L) (hL D.ρ_mem_L)
    (conj_eq_bU201 D hBC hrel hdC hdB hL) (conj_eq_bR201 D hBC hrel hdC hdB hL)
    (Type201.PhiU m) (Type201.PhiR m)
    (fun x => StrothTypeData.ec_conj_u_t201 D x)
    (fun x => StrothTypeData.ec_conj_ρ_t201 D x)
  change zR201 D hBC hrel hdC hdB hL +
      Type201.PhiR m (xU201 D hBC hrel hdC hdB hL) +
        Type201.PhiR m (Type201.PhiU m (zR201 D hBC hrel hdC hdB hL)) +
          Type201.PhiR m (Type201.PhiU m (Type201.PhiR m
            (xU201 D hBC hrel hdC hdB hL))) = 0 at h
  rw [hX, hZ, Type201.PhiR_apply_gens, Type201.PhiU_apply_gens,
    Type201.PhiR_apply_gens, Type201.PhiU_apply_gens, Type201.PhiR_apply_gens] at h
  have h1 := congrFun h 2
  simp [gen, Pi.single_apply, zsmul_eq_mul] at h1
  have hN2 : Type201.k m 2 - 1 = m + 1 := by rw [k201_two m]; omega
  have hNpos2 : 1 ≤ Type201.k m 2 := by rw [k201_two m]; omega
  have hpow0 : (2 : ZMod (2 ^ Type201.k m 2)) ^ m * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ Type201.k m 2)) = 2 ^ 2 by norm_num, ← pow_add]
    rw [show m + 2 = Type201.k m 2 by rw [k201_two m]]
    rw [show (2 : ZMod (2 ^ Type201.k m 2)) = ((2 : ℕ) : ZMod (2 ^ Type201.k m 2))
      by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
  have hpow08 : (2 : ZMod (2 ^ Type201.k m 2)) ^ m * 8 = 0 := by
    rw [show (8 : ZMod (2 ^ Type201.k m 2)) = 4 * 2 by norm_num, ← mul_assoc, hpow0, zero_mul]
  have hcast : ((((δ : ℤ) + (η : ℤ)) * 2 ^ (Type201.k m 2 - 1) : ℤ) :
      ZMod (2 ^ Type201.k m 2)) = 0 := by
    rw [hN2]
    push_cast at h1 ⊢
    linear_combination h1 +
      ((η : ZMod (2 ^ Type201.k m 2)) - (θ : ZMod (2 ^ Type201.k m 2))) * hpow0
  have he : Even ((δ : ℤ) + (η : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos2 hcast
  exact bit_eq_of_even_add hδ hη he

end Cross201

end CFSG.CGT.Stroth77
