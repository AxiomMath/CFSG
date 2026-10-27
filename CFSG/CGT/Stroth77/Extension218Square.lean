module

public import CFSG.CGT.Stroth77.Extension23

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S]

private theorem square_section_of_rho {τ : StrothTypeIndex} {B : Subgroup S}
    (D : StrothTypeData B τ) (e : ℤ) (hk1 : 1 ≤ τ.k 1) (hk2 : 1 ≤ τ.k 2)
    (hρ : ∀ i j l : ℤ, τ.action.φρ (i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) =
      (i + e * l) • gen τ.k 0 + (-l) • gen τ.k 1 + (j - l) • gen τ.k 2)
    (x : B) (hr : SquareIn B ((conjBy D.ρ_mem x * x⁻¹ : B) : S)) :
    ∃ i : ℤ, SquareIn B ((x : S) * (D.c : S) ^ (-i)) := by
  classical
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens τ.k (D.ec x)
  have hmemr : ((conjBy D.ρ_mem x * x⁻¹ : B) : S) ∈ B := (conjBy D.ρ_mem x * x⁻¹).2
  obtain ⟨zr, hzr⟩ := (isSquareInSubgroup_iff_even_of_type D hmemr).1 hr
  have hmap : D.e (Additive.ofMul (⟨((conjBy D.ρ_mem x * x⁻¹ : B) : S), hmemr⟩ : B)) =
      τ.action.φρ (D.ec x) - D.ec x := by
    have h1 : (⟨((conjBy D.ρ_mem x * x⁻¹ : B) : S), hmemr⟩ : B) = conjBy D.ρ_mem x * x⁻¹ := rfl
    rw [h1, ofMul_mul, ofMul_inv, map_add, map_neg, D.ρ_conj x, sub_eq_add_neg]
    rfl
  have hz : τ.action.φρ (D.ec x) - D.ec x = 2 • zr := hmap.symm.trans hzr
  rw [hy, hρ] at hz
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  have hg01 : (gen τ.k 0) 1 = 0 := Pi.single_eq_of_ne (by decide) _
  have hg11 : (gen τ.k 1) 1 = 1 := Pi.single_eq_same _ _
  have hg21 : (gen τ.k 2) 1 = 0 := Pi.single_eq_of_ne (by decide) _
  have hg02 : (gen τ.k 0) 2 = 0 := Pi.single_eq_of_ne (by decide) _
  have hg12 : (gen τ.k 1) 2 = 0 := Pi.single_eq_of_ne (by decide) _
  have hg22 : (gen τ.k 2) 2 = 1 := Pi.single_eq_same _ _
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at h1 h2
  rw [hg01, hg11, hg21] at h1
  rw [hg02, hg12, hg22] at h2
  simp only [smul_zero, zsmul_eq_mul, mul_one, zero_add, add_zero, nsmul_eq_mul,
    Nat.cast_ofNat] at h1 h2
  have h1' : (((-l - j : ℤ)) : ZMod (2 ^ τ.k 1)) = 2 * zr 1 := by
    rw [← h1]
    push_cast
    ring
  have h2' : (((j - 2 * l : ℤ)) : ZMod (2 ^ τ.k 2)) = 2 * zr 2 := by
    rw [← h2]
    push_cast
    ring
  have he1 : Even (-l - j) := even_of_intCast_eq_two_mul hk1 h1'
  have he2 : Even (j - 2 * l) := even_of_intCast_eq_two_mul hk2 h2'
  have hj : Even j := by
    have h2l : Even (2 * l) := ⟨l, by ring⟩
    exact (Int.even_sub.mp he2).mpr h2l
  have hl : Even l := by
    have hjl : Even (l + j) := by
      have := he1.neg
      rwa [show -(-l - j) = l + j by ring] at this
    exact (Int.even_add.mp hjl).mpr hj
  obtain ⟨j', hj'⟩ := hj
  obtain ⟨l', hl'⟩ := hl
  have hmem : (x : S) * (D.c : S) ^ (-i) ∈ B := B.mul_mem x.2 (B.zpow_mem D.c.2 _)
  refine ⟨i, (isSquareInSubgroup_iff_even_of_type D hmem).2 ⟨j' • gen τ.k 1 + l' • gen τ.k 2, ?_⟩⟩
  have hsub : (⟨(x : S) * (D.c : S) ^ (-i), hmem⟩ : B) = x * D.c ^ (-i) := rfl
  rw [hsub]
  change D.ec (x * D.c ^ (-i)) = _
  rw [D.ec_mul, D.ec_zpow, D.ec_c, hy, hj', hl', two_nsmul]
  simp only [Torus.c]
  module

private theorem exists_square_root_c_of_section {τ : StrothTypeIndex} {B C S' : Subgroup S}
    (D : StrothTypeData B τ)
    (hsec : ∀ x : B, SquareIn B ((conjBy D.ρ_mem x * x⁻¹ : B) : S) →
      ∃ i : ℤ, SquareIn B ((x : S) * (D.c : S) ^ (-i)))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hρC : D.ρ ∈ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) := by
  classical
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  have hlt : B < C := lt_of_relIndex hBC hrel
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
    have hzB : (zC : S) ∉ B := by
      intro hz
      have hd_eq : dC = zC * bC := by
        simp [zC, dC, bC]
      have hmem : dC ∈ B.subgroupOf C := by
        rw [hd_eq]
        exact (B.subgroupOf C).mul_mem (by simpa [Subgroup.mem_subgroupOf] using hz)
          (by simpa [Subgroup.mem_subgroupOf, bC] using b.2)
      exact hdB (by simpa [Subgroup.mem_subgroupOf] using hmem)
    exact hzB (hH (zC : S) (hCS zC.2) hz2 (hC zC.2))
  have hr : SquareIn B ((conjBy D.ρ_mem xB * xB⁻¹ : B) : S) := by
    have hconjC : D.ρ⁻¹ * d * D.ρ ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp hρC d).mp hdC
    have hconjB : D.ρ⁻¹ * d * D.ρ ∉ B := by
      intro hconj
      exact hdB ((Subgroup.mem_normalizer_iff''.mp D.ρ_mem d).mpr hconj)
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex hconjC with hconjBinB | ⟨b, hbB, hb_eq⟩
    · exact (hconjB hconjBinB).elim
    let bB : B := ⟨b, hbB⟩
    let bC : C := ⟨b, hBC hbB⟩
    let xC : C := ⟨(xB : S), hBC xB.2⟩
    have hxC : xC = dC * dC := by
      apply Subtype.ext
      simp [xC, dC, xB]
    have hconj_eq : conjBy hρC dC = dC * bC := by
      apply Subtype.ext
      change D.ρ⁻¹ * d * D.ρ = d * b
      exact hb_eq
    refine ⟨bB, ?_⟩
    have hcoerce : ((conjBy D.ρ_mem xB * xB⁻¹ : B) : S) =
        ((conjBy hρC xC * xC⁻¹ : C) : S) := rfl
    rw [hcoerce]
    change (bC : S) * (bC : S) = ((conjBy hρC xC * xC⁻¹ : C) : S)
    have hCeq : conjBy hρC xC * xC⁻¹ = bC * bC := by
      have hconj_sq : conjBy hρC xC = conjBy hρC dC * conjBy hρC dC := by
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
  obtain ⟨i, hi⟩ := hsec xB hr
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

theorem rho_apply_gens_t221 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t221 s hs).action.φρ
        (i • gen (StrothTypeIndex.t221 s hs).k 0 + j • gen (StrothTypeIndex.t221 s hs).k 1 +
          l • gen (StrothTypeIndex.t221 s hs).k 2) =
      (i + (-1) * l) • gen (StrothTypeIndex.t221 s hs).k 0 +
        (-l) • gen (StrothTypeIndex.t221 s hs).k 1 +
        (j - l) • gen (StrothTypeIndex.t221 s hs).k 2 := by
  change matAct (Type221.k s) Type221.ρM (Type221.compat_rho (Type221.data s))
      (i • gen (Type221.k s) 0 + j • gen (Type221.k s) 1 + l • gen (Type221.k s) 2) =
    (i + (-1) * l) • gen (Type221.k s) 0 + (-l) • gen (Type221.k s) 1 +
      (j - l) • gen (Type221.k s) 2
  rw [matAct_zsmul_gens]
  have h00 : Type221.ρM 0 0 = 1 := by decide
  have h01 : Type221.ρM 0 1 = 0 := by decide
  have h02 : Type221.ρM 0 2 = -1 := by decide
  have h10 : Type221.ρM 1 0 = 0 := by decide
  have h11 : Type221.ρM 1 1 = 0 := by decide
  have h12 : Type221.ρM 1 2 = -1 := by decide
  have h20 : Type221.ρM 2 0 = 0 := by decide
  have h21 : Type221.ρM 2 1 = 1 := by decide
  have h22 : Type221.ρM 2 2 = -1 := by decide
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  congr 2 <;> ring_nf

theorem square_section_t221 {s : ℕ} {hs : 1 ≤ s} {B : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t221 s hs)) (x : B)
    (hr : SquareIn B ((conjBy D.ρ_mem x * x⁻¹ : B) : S)) :
    ∃ i : ℤ, SquareIn B ((x : S) * (D.c : S) ^ (-i)) :=
  square_section_of_rho D (-1) (by change 1 ≤ s + 4; omega) (by change 1 ≤ s + 4; omega)
    (rho_apply_gens_t221 s hs) x hr

theorem exists_square_root_c_t221 {s : ℕ} {hs : 1 ≤ s} {B C S' : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hρC : D.ρ ∈ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) :=
  exists_square_root_c_of_section D (square_section_t221 D) hBC hC hrel hρC hH hCS

theorem rho_apply_gens_t131 (m : ℕ) (hm : 3 ≤ m) (i j l : ℤ) :
    (StrothTypeIndex.t131 m hm).action.φρ
        (i • gen (StrothTypeIndex.t131 m hm).k 0 + j • gen (StrothTypeIndex.t131 m hm).k 1 +
          l • gen (StrothTypeIndex.t131 m hm).k 2) =
      (i + (-2) * l) • gen (StrothTypeIndex.t131 m hm).k 0 +
        (-l) • gen (StrothTypeIndex.t131 m hm).k 1 +
        (j - l) • gen (StrothTypeIndex.t131 m hm).k 2 := by
  change matAct (Type131.k m) Type131.ρM (Type131.compat_rho (Type131.data m (by omega)))
      (i • gen (Type131.k m) 0 + j • gen (Type131.k m) 1 + l • gen (Type131.k m) 2) =
    (i + (-2) * l) • gen (Type131.k m) 0 + (-l) • gen (Type131.k m) 1 +
      (j - l) • gen (Type131.k m) 2
  rw [matAct_zsmul_gens]
  have h00 : Type131.ρM 0 0 = 1 := by decide
  have h01 : Type131.ρM 0 1 = 0 := by decide
  have h02 : Type131.ρM 0 2 = -2 := by decide
  have h10 : Type131.ρM 1 0 = 0 := by decide
  have h11 : Type131.ρM 1 1 = 0 := by decide
  have h12 : Type131.ρM 1 2 = -1 := by decide
  have h20 : Type131.ρM 2 0 = 0 := by decide
  have h21 : Type131.ρM 2 1 = 1 := by decide
  have h22 : Type131.ρM 2 2 = -1 := by decide
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  congr 2 <;> ring_nf

theorem square_section_t131 {m : ℕ} {hm : 3 ≤ m} {B : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t131 m hm)) (x : B)
    (hr : SquareIn B ((conjBy D.ρ_mem x * x⁻¹ : B) : S)) :
    ∃ i : ℤ, SquareIn B ((x : S) * (D.c : S) ^ (-i)) :=
  square_section_of_rho D (-2) (by change 1 ≤ m + 1; omega) (by change 1 ≤ m + 1; omega)
    (rho_apply_gens_t131 m hm) x hr

theorem exists_square_root_c_t131 {m : ℕ} {hm : 3 ≤ m} {B C S' : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t131 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hρC : D.ρ ∈ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) :=
  exists_square_root_c_of_section D (square_section_t131 D) hBC hC hrel hρC hH hCS

end CFSG.CGT.Stroth77
