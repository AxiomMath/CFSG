module

public import CFSG.CGT.Stroth77.Extension24
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

section SquareRoot

variable {τ : StrothTypeIndex}

theorem square_section_rho_Idx2R (D : StrothTypeData B τ) (x : ℤ) (hk : ∀ i, 1 ≤ τ.k i)
    (hρ0 : τ.action.φρ (gen τ.k 0) = gen τ.k 0)
    (hρ1 : τ.action.φρ (gen τ.k 1) = gen τ.k 2)
    (hρ2 : τ.action.φρ (gen τ.k 2) =
      x • gen τ.k 0 + (-1 : ℤ) • gen τ.k 1 + (-1 : ℤ) • gen τ.k 2)
    (y : B) (hr : SquareIn B ((conjBy D.ρ_mem y * y⁻¹ : B) : S)) :
    ∃ i : ℤ, SquareIn B ((y : S) * (D.c : S) ^ (-i)) := by
  classical
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens τ.k (D.ec y)
  have hmem : ((conjBy D.ρ_mem y * y⁻¹ : B) : S) ∈ B := (conjBy D.ρ_mem y * y⁻¹).2
  obtain ⟨z, hz⟩ := (isSquareInSubgroup_iff_even_of_type D hmem).1 hr
  have hz' : D.ec (conjBy D.ρ_mem y * y⁻¹) = 2 • z := hz
  have hmap : D.ec (conjBy D.ρ_mem y * y⁻¹) = Torus.ofInt τ.k ![x * l, -l - j, j - 2 * l] := by
    rw [D.ec_mul, D.ec_inv]
    have hc : D.ec (conjBy D.ρ_mem y) = τ.action.φρ (D.ec y) := D.ρ_conj y
    rw [hc, hy, Torus.ofInt_eq_zsmul_gens]
    simp only [map_add, map_zsmul, hρ0, hρ1, hρ2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    module
  have heven : ∀ t, Even (![x * l, -l - j, j - 2 * l] t) :=
    (Torus.exists_two_zsmul_eq_iff hk _).mp ⟨z, by rw [← hmap, hz', two_zsmul, two_nsmul]⟩
  have hj : Even j := by
    have h := heven 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
    have h2l : Even (2 * l) := ⟨l, by ring⟩
    have := Even.add h h2l
    simpa using this
  have hl : Even l := by
    have h := heven 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h
    have := Even.add h hj
    have h' : Even (-l) := by simpa using this
    exact even_neg.mp h'
  obtain ⟨j', hj'⟩ := hj
  obtain ⟨l', hl'⟩ := hl
  have hmem' : (y : S) * (D.c : S) ^ (-i) ∈ B := B.mul_mem y.2 (B.zpow_mem D.c.2 _)
  refine ⟨i, (isSquareInSubgroup_iff_even_of_type D hmem').2 ⟨j' • gen τ.k 1 + l' • gen τ.k 2, ?_⟩⟩
  have hsub : (⟨(y : S) * (D.c : S) ^ (-i), hmem'⟩ : B) = y * D.c ^ (-i) := rfl
  change D.ec (⟨(y : S) * (D.c : S) ^ (-i), hmem'⟩ : B) = _
  rw [hsub, D.ec_mul, D.ec_zpow, D.ec_c, hy, hj', hl']
  simp only [Torus.c]
  rw [two_nsmul]
  module

theorem exists_sq_eq_c_Idx2R (D : StrothTypeData B τ) (x : ℤ) (hk : ∀ i, 1 ≤ τ.k i)
    (hρ0 : τ.action.φρ (gen τ.k 0) = gen τ.k 0)
    (hρ1 : τ.action.φρ (gen τ.k 1) = gen τ.k 2)
    (hρ2 : τ.action.φρ (gen τ.k 2) =
      x • gen τ.k 0 + (-1 : ℤ) • gen τ.k 1 + (-1 : ℤ) • gen τ.k 2)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hρC : D.ρ ∈ Subgroup.normalizer C)
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
  obtain ⟨i, hi⟩ := square_section_rho_Idx2R D x hk hρ0 hρ1 hρ2 xB hr
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

end SquareRoot

section Basis

variable {τ : StrothTypeIndex}

theorem k_zero_eq_m_Idx2R (τ : StrothTypeIndex) : τ.k 0 = τ.m := by
  have h := congrFun (StrothTypeIndex.k_eq τ) 0
  simpa using h

theorem k_one_eq_n_Idx2R (τ : StrothTypeIndex) : τ.k 1 = τ.n := by
  have h := congrFun (StrothTypeIndex.k_eq τ) 1
  simpa using h

theorem exists_torusEquiv_Idx2R (D : StrothTypeData B τ) {k' : Fin 3 → ℕ}
    (hk0 : k' 0 = τ.k 0 + 1) (hk1 : k' 1 = τ.k 1) (hk2 : k' 2 = τ.k 2)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) :
    ∃ E : Torus k' ≃+ Additive C, E (gen k' 0) = Additive.ofMul ⟨d, hdC⟩ ∧
      E (gen k' 1) = Additive.ofMul ⟨D.a, hBC D.a.2⟩ ∧
      E (gen k' 2) = Additive.ofMul ⟨D.b, hBC D.b.2⟩ := by
  classical
  have hcomm : ∀ x y : C, x * y = y * x := comm_of_le_centralizer_of_type D hBC hC hrel
  let dC : C := ⟨d, hdC⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let bC : C := ⟨D.b, hBC D.b.2⟩
  let cC : C := ⟨D.c, hBC D.c.2⟩
  have hdd : dC * dC = cC := Subtype.ext hd2
  let x : Fin 3 → C := ![dC, aC, bC]
  have hcpow : cC ^ (2 ^ τ.k 0) = 1 := by
    apply Subtype.ext
    have h : D.c ^ (2 ^ τ.k 0) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_c, ← k_zero_eq_m_Idx2R]
    simpa [cC] using congrArg Subtype.val h
  have hapow : aC ^ (2 ^ τ.k 1) = 1 := by
    apply Subtype.ext
    have h : D.a ^ (2 ^ τ.k 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_a, ← k_one_eq_n_Idx2R]
    simpa [aC] using congrArg Subtype.val h
  have hbpow : bC ^ (2 ^ τ.k 2) = 1 := by
    apply Subtype.ext
    have h : D.b ^ (2 ^ τ.k 2) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_b, StrothTypeIndex.k_two]
    simpa [bC] using congrArg Subtype.val h
  have hx : ∀ i, x i ^ (2 ^ k' i) = 1 := by
    intro i
    fin_cases i
    · change dC ^ (2 ^ k' 0) = 1
      rw [hk0, pow_succ', pow_mul, sq, hdd, hcpow]
    · change aC ^ (2 ^ k' 1) = 1
      rw [hk1, hapow]
    · change bC ^ (2 ^ k' 2) = 1
      rw [hk2, hbpow]
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  let K := Subgroup.closure (Set.range x)
  have hdK : dC ∈ K := Subgroup.subset_closure ⟨0, rfl⟩
  have haK : aC ∈ K := Subgroup.subset_closure ⟨1, rfl⟩
  have hbK : bC ∈ K := Subgroup.subset_closure ⟨2, rfl⟩
  have hBK : ∀ y : C, (y : S) ∈ B → y ∈ K := by
    intro y hyB
    obtain ⟨i, j, l, hijl⟩ := torus_eq_zsmul_gens _ (D.ec ⟨y, hyB⟩)
    have hβ := eq_zpow_c_a_b_Idx4 D hijl
    have hyeq : y = (dC * dC) ^ i * aC ^ j * bC ^ l := by
      rw [hdd]
      apply Subtype.ext
      have h := congrArg Subtype.val hβ
      simpa [cC, aC, bC] using h
    rw [hyeq]
    exact K.mul_mem (K.mul_mem (K.zpow_mem (K.mul_mem hdK hdK) i) (K.zpow_mem haK j))
      (K.zpow_mem hbK l)
  have hgen : Subgroup.closure (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex y.2 with hyB | ⟨b, hbB, hyb⟩
    · exact hBK y hyB
    · have hy : y = dC * ⟨b, hBC hbB⟩ := Subtype.ext hyb
      rw [hy]
      exact K.mul_mem hdK (hBK _ hbB)
  have hcard : Nat.card (Torus k') = Nat.card C := by
    rw [natCard_torus, hrel, D.card, hk0, hk1, hk2]
    rw [show τ.k 0 + 1 + τ.k 1 + τ.k 2 = 1 + (τ.k 0 + τ.k 1 + τ.k 2) by ring, pow_add, pow_one]
  obtain ⟨E, hE⟩ := exists_torusEquiv_Idx4 hcomm x hx hgen hcard
  exact ⟨E, hE 0, hE 1, hE 2⟩

end Basis

section Transport

variable {τ : StrothTypeIndex} (D : StrothTypeData B τ) (hBC : B ≤ C) {k' : Fin 3 → ℕ}
  {d : S} (hdC : d ∈ C) (E : Torus k' ≃+ Additive C)
  (hE0 : E (gen k' 0) = Additive.ofMul ⟨d, hdC⟩)
  (hE1 : E (gen k' 1) = Additive.ofMul ⟨D.a, hBC D.a.2⟩)
  (hE2 : E (gen k' 2) = Additive.ofMul ⟨D.b, hBC D.b.2⟩) (hd2 : d * d = (D.c : S))

include hE0 hE1 hE2 hd2 in
theorem E_symm_incl_Idx2R (β : B) {i j l : ℤ}
    (h : D.ec β = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C)) =
      (2 * i) • gen k' 0 + j • gen k' 1 + l • gen k' 2 := by
  have hβ := eq_zpow_c_a_b_Idx4 D h
  have hβC : (⟨β, hBC β.2⟩ : C) =
      ((⟨d, hdC⟩ : C) * ⟨d, hdC⟩) ^ i * (⟨D.a, hBC D.a.2⟩ : C) ^ j *
        (⟨D.b, hBC D.b.2⟩ : C) ^ l := by
    apply Subtype.ext
    have h' := congrArg Subtype.val hβ
    simpa [hd2] using h'
  rw [AddEquiv.symm_apply_eq, hβC, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hE0, hE1,
    hE2, ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow, ofMul_mul, ← two_zsmul,
    smul_smul, mul_comm i 2]

include hE0 hE1 hE2 hd2 in
theorem alpha_incl_Idx2R {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (β : B) {i j l : ℤ}
    (h : D.ec (conjBy hgB β) = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    conjTorusIdx4 E hgC (E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C))) =
      (2 * i) • gen k' 0 + j • gen k' 1 + l • gen k' 2 := by
  rw [conjTorusIdx4_apply_symm]
  have hc : conjBy hgC (⟨β, hBC β.2⟩ : C) = ⟨conjBy hgB β, hBC (conjBy hgB β).2⟩ :=
    Subtype.ext rfl
  rw [hc]
  exact E_symm_incl_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 _ h

include hE0 hE1 hE2 hd2 in
theorem conjTorus_gen_Idx2R {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (M : IntMat) (hM : Compat τ.k M)
    (hconj : ∀ y : B, D.ec (conjBy hgB y) = matAct τ.k M hM (D.ec y)) :
    (2 : ℤ) • conjTorusIdx4 E hgC (gen k' 0) = Torus.ofInt k' ![2 * M 0 0, M 1 0, M 2 0] ∧
    conjTorusIdx4 E hgC (gen k' 1) = Torus.ofInt k' ![2 * M 0 1, M 1 1, M 2 1] ∧
    conjTorusIdx4 E hgC (gen k' 2) = Torus.ofInt k' ![2 * M 0 2, M 1 2, M 2 2] := by
  have hcol : ∀ (β : B) (j : Fin 3), D.ec β = gen τ.k j →
      conjTorusIdx4 E hgC (E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C))) =
        Torus.ofInt k' ![2 * M 0 j, M 1 j, M 2 j] := by
    intro β j hβ
    rw [alpha_incl_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 hgC hgB β (i := M 0 j) (j := M 1 j)
      (l := M 2 j) (by rw [hconj, hβ, matAct_gen_eq]), Torus.ofInt_eq_zsmul_gens]
    simp
  have hc : E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (2 : ℤ) • gen k' 0 := by
    rw [E_symm_incl_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 D.c (i := 1) (j := 0) (l := 0)
      (by rw [D.ec_c]; simp [Torus.c])]
    simp
  have ha : E.symm (Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C)) = gen k' 1 :=
    (AddEquiv.symm_apply_eq E).mpr hE1.symm
  have hb : E.symm (Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) = gen k' 2 :=
    (AddEquiv.symm_apply_eq E).mpr hE2.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_zsmul, ← hc]
    exact hcol D.c 0 D.ec_c
  · rw [← ha]
    exact hcol D.a 1 D.ec_a
  · rw [← hb]
    exact hcol D.b 2 D.ec_b

end Transport

section Coordinates

variable {k : Fin 3 → ℕ}

theorem gen_zero_eq_ofInt_Idx2R : gen k 0 = Torus.ofInt k ![1, 0, 0] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem gen_one_eq_ofInt_Idx2R : gen k 1 = Torus.ofInt k ![0, 1, 0] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem gen_two_eq_ofInt_Idx2R : gen k 2 = Torus.ofInt k ![0, 0, 1] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem endo_ofInt_Idx2R (X : Torus k →+ Torus k) {c0 c1 c2 : Fin 3 → ℤ}
    (h0 : X (gen k 0) = Torus.ofInt k c0) (h1 : X (gen k 1) = Torus.ofInt k c1)
    (h2 : X (gen k 2) = Torus.ofInt k c2) (v : Fin 3 → ℤ) :
    X (Torus.ofInt k v) = Torus.ofInt k (v 0 • c0 + v 1 • c1 + v 2 • c2) := by
  rw [Torus.ofInt_eq_zsmul_gens v, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1,
    h2, Torus.ofInt_add, Torus.ofInt_add, Torus.ofInt_zsmul, Torus.ofInt_zsmul,
    Torus.ofInt_zsmul]

theorem endo_ofInt_vec_Idx2R (X : Torus k →+ Torus k) {c0 c1 c2 : Fin 3 → ℤ}
    (h0 : X (gen k 0) = Torus.ofInt k c0) (h1 : X (gen k 1) = Torus.ofInt k c1)
    (h2 : X (gen k 2) = Torus.ofInt k c2) (v : Fin 3 → ℤ) :
    X (Torus.ofInt k v) = Torus.ofInt k ![v 0 * c0 0 + v 1 * c1 0 + v 2 * c2 0,
      v 0 * c0 1 + v 1 * c1 1 + v 2 * c2 1, v 0 * c0 2 + v 1 * c1 2 + v 2 * c2 2] := by
  rw [endo_ofInt_Idx2R X h0 h1 h2 v]
  congr 1
  funext i
  fin_cases i <;> simp

theorem exists_bits_Idx2R (hk : ∀ i, 1 ≤ k i) {y : Torus k} {h : Fin 3 → ℤ}
    (hy : (2 : ℤ) • y = Torus.ofInt k ((2 : ℤ) • h)) :
    ∃ e : Fin 3 → ℤ, (∀ i, e i = 0 ∨ e i = 1) ∧
      y = Torus.ofInt k (h + fun i => e i * 2 ^ (k i - 1)) := by
  have h2 : (2 : ℤ) • (y - Torus.ofInt k h) = 0 := by
    rw [smul_sub, hy, ← Torus.ofInt_zsmul, sub_self]
  obtain ⟨e, he, hye⟩ := (Torus.two_zsmul_eq_zero_iff hk _).mp h2
  refine ⟨e, he, ?_⟩
  rw [Torus.ofInt_add, ← hye]
  abel

theorem matAct_gen_ofInt_Idx2R (M : IntMat) (hM : Compat k M) (j : Fin 3) :
    matAct k M hM (gen k j) = Torus.ofInt k ![M 0 j, M 1 j, M 2 j] := by
  rw [matAct_gen_eq, Torus.ofInt_eq_zsmul_gens]
  simp

@[expose] noncomputable def shearHomIdx2R (k : Fin 3 → ℕ) (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) : Torus k →+ Torus k :=
  torusHomOfGens k ![gen k 0 + Torus.ofInt k zv, gen k 1, gen k 2] (by
    intro i
    fin_cases i
    · change (2 ^ k 0) • (gen k 0 + Torus.ofInt k zv) = 0
      rw [smul_add]
      have h1 : (2 ^ k 0) • gen k 0 = 0 := by
        rw [← addOrderOf_gen k 0]
        exact addOrderOf_nsmul_eq_zero _
      have h2 : (2 ^ k 0) • Torus.ofInt k zv = 0 := by
        obtain ⟨t, ht⟩ : ∃ t, k 0 = t + 1 := ⟨k 0 - 1, by omega⟩
        have hz' : (2 : ℕ) • Torus.ofInt k zv = 0 := by
          rw [← natCast_zsmul]
          exact_mod_cast hz
        rw [ht, pow_succ, mul_smul, hz', smul_zero]
      rw [h1, h2, add_zero]
    · change (2 ^ k 1) • gen k 1 = 0
      rw [← addOrderOf_gen k 1]
      exact addOrderOf_nsmul_eq_zero _
    · change (2 ^ k 2) • gen k 2 = 0
      rw [← addOrderOf_gen k 2]
      exact addOrderOf_nsmul_eq_zero _)

theorem shearHomIdx2R_gen0 (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) :
    shearHomIdx2R k hk0 zv hz (gen k 0) = Torus.ofInt k (![1, 0, 0] + zv) := by
  rw [shearHomIdx2R, torusHomOfGens_gen, Torus.ofInt_add, ← gen_zero_eq_ofInt_Idx2R]
  rfl

theorem shearHomIdx2R_gen1 (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) :
    shearHomIdx2R k hk0 zv hz (gen k 1) = Torus.ofInt k ![0, 1, 0] := by
  rw [shearHomIdx2R, torusHomOfGens_gen, ← gen_one_eq_ofInt_Idx2R]
  rfl

theorem shearHomIdx2R_gen2 (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) :
    shearHomIdx2R k hk0 zv hz (gen k 2) = Torus.ofInt k ![0, 0, 1] := by
  rw [shearHomIdx2R, torusHomOfGens_gen, ← gen_two_eq_ofInt_Idx2R]
  rfl

theorem shearHomIdx2R_ofInt (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) (v : Fin 3 → ℤ) :
    shearHomIdx2R k hk0 zv hz (Torus.ofInt k v) = Torus.ofInt k (v + v 0 • zv) := by
  rw [endo_ofInt_Idx2R _ (shearHomIdx2R_gen0 hk0 zv hz) (shearHomIdx2R_gen1 hk0 zv hz)
    (shearHomIdx2R_gen2 hk0 zv hz)]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring

theorem shearHomIdx2R_involutive (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) (hz0 : Even (zv 0)) (x : Torus k) :
    shearHomIdx2R k hk0 zv hz (shearHomIdx2R k hk0 zv hz x) = x := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [shearHomIdx2R_ofInt, shearHomIdx2R_ofInt]
  obtain ⟨w, hw⟩ := hz0
  have e : (v + v 0 • zv) + (v + v 0 • zv) 0 • zv = v + ((v 0 + v 0 * w) * 2) • zv := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw]
    ring
  rw [e, Torus.ofInt_add, Torus.ofInt_zsmul, mul_smul, hz, smul_zero, add_zero]

@[expose] noncomputable def shearIdx2R (k : Fin 3 → ℕ) (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) (hz0 : Even (zv 0)) : Torus k ≃+ Torus k where
  toFun := shearHomIdx2R k hk0 zv hz
  invFun := shearHomIdx2R k hk0 zv hz
  left_inv := shearHomIdx2R_involutive hk0 zv hz hz0
  right_inv := shearHomIdx2R_involutive hk0 zv hz hz0
  map_add' := map_add _

theorem conjTorusIdx4_shear_Idx2R (hk0 : 1 ≤ k 0) (zv : Fin 3 → ℤ)
    (hz : (2 : ℤ) • Torus.ofInt k zv = 0) (hz0 : Even (zv 0)) (E : Torus k ≃+ Additive C)
    {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus k) :
    conjTorusIdx4 ((shearIdx2R k hk0 zv hz hz0).trans E) hg x =
      shearHomIdx2R k hk0 zv hz (conjTorusIdx4 E hg (shearHomIdx2R k hk0 zv hz x)) :=
  rfl

end Coordinates

theorem eq_two_of_u_Idx2R {k' : Fin 3 → ℕ} {m n : ℕ} (hk0 : k' 0 = m + 1) (hk1 : k' 1 = n)
    (hk2 : k' 2 = n) (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (U : Torus k' →+ Torus k')
    (hUU : U (U (gen k' 0)) = gen k' 0) (κ κ' : ℤ)
    (hU0 : (2 : ℤ) • U (gen k' 0) = Torus.ofInt k' ![2 + 2 ^ m, 0, 0])
    (hU1 : U (gen k' 1) = Torus.ofInt k' ![2 * κ, 0, 1])
    (hU2 : U (gen k' 2) = Torus.ofInt k' ![2 * κ', 1, 0]) : m = 2 := by
  obtain ⟨v, hv⟩ := Torus.exists_ofInt (U (gen k' 0))
  rw [← hv, ← Torus.ofInt_zsmul, Torus.ofInt_eq_ofInt_iff] at hU0
  have hUv := endo_ofInt_Idx2R U hv.symm hU1 hU2 v
  rw [← hv, hUv, gen_zero_eq_ofInt_Idx2R, Torus.ofInt_eq_ofInt_iff] at hUU
  have h00 := hU0 0
  have h01 := hU0 1
  have h02 := hU0 2
  have hc := hUU 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hk0, hk1, hk2] at h00 h01 h02 hc
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = s + 3 + r := ⟨n - (s + 3), by omega⟩
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = 2 ^ s := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [hP]; positivity
  have p2 : (2 : ℤ) ^ (s + 2) = 4 * P := by rw [hP, pow_add]; ring
  have p3 : (2 : ℤ) ^ (s + 2 + 1) = 8 * P := by rw [hP, pow_add]; ring
  have pn : (2 : ℤ) ^ (s + 3 + r) = 8 * P * 2 ^ r := by rw [hP, pow_add, pow_add]; ring
  rw [Int.modEq_iff_dvd] at h00 h01 h02 hc
  rw [p2, p3] at h00
  rw [pn] at h01 h02
  rw [p3] at hc
  obtain ⟨e0, he0⟩ := h00
  obtain ⟨e1, he1⟩ := h01
  obtain ⟨e2, he2⟩ := h02
  obtain ⟨f, hf⟩ := hc
  have hv0 : v 0 = 1 + 2 * P - 4 * P * e0 := by linarith
  have hv1 : v 1 = -(4 * P * 2 ^ r * e1) := by linarith
  have hv2 : v 2 = -(4 * P * 2 ^ r * e2) := by linarith
  rw [hv0, hv1, hv2] at hf
  have key : 4 * P * (1 + P) = 4 * P * (2 * (-f + e0 + 2 * P * e0 - 2 * P * e0 ^ 2 +
      2 ^ r * e1 * κ + 2 ^ r * e2 * κ')) := by
    linear_combination (-1 : ℤ) * hf
  have h4P : (4 * P) ≠ 0 := by omega
  have hodd := mul_left_cancel₀ h4P key
  rcases s with _ | s
  · rfl
  · exfalso
    have hP2 : P = 2 * 2 ^ s := by rw [hP, pow_succ]; ring
    have h2 : (1 + P) % 2 = 0 := by rw [hodd]; exact Int.mul_emod_right 2 _
    rw [hP2, Int.add_mul_emod_self_left] at h2
    norm_num at h2

end CFSG.CGT.Stroth77
