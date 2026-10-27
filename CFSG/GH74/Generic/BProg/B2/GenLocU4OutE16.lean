module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrame
import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMu

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank Subgroup Matrix

namespace GenLocU4OutE16

open GenLocU4Basic GenLocL4Out

variable {K : Type} [Field K] {p f : ℕ}

theorem mm_map (hq : Odd (p ^ f)) (i : Fin 4) :
    (mm i : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = mm i := by
  have hp0 : p ^ f ≠ 0 := by
    intro h0; rw [h0] at hq; exact (Nat.not_odd_zero hq)
  have h0 : ((0 : K) ^ (p ^ f)) = 0 := zero_pow hp0
  have hm : ((-1 : K) ^ (p ^ f)) = -1 := hq.neg_one_pow
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [mm, m1, m2, m3, m4, h0, hm]

theorem mm_unitary (hq : Odd (p ^ f)) (i : Fin 4) :
    ((mm i : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (mm i : Matrix (Fin 4) (Fin 4) K) = 1 := by
  rw [mm_map hq]
  fin_cases i
  · show m1ᵀ * m1 = 1
    rw [m1_t, Matrix.neg_mul, m1_sq, neg_neg]
  · show m2ᵀ * m2 = 1
    rw [m2_t, m2_sq]
  · show m3ᵀ * m3 = 1
    rw [m3_t, Matrix.neg_mul, m3_sq, neg_neg]
  · show m4ᵀ * m4 = 1
    rw [m4_t, m4_sq]

omit [Field K] in
theorem det_ne_zero_mm {K : Type} [Field K] (i : Fin 4) : (mm i : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
  rw [det_mm]; exact one_ne_zero

@[expose] noncomputable def pauliJ (hq : Odd (p ^ f)) (i : Fin 4) : ↥(StatedSU 4 (p ^ f) K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mm i) (det_ne_zero_mm i),
    Subgroup.subset_closure ⟨det_mm i, mm_unitary hq i⟩⟩

theorem coe_pauliJ (hq : Odd (p ^ f)) (i : Fin 4) :
    (((pauliJ hq i : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = mm i := rfl

@[expose] noncomputable def zJ (hq : Odd (p ^ f)) : ↥(StatedSU 4 (p ^ f) K) := pauliJ hq 0 * pauliJ hq 0

theorem coe_zJ (hq : Odd (p ^ f)) :
    (((zJ hq : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
  show ((pauliJ hq 0 * pauliJ hq 0 : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K).val = _
  rw [Subgroup.coe_mul, Units.val_mul]
  exact m1_sq

theorem zJ_central (hq : Odd (p ^ f)) : zJ hq ∈ Subgroup.center ↥(StatedSU 4 (p ^ f) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_zJ]
  simp

theorem zJ_mul_self (hq : Odd (p ^ f)) : zJ hq * zJ hq = (1 : ↥(StatedSU 4 (p ^ f) K)) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_zJ]
  simp

theorem zJ_ne_one (hq : Odd (p ^ f)) (h2 : (2 : K) ≠ 0) : zJ hq ≠ (1 : ↥(StatedSU 4 (p ^ f) K)) := by
  intro h
  have := congrArg (fun x : ↥(StatedSU 4 (p ^ f) K) => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h
  simp only [coe_zJ] at this
  simp at this
  apply h2
  linear_combination -this

theorem ext_J {g g' : ↥(StatedSU 4 (p ^ f) K)}
    (h : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    g = g' := Subtype.ext (Units.ext h)

theorem pauli_sq (hq : Odd (p ^ f)) (i : Fin 4) :
    pauliJ (K := K) hq i * pauliJ hq i = (1 : ↥(StatedSU 4 (p ^ f) K)) ∨ pauliJ (K := K) hq i * pauliJ hq i = zJ hq := by
  fin_cases i
  · right; rfl
  · left
    apply ext_J
    rw [Subgroup.coe_mul, Units.val_mul]
    exact m2_sq
  · right
    apply ext_J
    rw [Subgroup.coe_mul, Units.val_mul, coe_zJ]
    exact m3_sq
  · left
    apply ext_J
    rw [Subgroup.coe_mul, Units.val_mul]
    exact m4_sq

theorem pauli_anti (hq : Odd (p ^ f)) {i j : Fin 4} (hij : (mm i : Matrix (Fin 4) (Fin 4) K) * mm j = -(mm j * mm i)) :
    pauliJ (K := K) hq i * pauliJ hq j = zJ hq * (pauliJ hq j * pauliJ hq i) := by
  apply ext_J
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Units.val_mul, coe_zJ]
  rw [coe_pauliJ (K := K), coe_pauliJ (K := K), hij]
  simp

theorem pauli_comm (hq : Odd (p ^ f)) {i j : Fin 4} (hij : (mm i : Matrix (Fin 4) (Fin 4) K) * mm j = mm j * mm i) :
    pauliJ (K := K) hq i * pauliJ hq j = pauliJ hq j * pauliJ hq i := by
  apply ext_J
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_pauliJ (K := K), coe_pauliJ (K := K)]
  exact hij

theorem not_sectional_of_E16' {J : Type} [Group J] [Finite J] {A : Type} [Group A] [Finite A]
    (α : A →* MulAut J) (a : A) (haa : α a * α a = 1)
    (hu : α a ∉ (MulAut.conj : J →* MulAut J).range) (V : Subgroup (MulAut J))
    (hVinn : V ≤ (MulAut.conj : J →* MulAut J).range) (hVea : CFSG.IsElementaryAbelian 2 ↥V)
    (hVcard : 16 ≤ Nat.card ↥V) (hcomm : ∀ φ ∈ V, α a * φ = φ * α a) :
    ¬ SectionalTwoRankLE ↥(innJoin α) 4 := by
  intro hsec
  set W : Subgroup (MulAut J) := GenLocL5Gen.adjoinInvolution V (α a) haa hcomm with hWdef
  have hWea : CFSG.IsElementaryAbelian 2 ↥W := GenLocL5Gen.isEA_adjoin hVea
  have hWinn : W ≤ innJoin α := by
    intro x hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Subgroup.mem_sup_left (hVinn hx)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hVinn hy))
        (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hEW : V < W := by
    refine lt_of_le_of_ne (fun x hx => GenLocL5Gen.mem_adjoin_of_mem hx) fun hEq => ?_
    have : α a ∈ V := by rw [hEq]; exact GenLocL5Gen.u_mem_adjoin
    exact hu (hVinn this)
  have hcardW : 32 ≤ Nat.card ↥W := by
    have h1 := Subgroup.card_lt_of_lt hEW
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEW.le
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> simp at hk <;> omega
    calc 32 = 16 * 2 := by norm_num
      _ ≤ Nat.card ↥V * k := Nat.mul_le_mul hVcard hk2
      _ = Nat.card ↥W := hk.symm
  let W' : Subgroup ↥(innJoin α) := W.subgroupOf (innJoin α)
  have hW'card : Nat.card ↥W' = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWinn).toEquiv
  have hW'ea : CFSG.IsElementaryAbelian 2 ↥W' := by
    refine WeakSigGen.isElementaryAbelian_of_forall (G := ↥(innJoin α)) (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : MulAut J)) (mul_comm' (⟨x.1, hx⟩ : W) ⟨y.1, hy⟩)
    · apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : MulAut J))
        (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hWea (⟨x.1, hx⟩ : W))
  have hbound := hsec.card_le_of_elementary W'
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 W').1 hW'ea)
  omega

section Key

open CFSG.GH74.Generic.S1.Uni CFSG.LocalAnalysis.ComponentInitial

variable (h : UnitaryFieldData p f K)

theorem map_mm (hq : Odd (p ^ f)) (i : Fin 4) : (mm i : Matrix (Fin 4) (Fin 4) K).map h.bar = mm i := by
  have := mm_map (K := K) hq i
  rw [GenLocU4Basic.bar_eq_pow h]
  exact this

theorem map_cT (P : Matrix (Fin 4) (Fin 4) K) : (cT h P).map h.bar = Pᵀ := by
  rw [cT, Matrix.transpose_map, map_bar_bar h]

theorem Pt_Pbar {P : Matrix (Fin 4) (Fin 4) K} (hP : cT h P * P = 1) : Pᵀ * P.map h.bar = 1 := by
  have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) hP
  simp only [Matrix.map_mul, map_cT h] at this
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem graph_pauli (hq : Odd (p ^ f)) {P N B : Matrix (Fin 4) (Fin 4) K} (hP : cT h P * P = 1)
    (hBN : B = P * N * Pᵀ) (i : Fin 4) :
    B * (P * mm i * cT h P).map h.bar = P * (N * mm i) * Pᵀ ∧
      (P * mm i * cT h P) * B = P * (mm i * N) * Pᵀ := by
  constructor
  · rw [Matrix.map_mul, Matrix.map_mul, map_mm h hq i, map_cT h, hBN]
    have := Pt_Pbar h hP
    calc P * N * Pᵀ * (P.map h.bar * mm i * Pᵀ) = P * N * (Pᵀ * P.map h.bar) * mm i * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [this, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  · rw [hBN]
    calc P * mm i * cT h P * (P * N * Pᵀ) = P * mm i * (cT h P * P) * N * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]; simp only [Matrix.mul_assoc]

end Key

section Frame

open CFSG.GH74.Generic.S1.Uni CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel

variable (h : UnitaryFieldData p f K)

theorem mem_pfu {P : GL (Fin 4) K}
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) :
    P ∈ primeFormUnitary h (idGram K 4) := by
  rw [mem_primeFormUnitary]
  have hb : ((P : Matrix (Fin 4) (Fin 4) K).map h.bar) = (P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) := rfl
  rw [hb]
  simpa [idGram] using hP

@[expose] noncomputable def gP (hq : Odd (p ^ f)) {P : GL (Fin 4) K}
    (hP : IsUnitaryU (p ^ f) (P : Matrix (Fin 4) (Fin 4) K)) (i : Fin 4) : ↥(StatedSU 4 (p ^ f) K) :=
  GenLocDiagU.conjSUHom h 4 ⟨P, mem_pfu h hP⟩ (pauliJ hq i)

theorem coe_gP (hq : Odd (p ^ f)) {P : GL (Fin 4) K} (hP : IsUnitaryU (p ^ f) (P : Matrix (Fin 4) (Fin 4) K))
    (i : Fin 4) :
    (((gP h hq hP i : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * mm i * cT h (P : Matrix (Fin 4) (Fin 4) K) := by
  have e : (((gP h hq hP i : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * mm i * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [gP, GenLocDiagU.coe_conjSUHom, Units.val_mul, Units.val_mul]
    rfl
  rw [e, GenLocU4Basic.inv_coe_of_isUnitaryU hP, cT, GenLocU4Basic.bar_eq_pow h]

theorem cancel_of_unitary {q : ℕ} {B X Y : Matrix (Fin 4) (Fin 4) K} (hB : IsUnitaryU q B)
    (hXY : X * B = Y * B) : X = Y := by
  have h1 : B * (B.map (· ^ q))ᵀ = 1 := mul_eq_one_comm.mp hB
  calc X = X * (B * (B.map (· ^ q))ᵀ) := by rw [h1, Matrix.mul_one]
    _ = (X * B) * (B.map (· ^ q))ᵀ := by rw [Matrix.mul_assoc]
    _ = (Y * B) * (B.map (· ^ q))ᵀ := by rw [hXY]
    _ = Y := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end Frame

section Main

open CFSG.GH74.Generic.S1.Uni CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel

theorem not_sectional_of_pauli_form [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (a : A) (haa : α a * α a = 1)
    (hnin : α a ∉ (MulAut.conj : ↥(StatedSU 4 (p ^ f) K) →* MulAut ↥(StatedSU 4 (p ^ f) K)).range)
    {P : GL (Fin 4) K} {B N : Matrix (Fin 4) (Fin 4) K}
    (hP : IsUnitaryU (p ^ f) (P : Matrix (Fin 4) (Fin 4) K))
    (hBN : B = (P : Matrix (Fin 4) (Fin 4) K) * N * (P : Matrix (Fin 4) (Fin 4) K)ᵀ)
    (hBU : IsUnitaryU (p ^ f) B)
    (hu : ∀ g : ↥(StatedSU 4 (p ^ f) K),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B =
        B * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))
    (hN : ∀ i, N * mm i = mm i * N ∨ N * mm i = -(mm i * N)) :
    ¬ SectionalTwoRankLE ↥(innJoin α) 4 := by
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hPc : cT h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 :=
    (GenLocU4OutFrame.isUnitaryU_iff_cT h _).1 hP
  have hPc' : (P : Matrix (Fin 4) (Fin 4) K) * cT h (P : Matrix (Fin 4) (Fin 4) K) = 1 := mul_eq_one_comm.mp hPc
  set φ := GenLocDiagU.conjSUHom h 4 ⟨P, mem_pfu h hP⟩ with hφ
  have hφz : φ (zJ hq) = zJ hq := by
    apply ext_J
    rw [hφ, GenLocDiagU.coe_conjSUHom, Units.val_mul, Units.val_mul, coe_zJ,
      GenLocU4Basic.inv_coe_of_isUnitaryU hP]
    show (P : Matrix (Fin 4) (Fin 4) K) * (-1) * (((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ) = -1
    have : (((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ) = cT h (P : Matrix (Fin 4) (Fin 4) K) := by
      rw [cT, GenLocU4Basic.bar_eq_pow h]
    rw [this, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hPc']
  have hg : ∀ i, gP h hq hP i = φ (pauliJ hq i) := fun i => rfl
  have hsq : ∀ i, gP h hq hP i * gP h hq hP i = 1 ∨ gP h hq hP i * gP h hq hP i = zJ hq := by
    intro i
    rcases pauli_sq (K := K) hq i with h1 | h1
    · left
      rw [hg, ← map_mul, h1, map_one]
    · right
      rw [hg, ← map_mul, h1, hφz]
  have hanti : ∀ {i j : Fin 4}, (mm i : Matrix (Fin 4) (Fin 4) K) * mm j = -(mm j * mm i) →
      gP h hq hP i * gP h hq hP j = zJ hq * (gP h hq hP j * gP h hq hP i) := by
    intro i j hij
    have := congrArg φ (pauli_anti (K := K) hq hij)
    simpa only [map_mul, hφz, hg] using this
  have hcomm : ∀ {i j : Fin 4}, (mm i : Matrix (Fin 4) (Fin 4) K) * mm j = mm j * mm i →
      gP h hq hP i * gP h hq hP j = gP h hq hP j * gP h hq hP i := by
    intro i j hij
    have := congrArg φ (pauli_comm (K := K) hq hij)
    simpa only [map_mul, hg] using this
  obtain ⟨V, hVinn, hVea, hVcard, hVcomm⟩ := GenLocL4Out.exists_E16 (zJ_central hq) (zJ_mul_self hq)
    (zJ_ne_one hq h2) (gP h hq hP) hsq (hanti m12) (hanti m34) (hcomm m13) (hcomm m14) (hcomm m23) (hcomm m24)
  refine not_sectional_of_E16' α a haa hnin V hVinn hVea hVcard (hVcomm (α a) fun i => ?_)
  have hi := graph_pauli h hq hPc hBN i
  have hXB := hu (gP h hq hP i)
  rw [coe_gP h hq hP i, ← GenLocU4Basic.bar_eq_pow h] at hXB
  rw [hi.1] at hXB
  have hYB : (((gP h hq hP i : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B =
      (P : Matrix (Fin 4) (Fin 4) K) * (mm i * N) * (P : Matrix (Fin 4) (Fin 4) K)ᵀ := by
    rw [coe_gP h hq hP i]; exact hi.2
  rcases hN i with hNi | hNi
  · left
    apply ext_J
    apply cancel_of_unitary hBU
    rw [hXB, hYB, hNi]
  · right
    apply ext_J
    apply cancel_of_unitary hBU
    have e : (((zJ hq * gP h hq hP i : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B =
        -((P : Matrix (Fin 4) (Fin 4) K) * (mm i * N) * (P : Matrix (Fin 4) (Fin 4) K)ᵀ) := by
      rw [Subgroup.coe_mul, Units.val_mul, coe_zJ]
      simp only [Matrix.neg_mul, Matrix.one_mul]
      rw [hYB]
    rw [hXB, e, hNi, Matrix.mul_neg, Matrix.neg_mul]

end Main

section NotInner

theorem exists_unit_scalar_sq_ne_one [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (h3 : 3 ≤ p ^ f) :
    ∃ ε : K, ε ^ (p ^ f) * ε = 1 ∧ ε * ε ≠ 1 := by
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hq1 : 1 ≤ p ^ f := by omega
  have hprod : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring
  have hu1 : (g ^ (p ^ f - 1)) ^ (p ^ f + 1) = 1 := by
    rw [← pow_mul, hprod, ← hord, pow_orderOf_eq_one]
  have hu2 : (g ^ (p ^ f - 1)) ^ 2 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by omega) hd
    have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := hprod.symm
    rw [this] at hle
    have h4 : 0 < p ^ f - 1 := by omega
    nlinarith
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), ?_, ?_⟩
  · have := congrArg (fun w : Kˣ => (w : K)) hu1
    simpa [Units.val_pow_eq_pow_val, pow_succ] using this
  · intro h
    apply hu2
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val, pow_two] using h

theorem five_le_of_mod_four [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) : 5 ≤ p ^ f := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  have h2 : 2 ≤ p ^ f := by
    rcases Nat.lt_or_ge (p ^ f) 2 with h | h
    · have : p ^ f = 0 ∨ p ^ f = 1 := by omega
      rcases this with h0 | h0 <;> simp [h0] at h1
    · exact h
  omega

@[expose] def dMat (ω : K) : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![ω, ω, ω⁻¹ * ω⁻¹, 1]

theorem det_dMat {ω : K} (hω0 : ω ≠ 0) : (dMat ω).det = 1 := by
  simp [dMat, Matrix.det_diagonal, Fin.prod_univ_four]
  field_simp

theorem dMat_unitary (hq : 0 < p ^ f) {ω : K} (hω0 : ω ≠ 0) (hω : ω ^ (p ^ f) * ω = 1) :
    ((dMat ω).map (· ^ (p ^ f)))ᵀ * dMat ω = 1 := by
  have h0 : ((0 : K) ^ (p ^ f)) = 0 := zero_pow hq.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, Matrix.mul_apply, h0, Matrix.diagonal]
  · exact hω
  · exact hω
  · rw [mul_pow, inv_pow]
    have : ω ^ p ^ f ≠ 0 := pow_ne_zero _ hω0
    field_simp
    linear_combination -(ω ^ p ^ f * ω + 1) * hω

theorem graph_not_inner [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (hq4 : p ^ f % 4 = 1) {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (a : A)
    {B : Matrix (Fin 4) (Fin 4) K} (hBU : IsUnitaryU (p ^ f) B)
    (hu : ∀ g : ↥(StatedSU 4 (p ^ f) K),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B =
        B * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f))) :
    α a ∉ (MulAut.conj : ↥(StatedSU 4 (p ^ f) K) →* MulAut ↥(StatedSU 4 (p ^ f) K)).range := by
  rintro ⟨j, hj⟩
  have h5 := five_le_of_mod_four hK hq4
  obtain ⟨ω, hω, hω2⟩ := exists_unit_scalar_sq_ne_one hK (by omega)
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), zero_mul] at hω
    exact zero_ne_one hω
  have hωq : ω ^ (p ^ f) = ω⁻¹ := eq_inv_of_mul_eq_one_left hω
  have hqpos : 0 < p ^ f := by omega
  let g : ↥(StatedSU 4 (p ^ f) K) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (dMat ω) (by rw [det_dMat hω0]; exact one_ne_zero),
      Subgroup.subset_closure ⟨det_dMat hω0, dMat_unitary hqpos hω0 hω⟩⟩
  have hg := hu g
  rw [← hj, MulAut.conj_apply] at hg
  have hgm : (((g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = dMat ω := rfl
  set jm : Matrix (Fin 4) (Fin 4) K := ((j : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hjm
  set jim : Matrix (Fin 4) (Fin 4) K := (((j : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hjim
  have hjj : jm * jim = 1 := by
    rw [hjm, hjim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hjj' : jim * jm = 1 := mul_eq_one_comm.mp hjj
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hgm, Subgroup.coe_inv] at hg
  change jm * dMat ω * jim * B = B * (dMat ω).map (· ^ (p ^ f)) at hg
  have hdetB : B.det ≠ 0 := by
    have h1 : B * (B.map (· ^ (p ^ f)))ᵀ = 1 := mul_eq_one_comm.mp hBU
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have e1 : (jm * dMat ω * jim - ω • (1 : Matrix (Fin 4) (Fin 4) K)) * B =
      B * ((dMat ω).map (· ^ (p ^ f)) - ω • (1 : Matrix (Fin 4) (Fin 4) K)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have e2 := congrArg Matrix.det e1
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm B.det] at e2
  have e3 := mul_right_cancel₀ hdetB e2
  have e4 : jm * dMat ω * jim - ω • (1 : Matrix (Fin 4) (Fin 4) K) = jm * (dMat ω - ω • 1) * jim := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hjj]
  have hdj : jm.det * jim.det = 1 := by rw [← Matrix.det_mul, hjj, Matrix.det_one]
  have e5 : (jm * dMat ω * jim - ω • (1 : Matrix (Fin 4) (Fin 4) K)).det = 0 := by
    rw [e4, Matrix.det_mul, Matrix.det_mul]
    have : (dMat ω - ω • (1 : Matrix (Fin 4) (Fin 4) K)).det = 0 := by
      have hd : dMat ω - ω • (1 : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![ω - ω, ω - ω, ω⁻¹ * ω⁻¹ - ω, 1 - ω] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [dMat, Matrix.diagonal]
      rw [hd, Matrix.det_diagonal, Fin.prod_univ_four]
      simp
    rw [this]; simp
  rw [e5] at e3
  have hD : ((dMat ω).map (· ^ (p ^ f)) - ω • (1 : Matrix (Fin 4) (Fin 4) K)) =
      Matrix.diagonal ![ω⁻¹ - ω, ω⁻¹ - ω, ω * ω - ω, 1 - ω] := by
    have h0 : ((0 : K) ^ (p ^ f)) = 0 := zero_pow hqpos.ne'
    ext a b
    fin_cases a <;> fin_cases b <;> simp [dMat, Matrix.diagonal, h0, hωq, mul_pow, inv_pow]
  rw [hD, Matrix.det_diagonal, Fin.prod_univ_four] at e3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e3
  have h1 : ω⁻¹ - ω ≠ 0 := by
    intro h0
    apply hω2
    have : ω⁻¹ = ω := sub_eq_zero.1 h0
    calc ω * ω = ω * ω⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel₀ hω0
  have hne1 : ω ≠ 1 := by
    intro h1
    apply hω2
    rw [h1]; norm_num
  have h2 : ω * ω - ω ≠ 0 := by
    intro h0
    apply hne1
    have : ω * (ω - 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hω0
    · linear_combination h
  have h3 : 1 - ω ≠ 0 := fun h => hne1 (by linear_combination -h)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h1) h2) h3 e3.symm

end NotInner

section Signs

theorem diag_m1 {σ : Fin 4 → K} (hs : ∀ i, σ i * σ i = 1) (hc : σ 0 * σ 2 = σ 1 * σ 3) :
    Matrix.diagonal σ * (m1 : Matrix (Fin 4) (Fin 4) K) = (σ 0 * σ 2) • (m1 * Matrix.diagonal σ) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal]
  fin_cases a <;> fin_cases b <;> simp [m1]
  · linear_combination (-σ 0) * hs 2
  · linear_combination (-σ 1) * hs 3 + (-σ 3) * hc
  · linear_combination (-σ 2) * hs 0
  · linear_combination (-σ 3) * hs 1 + (-σ 1) * hc

theorem diag_m3 {σ : Fin 4 → K} (hs : ∀ i, σ i * σ i = 1) (hc : σ 0 * σ 1 = σ 2 * σ 3) :
    Matrix.diagonal σ * (m3 : Matrix (Fin 4) (Fin 4) K) = (σ 0 * σ 1) • (m3 * Matrix.diagonal σ) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal]
  fin_cases a <;> fin_cases b <;> simp [m3]
  · linear_combination (-σ 0) * hs 1
  · linear_combination (-σ 1) * hs 0
  · linear_combination (-σ 2) * hs 3 + (-σ 3) * hc
  · linear_combination (-σ 3) * hs 2 + (-σ 2) * hc

theorem m2_eq_diag : (m2 : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![1, 1, -1, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [m2, Matrix.diagonal]

theorem m4_eq_diag : (m4 : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![1, -1, 1, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [m4, Matrix.diagonal]

theorem diag_comm_diag (d σ : Fin 4 → K) : Matrix.diagonal σ * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal σ := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem sign_pauli {σ : Fin 4 → K} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (hprod : σ 0 * σ 1 * σ 2 * σ 3 = 1) (i : Fin 4) :
    Matrix.diagonal σ * (mm i : Matrix (Fin 4) (Fin 4) K) = mm i * Matrix.diagonal σ ∨
      Matrix.diagonal σ * (mm i : Matrix (Fin 4) (Fin 4) K) = -(mm i * Matrix.diagonal σ) := by
  have hs : ∀ i, σ i * σ i = 1 := fun i => by
    rcases hσ i with h | h <;> rw [h] <;> norm_num
  have hc02 : σ 0 * σ 2 = σ 1 * σ 3 := by
    linear_combination (σ 1 * σ 3) * hprod - (σ 0 * σ 2) * (σ 3 * σ 3) * hs 1 - (σ 0 * σ 2) * hs 3
  have hc01 : σ 0 * σ 1 = σ 2 * σ 3 := by
    linear_combination (σ 2 * σ 3) * hprod - (σ 0 * σ 1) * (σ 3 * σ 3) * hs 2 - (σ 0 * σ 1) * hs 3
  have hpm : ∀ a b : Fin 4, σ a * σ b = 1 ∨ σ a * σ b = -1 := fun a b => by
    rcases hσ a with ha | ha <;> rcases hσ b with hb | hb <;> rw [ha, hb] <;> norm_num
  fin_cases i
  · rcases hpm 0 2 with h | h
    · left; show diagonal σ * m1 = m1 * diagonal σ
      rw [diag_m1 hs hc02, h, one_smul]
    · right; show diagonal σ * m1 = -(m1 * diagonal σ)
      rw [diag_m1 hs hc02, h, neg_one_smul]
  · left; show diagonal σ * m2 = m2 * diagonal σ
    rw [m2_eq_diag]; exact diag_comm_diag _ _
  · rcases hpm 0 1 with h | h
    · left; show diagonal σ * m3 = m3 * diagonal σ
      rw [diag_m3 hs hc01, h, one_smul]
    · right; show diagonal σ * m3 = -(m3 * diagonal σ)
      rw [diag_m3 hs hc01, h, neg_one_smul]
  · left; show diagonal σ * m4 = m4 * diagonal σ
    rw [m4_eq_diag]; exact diag_comm_diag _ _

theorem skew_pauli (a : K) (i : Fin 4) :
    (a • (m1 : Matrix (Fin 4) (Fin 4) K)) * mm i = mm i * (a • m1) ∨
      (a • (m1 : Matrix (Fin 4) (Fin 4) K)) * mm i = -(mm i * (a • m1)) := by
  fin_cases i
  · left; show (a • m1) * m1 = m1 * (a • m1)
    rw [Matrix.smul_mul, Matrix.mul_smul]
  · right; show (a • m1) * m2 = -(m2 * (a • m1))
    rw [Matrix.smul_mul, Matrix.mul_smul, m12, smul_neg]
  · left; show (a • m1) * m3 = m3 * (a • m1)
    rw [Matrix.smul_mul, Matrix.mul_smul, m13]
  · left; show (a • m1) * m4 = m4 * (a • m1)
    rw [Matrix.smul_mul, Matrix.mul_smul, m14]

theorem prod_sigma {σ : Fin 4 → K} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    σ 0 * σ 1 * σ 2 * σ 3 = 1 ∨ σ 0 * σ 1 * σ 2 * σ 3 = -1 := by
  rcases hσ 0 with h0 | h0 <;> rcases hσ 1 with h1 | h1 <;> rcases hσ 2 with h2 | h2 <;>
    rcases hσ 3 with h3 | h3 <;> simp [h0, h1, h2, h3]

end Signs

end GenLocU4OutE16

end CFSG.GH74.Generic.BProg.B2

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank Subgroup Matrix
  CFSG.GH74.Generic.S1.Uni CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace GenLocU4Out

open GenLocU4Basic GenLocL4Out

variable {K : Type} [Field K] [Finite K]

theorem not_sectional_su4_sp_or_plus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (a : A) (B : GL (Fin 4) K) (hB : IsGraphU4 B (α a)) (haa : α a * α a = 1)
    (htype : (B : Matrix (Fin 4) (Fin 4) K)ᵀ = -(B : Matrix (Fin 4) (Fin 4) K) ∨
      ((B : Matrix (Fin 4) (Fin 4) K)ᵀ = B ∧ ∃ μ : K, μ ^ (p ^ f + 1) = 1 ∧
        μ * μ = (B : Matrix (Fin 4) (Fin 4) K).det)) :
    ¬ SectionalTwoRankLE ↥(innJoin α) 4 := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨hBU, hBg⟩ := hB
  have hu : ∀ g : ↥(StatedSU 4 (p ^ f) K),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (B : Matrix (Fin 4) (Fin 4) K) =
        (B : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) := by
    intro g
    rw [hBg g, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have hnin := GenLocU4OutE16.graph_not_inner hK hq α a hBU hu
  have hUmk : ∀ {U : Matrix (Fin 4) (Fin 4) K}, IsUnitaryU (p ^ f) U →
      ∃ P : GL (Fin 4) K, (P : Matrix (Fin 4) (Fin 4) K) = U := fun {U} hU =>
    ⟨⟨U, (U.map (· ^ (p ^ f)))ᵀ, mul_eq_one_comm.mp hU, hU⟩, rfl⟩
  rcases htype with hskew | ⟨hsym, μ, hμ, hμ2⟩
  · obtain ⟨U, a₀, hU, hBdef⟩ := GenLocU4OutFrame.exists_skew_nf h hp2 hskew
      ((GenLocU4OutFrame.isUnitaryU_iff_cT h _).1 hBU)
    have hU' : IsUnitaryU (p ^ f) U := (GenLocU4OutFrame.isUnitaryU_iff_cT h _).2 hU
    obtain ⟨P, hPU⟩ := hUmk hU'
    subst hPU
    exact GenLocU4OutE16.not_sectional_of_pauli_form hp hp2 hK α a haa hnin hU' hBdef hBU hu
      (GenLocU4OutE16.skew_pauli a₀)
  · obtain ⟨U, σ, hU, hσ, hBdef⟩ := GenLocU4OutFrame.exists_sym_nf_pm hp hp2 hK hq hsym hBU
    have hprod : σ 0 * σ 1 * σ 2 * σ 3 = 1 := by
      rcases GenLocU4OutE16.prod_sigma hσ with h1 | h1
      · exact h1
      · exfalso
        have hdet : (B : Matrix (Fin 4) (Fin 4) K).det = U.det * U.det * (σ 0 * σ 1 * σ 2 * σ 3) := by
          rw [hBdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
            Fin.prod_univ_four]
          ring
        have hUc := (GenLocU4OutFrame.isUnitaryU_iff_cT h _).1 hU
        have hdetcT : (cT h U).det = h.bar U.det := by
          rw [cT, Matrix.det_transpose]
          exact (RingHom.map_det (h.bar : K →+* K) U).symm
        have hdU : h.bar U.det * U.det = 1 := by
          have := congrArg Matrix.det hUc
          rwa [Matrix.det_mul, hdetcT, Matrix.det_one] at this
        have hdU0 : U.det ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hdU; exact zero_ne_one hdU
        have hdUq : U.det ^ (p ^ f + 1) = 1 := by
          rw [pow_succ]
          rw [UnitaryFieldData.bar_apply] at hdU
          exact hdU
        rw [h1, mul_neg_one] at hdet
        refine GenLocU4ExtMu.not_isSqM_neg_one hq h2 ⟨μ * U.det⁻¹, ?_, ?_⟩
        · rw [mul_pow, inv_pow, hμ, hdUq, inv_one, mul_one]
        · have : (μ * U.det⁻¹) * (μ * U.det⁻¹) = μ * μ * (U.det⁻¹ * U.det⁻¹) := by ring
          rw [this, hμ2, hdet]
          field_simp
    obtain ⟨P, hPU⟩ := hUmk hU
    subst hPU
    exact GenLocU4OutE16.not_sectional_of_pauli_form hp hp2 hK α a haa hnin hU hBdef hBU hu
      (GenLocU4OutE16.sign_pauli hσ hprod)

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
