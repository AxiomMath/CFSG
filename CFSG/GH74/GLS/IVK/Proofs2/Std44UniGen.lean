module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical CFSG.GH74.GLS.IVK

namespace Std44UniGen

section Blocks

variable {F : Type} [Field F]

abbrev dgn (F : Type) [Field F] (c : Fin 3) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal (fun i => if i = c then (1 : F) else -1)

theorem block_col {M : Matrix (Fin 3) (Fin 3) F} {c : Fin 3}
    (hM : M *ᵥ Pi.single c 1 = Pi.single c 1) (i : Fin 3) :
    M i c = if i = c then 1 else 0 := by
  have := congrFun hM i
  rw [Matrix.mulVec_single_one] at this
  simpa [Pi.single_apply] using this

theorem block_row (σ : F →+* F) {M : Matrix (Fin 3) (Fin 3) F} {c : Fin 3}
    (hU : (M.map σ)ᵀ * M = 1) (hcol : ∀ i, M i c = if i = c then 1 else 0) (j : Fin 3) :
    M c j = if c = j then 1 else 0 := by
  have h := congrFun (congrFun hU c) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at h
  rw [Finset.sum_eq_single c] at h
  · simpa [hcol] using h
  · intro i _ hi
    simp [hcol, hi]
  · simp

theorem commute_dgn {M : Matrix (Fin 3) (Fin 3) F} {c : Fin 3}
    (hcol : ∀ i, M i c = if i = c then 1 else 0) (hrow : ∀ j, M c j = if c = j then 1 else 0) :
    M * dgn F c = dgn F c * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i = c <;> by_cases hj : j = c
  · subst hi; subst hj; simp
  · subst hi
    have := hrow j
    simp [Ne.symm hj] at this
    simp [hj, this]
  · subst hj
    have := hcol i
    simp [hi] at this
    simp [hi, this]
  · simp only [hi, hj, ite_false]
    ring

theorem entries_of_commute_dgn {M : Matrix (Fin 3) (Fin 3) F} {c : Fin 3} (h2 : (2 : F) ≠ 0)
    (hcomm : M * dgn F c = dgn F c * M) {i : Fin 3} (hi : i ≠ c) : M i c = 0 := by
  have := congrFun (congrFun hcomm i) c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  simp only [hi, ite_true, ite_false, mul_one] at this
  have h3 : (2 : F) * M i c = 0 := by linear_combination this
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem trace_dgn (c : Fin 3) : (dgn F c).trace = -1 := by
  fin_cases c <;> simp [Matrix.trace, Fin.sum_univ_three]

theorem commute_of_mem_centralizer {q : ℕ} (c : Fin 3) (t g : StatedSU 3 q F)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hg : statedProjMk (StatedSU 3 q F) g ∈
      centralizer ({statedProjMk (StatedSU 3 q F) t} : Set (StatedProj (StatedSU 3 q F)))) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * dgn F c =
      dgn F c * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h1 : statedProjMk (StatedSU 3 q F) (g * t) = statedProjMk (StatedSU 3 q F) (t * g) := by
    rw [map_mul, map_mul]; exact hg
  have h2 := QuotientGroup.eq.mp h1
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h2
  obtain ⟨u, hu⟩ := h2
  set G : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  set T : Matrix (Fin 3) (Fin 3) F := ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hT
  have hgt : (g : GL (Fin 3) F) * (t : GL (Fin 3) F) *
      Matrix.GeneralLinearGroup.scalar (Fin 3) u = (t : GL (Fin 3) F) * (g : GL (Fin 3) F) := by
    rw [hu]
    simp [_root_.mul_inv_rev, mul_assoc]
  have hmat : G * T * (Matrix.scalar (Fin 3) (u : F)) = T * G := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hgt
    simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] using this
  have hsm : T * G = (u : F) • (G * T) := by
    rw [← hmat, Matrix.scalar_apply, Matrix.smul_eq_mul_diagonal]
  set Gi : Matrix (Fin 3) (Fin 3) F :=
    (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGi
  have hGiG : Gi * G = 1 := by simp [Gi, G]
  have hGGi : G * Gi = 1 := by simp [Gi, G]
  have h5 : Gi * T * G = (u : F) • T := by
    calc Gi * T * G = Gi * (T * G) := by rw [Matrix.mul_assoc]
      _ = Gi * ((u : F) • (G * T)) := by rw [hsm]
      _ = (u : F) • (Gi * G * T) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (u : F) • T := by rw [hGiG, Matrix.one_mul]
  have h6 : (Gi * T * G).trace = T.trace := by
    rw [Matrix.trace_mul_cycle, hGGi, Matrix.one_mul]
  rw [h5, Matrix.trace_smul, smul_eq_mul, ht, trace_dgn] at h6
  have hu1 : (u : F) = 1 := by linear_combination -h6
  rw [hu1, one_smul] at hsm
  rw [← ht]
  exact hsm.symm

theorem conj_fix_single {q : ℕ} (c : Fin 3) (g b : StatedSU 3 q F)
    (hgc : ∀ i, i ≠ c → ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i c = 0)
    (hb : ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single c 1 = Pi.single c 1) :
    (((g * b * g⁻¹ : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Pi.single c 1 = Pi.single c 1 := by
  set G : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  set B : Matrix (Fin 3) (Fin 3) F := ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hB
  set Gi : Matrix (Fin 3) (Fin 3) F :=
    (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGi
  have hGiG : Gi * G = 1 := by simp [Gi, G]
  set e : Fin 3 → F := Pi.single c 1 with he
  have hGe : G *ᵥ e = (G c c) • e := by
    rw [he, Matrix.mulVec_single_one]
    funext i
    by_cases hi : i = c
    · subst hi; simp
    · simp [hgc i hi, hi]
  have hd : G c c ≠ 0 := by
    intro hd0
    rw [hd0, zero_smul] at hGe
    have h0 : e = 0 := by
      calc e = (Gi * G) *ᵥ e := by rw [hGiG, Matrix.one_mulVec]
        _ = Gi *ᵥ (G *ᵥ e) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hGe, Matrix.mulVec_zero]
    have := congrFun h0 c
    simp [he] at this
  have hGie : Gi *ᵥ e = (G c c)⁻¹ • e := by
    have h1 : e = (G c c) • (Gi *ᵥ e) := by
      calc e = (Gi * G) *ᵥ e := by rw [hGiG, Matrix.one_mulVec]
        _ = Gi *ᵥ (G *ᵥ e) := by rw [Matrix.mulVec_mulVec]
        _ = (G c c) • (Gi *ᵥ e) := by rw [hGe, Matrix.mulVec_smul]
    calc Gi *ᵥ e = (G c c)⁻¹ • ((G c c) • (Gi *ᵥ e)) := by
          rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
      _ = (G c c)⁻¹ • e := by rw [← h1]
  have hcoe : (((g * b * g⁻¹ : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      G * B * Gi := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rfl
  rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGie, Matrix.mulVec_smul, hb,
    Matrix.mulVec_smul, hGe, smul_smul, inv_mul_cancel₀ hd, one_smul]

end Blocks

section Abstract

variable {Y : Type} [Group Y]

theorem le_Ez_of_normal_quasisimple (z : Y) (J : Subgroup Y)
    (hJC : J ≤ centralizer ({z} : Set Y))
    (hN : ∀ x ∈ centralizer ({z} : Set Y), ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hQ : CFSG.IsQuasisimple ↥J) : J ≤ Ez z := by
  set C := centralizer ({z} : Set Y) with hC
  have hnorm : (J.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hN (g : Y) g.2 (n : Y) hn
    simpa using this
  have hQ' : CFSG.IsQuasisimple ↥(J.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hQ
  have hcomp : CFSG.IsComponent (J.subgroupOf C) := ⟨hQ', hnorm.isSubnormal⟩
  have hle : J.subgroupOf C ≤ CFSG.layer ↥C := le_sSup hcomp
  intro x hx
  refine ⟨⟨x, hJC hx⟩, hle ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]; exact hx

theorem le_O2z_of_odd (z : Y) (J : Subgroup Y)
    (hJC : J ≤ centralizer ({z} : Set Y))
    (hgen : ∀ x ∈ J, x ∈ Subgroup.closure {y : Y | y ∈ J ∧ Nat.Coprime (orderOf y) 2}) :
    J ≤ O2z z := by
  set C := centralizer ({z} : Set Y) with hC
  have hsub : Subgroup.closure {y : Y | y ∈ J ∧ Nat.Coprime (orderOf y) 2} ≤ O2z z := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyJ, hy⟩
    refine ⟨⟨y, hJC hyJ⟩, Subgroup.subset_closure ?_, rfl⟩
    show Nat.Coprime (orderOf (⟨y, hJC hyJ⟩ : C)) 2
    rwa [Subgroup.orderOf_mk]
  exact fun x hx => hsub (hgen x hx)

end Abstract

section CoordBlock

variable {p f : ℕ} {F : Type} [Field F]

theorem coordBlock_commute (h : UnitaryFieldData p f F) (c : Fin 3) (t b : unitarySU p f F 3)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hb : b ∈ coordBlock p f F c) : b * t = t * b := by
  have hcol := block_col (mem_coordBlock.mp hb)
  have hU := ((mem_unitarySU_iff h).mp b.2).2
  have hrow := block_row h.bar hU hcol
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [ht]
  exact commute_dgn hcol hrow

theorem two_ne_zero_of_data (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  have : CharP F p := h.charP
  exact Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)

theorem block_map_le_centralizer (c : Fin 3) (h : UnitaryFieldData p f F) (t : unitarySU p f F 3)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c) :
    (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) ≤
      centralizer ({statedProjMk (unitarySU p f F 3) t} : Set (StatedProj (unitarySU p f F 3))) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    coordBlock_commute h c t b ht hb]

theorem block_map_normalized (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (c : Fin 3)
    (t : unitarySU p f F 3) (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c) :
    ∀ x ∈ centralizer ({statedProjMk (unitarySU p f F 3) t} : Set (StatedProj (unitarySU p f F 3))),
      ∀ j ∈ (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)),
        x * j * x⁻¹ ∈ (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) := by
  intro x hx j hj
  obtain ⟨g, rfl⟩ := statedProjMk_surjective (unitarySU p f F 3) x
  obtain ⟨b, hb, rfl⟩ := hj
  refine ⟨g * b * g⁻¹, mem_coordBlock.mpr ?_, by simp [map_mul, map_inv]⟩
  exact conj_fix_single c g b (fun i hi => entries_of_commute_dgn (two_ne_zero_of_data h hp2)
    (commute_of_mem_centralizer c t g ht hx) hi) (mem_coordBlock.mp hb)

theorem isQuasisimple_block_map (h : UnitaryFieldData p f F) (c : Fin 3) (hq : 4 ≤ p ^ f) :
    CFSG.IsQuasisimple ↥((coordBlock p f F c).map (statedProjMk (unitarySU p f F 3))) := by
  have hQ := isQuasisimple_map_coordBlock h c hq
  let e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  have hmap : (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) =
      ((coordBlock p f F c).map (unitaryProj h 3)).map e.toMonoidHom := by
    have hcomp : e.toMonoidHom.comp (unitaryProj h 3) = statedProjMk (unitarySU p f F 3) :=
      MonoidHom.ext fun g => unitaryPSUEquiv_unitaryProj h (by norm_num) g
    rw [Subgroup.map_map, hcomp]
  rw [hmap]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.subgroupMap _) hQ

theorem block_le_Ez (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (c : Fin 3)
    (t : unitarySU p f F 3) (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hq : 4 ≤ p ^ f) :
    (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) ≤
      Ez (statedProjMk (unitarySU p f F 3) t) :=
  le_Ez_of_normal_quasisimple _ _ (block_map_le_centralizer c h t ht)
    (block_map_normalized h hp2 c t ht) (isQuasisimple_block_map h c hq)

end CoordBlock

section Odd

variable {p f : ℕ} {F : Type} [Field F]

theorem closure_cube_eq_top {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = 3) :
    Subgroup.closure {z : Matrix.SpecialLinearGroup (Fin 2) F₀ | z ^ 3 = 1} = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
  apply Subgroup.closure_mono
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  show (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩) ^ 3 = 1
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  have h3 : (3 : F₀) = 0 := by
    have := Fintype.ofFinite F₀
    have := FiniteField.cast_card_eq_zero F₀
    rwa [← Nat.card_eq_fintype_card, hF₀, Nat.cast_ofNat] at this
  have hc : c + (c + c) = 0 := by linear_combination c * h3
  rw [pow_three, ← Matrix.SpecialLinearGroup.transvection_add,
    ← Matrix.SpecialLinearGroup.transvection_add, hc,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem block_cube_generated (h : UnitaryFieldData p f F) (c : Fin 3) (hq3 : p ^ f = 3)
    (b : unitarySU p f F 3) (hb : b ∈ coordBlock p f F c) :
    b ∈ Subgroup.closure {y : unitarySU p f F 3 | y ∈ coordBlock p f F c ∧ y ^ 3 = 1} := by
  obtain ⟨φ⟩ := nonempty_coordBlock_mulEquiv h c
  have := h.finite
  have hcard : Nat.card h.fixedField = 3 := by rw [UnitaryFieldData.card_fixedField h, hq3]
  have hcl := closure_cube_eq_top hcard
  set K' := Subgroup.closure {y : ↥(coordBlock p f F c) | y ^ 3 = 1} with hK'
  have hall : ∀ z : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, φ.symm z ∈ K' := by
    intro z
    have hz : z ∈ Subgroup.closure
        {w : Matrix.SpecialLinearGroup (Fin 2) h.fixedField | w ^ 3 = 1} := by
      rw [hcl]; exact Subgroup.mem_top z
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      refine Subgroup.subset_closure ?_
      show (φ.symm w) ^ 3 = 1
      rw [← map_pow, show w ^ 3 = 1 from hw, map_one]
    | one => rw [map_one]; exact K'.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact K'.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact K'.inv_mem hx
  have hbK : (⟨b, hb⟩ : ↥(coordBlock p f F c)) ∈ K' := by
    have := hall (φ ⟨b, hb⟩)
    rwa [MulEquiv.symm_apply_apply] at this
  have hle : K'.map (coordBlock p f F c).subtype ≤
      Subgroup.closure {y : unitarySU p f F 3 | y ∈ coordBlock p f F c ∧ y ^ 3 = 1} := by
    rw [hK', MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 : ((y ^ 3 : ↥(coordBlock p f F c)) : unitarySU p f F 3) = 1 := by
      rw [show y ^ 3 = 1 from hy]; rfl
    simpa using h1
  exact hle ⟨_, hbK, rfl⟩

theorem block_le_O2z (h : UnitaryFieldData p f F) (c : Fin 3) (t : unitarySU p f F 3)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c) (hq3 : p ^ f = 3) :
    (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) ≤
      O2z (statedProjMk (unitarySU p f F 3) t) := by
  refine le_O2z_of_odd _ _ (block_map_le_centralizer c h t ht) ?_
  rintro _ ⟨b, hb, rfl⟩
  have hb' := block_cube_generated h c hq3 b hb
  have hle : (Subgroup.closure {y : unitarySU p f F 3 | y ∈ coordBlock p f F c ∧ y ^ 3 = 1}).map
      (statedProjMk (unitarySU p f F 3)) ≤
      Subgroup.closure {y : StatedProj (unitarySU p f F 3) |
        y ∈ (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) ∧
          Nat.Coprime (orderOf y) 2} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨y, ⟨hyB, hy3⟩, rfl⟩
    refine ⟨⟨y, hyB, rfl⟩, ?_⟩
    have h3 : (statedProjMk (unitarySU p f F 3) y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3) (by norm_num)
  exact hle ⟨_, hb', rfl⟩

end Odd

section Gen

variable {p f : ℕ} {F : Type} [Field F]

def rotGL (F : Type) [Field F] : GL (Fin 3) F :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; -1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem rotGL_mem (h : UnitaryFieldData p f F) : rotGL F ∈ unitarySU p f F 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨by simp [rotGL, Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotGL, Matrix.mul_apply, Fin.sum_univ_three]

theorem conj_fix_of_map {q : ℕ} (s g : StatedSU 3 q F) (v w : Fin 3 → F)
    (hs : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w)
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    (((s * g * s⁻¹ : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
  set S : Matrix (Fin 3) (Fin 3) F := ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hS
  set G : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  set Si : Matrix (Fin 3) (Fin 3) F :=
    (((s : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hSi
  have hSiS : Si * S = 1 := by simp [Si, S]
  have hSiw : Si *ᵥ w = v := by
    rw [← hs, Matrix.mulVec_mulVec, hSiS, Matrix.one_mulVec]
  have hcoe : (((s * g * s⁻¹ : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      S * G * Si := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rfl
  rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSiw, hg, hs]

theorem coordBlock_sup_eq_top (h : UnitaryFieldData p f F) (hq2 : p ^ f ≠ 2) :
    coordBlock p f F 2 ⊔ coordBlock p f F 1 = ⊤ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP F p := h.charP
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  let e : CFSG.ClassicalInvolution.Phan.Su F p f 3 ≃* unitarySU p f F 3 :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3)
  set W : Subgroup (unitarySU p f F 3) := coordBlock p f F 2 ⊔ coordBlock p f F 1 with hW
  set rot : unitarySU p f F 3 := ⟨rotGL F, rotGL_mem h⟩ with hrot
  have hrot2 : rot ∈ coordBlock p f F 2 := by
    rw [mem_coordBlock, Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [hrot, rotGL]
  have hrot0 : ((rot : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 =
      Pi.single 1 1 := by
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [hrot, rotGL]
  have hcomap : W.comap e.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← CFSG.ClassicalInvolution.Phan.B12_sup_B23 hF hq2]
    refine sup_le ?_ ?_
    · rintro g ⟨A, rfl⟩
      refine Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (mem_coordBlock.mpr ?_))
      rw [Matrix.mulVec_single_one]
      funext i
      fin_cases i <;> simp [e, CFSG.LieType.Steinberg.coe_embSUid, CFSG.LieType.Steinberg.embPair]
    · rintro g ⟨A, rfl⟩
      have hfix : ((e (CFSG.LieType.Steinberg.embSUid
          (CFSG.LieType.BorelTits.unitaryInvolution F p f) 0 A) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
        rw [Matrix.mulVec_single_one]
        funext i
        fin_cases i <;> simp [e, CFSG.LieType.Steinberg.coe_embSUid, CFSG.LieType.Steinberg.embPair]
      refine Subgroup.mem_comap.mpr ?_
      show e (CFSG.LieType.Steinberg.embSUid
          (CFSG.LieType.BorelTits.unitaryInvolution F p f) 0 A) ∈ W
      generalize e (CFSG.LieType.Steinberg.embSUid
          (CFSG.LieType.BorelTits.unitaryInvolution F p f) 0 A) = g' at hfix ⊢
      have hmem : rot * g' * rot⁻¹ ∈ coordBlock p f F 1 :=
        mem_coordBlock.mpr (conj_fix_of_map rot g' (Pi.single 0 1) (Pi.single 1 1) hrot0 hfix)
      have hrotW : rot ∈ W := Subgroup.mem_sup_left hrot2
      have hmemW : rot * g' * rot⁻¹ ∈ W := Subgroup.mem_sup_right hmem
      have hrw : g' = rot⁻¹ * (rot * g' * rot⁻¹) * rot := by group
      rw [hrw]
      exact W.mul_mem (W.mul_mem (W.inv_mem hrotW) hmemW) hrotW
  rw [eq_top_iff]
  intro x _
  have hx : e.symm x ∈ W.comap e.toMonoidHom := by rw [hcomap]; exact Subgroup.mem_top _
  simpa using hx

end Gen

section Data

theorem exists_prime_pow_of_card_sq (F : Type) [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) : ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f = q ∧ CharP F p := by
  have := Fintype.ofFinite F
  have hpp : IsPrimePow q := by
    have h1 : IsPrimePow (Nat.card F) := by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.isPrimePow_card F
    rw [hF] at h1
    exact (isPrimePow_pow_iff two_ne_zero).mp h1
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := (isPrimePow_def q).mp hpp
  rw [← Nat.prime_iff] at hℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact ⟨ℓ, f, hℓ, hf, rfl, charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])⟩

theorem dgn_oddDiag₃ (F : Type) [Field F] :
    ((oddDiag₃ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₃]

theorem dgn_oddDiag₂ (F : Type) [Field F] :
    ((oddDiag₂ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₂]

end Data

end Std44UniGen

open Std44UniGen in
theorem uniGen (F : Type) [Field F] [Finite F] {q : ℕ} (hq : Odd q) (hF : Nat.card F = q ^ 2) :
    UniGen F hq := by
  obtain ⟨p, f, hp, hf, rfl, hchar⟩ := exists_prime_pow_of_card_sq F hF
  have : Fact p.Prime := ⟨hp⟩
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hq) (Nat.even_pow.mpr ⟨even_two, hf.ne'⟩)
  have hq2 : p ^ f ≠ 2 := fun h2 => by
    rw [h2] at hq
    exact absurd hq (by decide)
  let ρ := statedProjMk (unitarySU p f F 3)
  let t₃ : unitarySU p f F 3 :=
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
  let t₂ : unitarySU p f F 3 :=
    ⟨oddDiag₂ F, Subgroup.subset_closure ⟨det_oddDiag₂ F, unitary_oddDiag₂ hq⟩⟩
  have hgen : Subgroup.closure (((coordBlock p f F 2).map ρ : Set (StatedProj (unitarySU p f F 3))) ∪
      ((coordBlock p f F 1).map ρ : Set (StatedProj (unitarySU p f F 3)))) = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, ← Subgroup.map_sup,
      coordBlock_sup_eq_top h hq2, Subgroup.map_top, MonoidHom.range_eq_top.mpr
        (statedProjMk_surjective _)]
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · have h3 := block_le_Ez h hp2 2 t₃ (dgn_oddDiag₃ F) (by omega)
    have h2 := block_le_Ez h hp2 1 t₂ (dgn_oddDiag₂ F) (by omega)
    rw [eq_top_iff, ← hgen]
    exact Subgroup.closure_mono (Set.union_subset_union h3 h2)
  · have h3 := block_le_O2z h 2 t₃ (dgn_oddDiag₃ F) heq
    have h2 := block_le_O2z h 1 t₂ (dgn_oddDiag₂ F) heq
    rw [eq_top_iff, ← hgen]
    exact Subgroup.closure_mono (Set.union_subset_union h3 h2)

end CFSG.GH74.GLS.IVK.Proofs2
