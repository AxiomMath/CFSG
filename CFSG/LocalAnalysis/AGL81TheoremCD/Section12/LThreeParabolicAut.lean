module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
import CFSG.Milestones.ASVolI.F411.aL3Core

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient
open Matrix
open scoped MatrixGroups

private theorem transvection_matrix_mul_neg {p : ℕ} [Fact p.Prime] {i j : Fin 3} (hij : i ≠ j)
    (c : ZMod p) :
    (1 + single i j c : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      (1 + single i j (-c) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
  have h1SL : Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij (-c) = 1 :=
    Matrix.SpecialLinearGroup.transvection_mul_neg _ _
  have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) =>
    (x : Matrix (Fin 3) (Fin 3) (ZMod p))) h1SL
  simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one]
    using this

private theorem transvection_two_one_mem_stabilizer_flagSpace_one {p : ℕ} [Fact p.Prime]
    (c : ZMod p) :
    Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := (1 : Fin 3))
      (by decide) c ∈ stabilizer (flagSpace 3 (ZMod p) 1) := by
  rw [mem_stabilizer]
  change (flagSpace 3 (ZMod p) 1).map
    (mulVecLin (1 + single (2 : Fin 3) (1 : Fin 3) c :
      Matrix (Fin 3) (Fin 3) (ZMod p))) = flagSpace 3 (ZMod p) 1
  have hmap : ∀ c : ZMod p, (flagSpace 3 (ZMod p) 1).map
      (mulVecLin (1 + single (2 : Fin 3) (1 : Fin 3) c :
        Matrix (Fin 3) (Fin 3) (ZMod p))) ≤ flagSpace 3 (ZMod p) 1 := by
    intro c
    rintro _ ⟨v, hv, rfl⟩
    change v ∈ flagSpace 3 (ZMod p) 1 at hv
    rw [mem_flagSpace] at hv
    rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · simp at hj
    · simp [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, hv 1 le_rfl]
    · simp [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, hv 1 le_rfl,
        hv 2 (by decide)]
  refine le_antisymm (hmap c) ?_
  intro v hv
  refine ⟨(1 + single (2 : Fin 3) (1 : Fin 3) (-c) :
    Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v, hmap (-c) ⟨v, hv, rfl⟩, ?_⟩
  change (1 + single (2 : Fin 3) (1 : Fin 3) c : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
    ((1 + single (2 : Fin 3) (1 : Fin 3) (-c) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) = v
  rw [Matrix.mulVec_mulVec]
  rw [transvection_matrix_mul_neg (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide) c,
    Matrix.one_mulVec]

private theorem transvection_one_zero_mem_stabilizer_flagSpace_two {p : ℕ} [Fact p.Prime]
    (c : ZMod p) :
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := (0 : Fin 3))
      (by decide) c ∈ stabilizer (flagSpace 3 (ZMod p) 2) := by
  rw [mem_stabilizer]
  change (flagSpace 3 (ZMod p) 2).map
    (mulVecLin (1 + single (1 : Fin 3) (0 : Fin 3) c :
      Matrix (Fin 3) (Fin 3) (ZMod p))) = flagSpace 3 (ZMod p) 2
  have hmap : ∀ c : ZMod p, (flagSpace 3 (ZMod p) 2).map
      (mulVecLin (1 + single (1 : Fin 3) (0 : Fin 3) c :
        Matrix (Fin 3) (Fin 3) (ZMod p))) ≤ flagSpace 3 (ZMod p) 2 := by
    intro c
    rintro _ ⟨v, hv, rfl⟩
    change v ∈ flagSpace 3 (ZMod p) 2 at hv
    rw [mem_flagSpace] at hv
    rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · simp at hj
    · simp at hj
    · simp [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, hv 2 le_rfl]
  refine le_antisymm (hmap c) ?_
  intro v hv
  refine ⟨(1 + single (1 : Fin 3) (0 : Fin 3) (-c) :
    Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v, hmap (-c) ⟨v, hv, rfl⟩, ?_⟩
  change (1 + single (1 : Fin 3) (0 : Fin 3) c : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
    ((1 + single (1 : Fin 3) (0 : Fin 3) (-c) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) = v
  rw [Matrix.mulVec_mulVec]
  rw [transvection_matrix_mul_neg (i := (1 : Fin 3)) (j := (0 : Fin 3)) (by decide) c,
    Matrix.one_mulVec]

private theorem exists_scalar_eq_mul_of_centralizer_flagSpace {p : ℕ} [Fact p.Prime] {d : ℕ}
    {A t : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)}
    (htQ : t ∈ stabilizer (flagSpace 3 (ZMod p) d))
    (hg : proj 3 (ZMod p) A ∈ Subgroup.centralizer
      ((projStabilizer (flagSpace 3 (ZMod p) d) :
        Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p)))) :
    ∃ z ∈ scalars 3 (ZMod p), A * t = z * t * A := by
  have htmem : proj 3 (ZMod p) t ∈ projStabilizer (flagSpace 3 (ZMod p) d) :=
    Subgroup.mem_map_of_mem _ htQ
  have hcomm := (Subgroup.mem_centralizer_iff.mp hg) (proj 3 (ZMod p) t) htmem
  have hproj : proj 3 (ZMod p) (A * t * A⁻¹) = proj 3 (ZMod p) t := by
    rw [map_mul, map_mul, map_inv]
    rw [← hcomm]
    group
  set X : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) := A * t * A⁻¹ with hX
  have hz0mem : X⁻¹ * t ∈ scalars 3 (ZMod p) :=
    (proj_eq_proj_iff (n := 3) (K := ZMod p)).mp hproj
  set z0 := X⁻¹ * t with hz0
  set z := z0⁻¹ with hzdef
  have hzmem : z ∈ scalars 3 (ZMod p) := Subgroup.inv_mem _ hz0mem
  have hXeq : X = t * z := by
    have h1 : X⁻¹ = z0 * t⁻¹ := by
      rw [hz0]
      group
    calc X = (X⁻¹)⁻¹ := by simp
      _ = (z0 * t⁻¹)⁻¹ := by rw [h1]
      _ = t * z0⁻¹ := by group
      _ = t * z := by rw [hzdef]
  have hzcent : ∀ y, z * y = y * z := fun y =>
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 (ZMod p) hzmem) y).symm
  refine ⟨z, hzmem, ?_⟩
  calc A * t = (A * t * A⁻¹) * A := by group
    _ = X * A := by rw [hX]
    _ = (t * z) * A := by rw [hXeq]
    _ = z * t * A := by rw [← hzcent t]

private theorem eq_zero_of_centralizer_flagSpace_one {p : ℕ} [Fact p.Prime]
    {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)} {a b : ZMod p}
    (hab : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      a • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) +
        b • single (0 : Fin 3) (2 : Fin 3) (1 : ZMod p))
    (hg : proj 3 (ZMod p) A ∈ Subgroup.centralizer
      ((projStabilizer (flagSpace 3 (ZMod p) 1) :
        Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p)))) : b = 0 := by
  let t : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
    Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := (1 : Fin 3))
      (by decide) 1
  obtain ⟨z, hzmem, hAt⟩ := exists_scalar_eq_mul_of_centralizer_flagSpace
    (d := 1) (A := A) (t := t) (transvection_two_one_mem_stabilizer_flagSpace_one 1) hg
  obtain ⟨c, -, hzmat⟩ := mem_scalars.mp hzmem
  have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) =>
    (x : Matrix (Fin 3) (Fin 3) (ZMod p))) hAt
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hmat
  have h01 := congrFun₂ hmat (0 : Fin 3) (1 : Fin 3)
  simp [hab, hzmat, t, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply, Fin.sum_univ_three] at h01
  exact h01

private theorem eq_zero_of_centralizer_flagSpace_two {p : ℕ} [Fact p.Prime]
    {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)} {a b : ZMod p}
    (hab : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      a • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) +
        b • single (0 : Fin 3) (2 : Fin 3) (1 : ZMod p))
    (hg : proj 3 (ZMod p) A ∈ Subgroup.centralizer
      ((projStabilizer (flagSpace 3 (ZMod p) 2) :
        Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p)))) : b = 0 := by
  let t : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := (0 : Fin 3))
      (by decide) 1
  obtain ⟨z, hzmem, hAt⟩ := exists_scalar_eq_mul_of_centralizer_flagSpace
    (d := 2) (A := A) (t := t) (transvection_one_zero_mem_stabilizer_flagSpace_two 1) hg
  obtain ⟨c, -, hzmat⟩ := mem_scalars.mp hzmem
  have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) =>
    (x : Matrix (Fin 3) (Fin 3) (ZMod p))) hAt
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hmat
  have h12 := congrFun₂ hmat (1 : Fin 3) (2 : Fin 3)
  simp [hab, hzmat, t, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply, Fin.sum_univ_three] at h12
  exact h12

private theorem proj_eq_one_of_eq_smul_one {p : ℕ} [Fact p.Prime]
    {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)} {a : ZMod p}
    (hAmat : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      a • (1 : Matrix (Fin 3) (Fin 3) (ZMod p))) :
    proj 3 (ZMod p) A = 1 := by
  have hAdet : a ^ 3 = 1 := by
    have h := A.prop
    rw [hAmat] at h
    simpa [Matrix.det_smul, Fintype.card_fin] using h
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hAdet
    norm_num at hAdet
  refine proj_eq_one_iff.mpr (mem_scalars.mpr ⟨Units.mk0 a ha0, ?_, ?_⟩)
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hAdet
  · rw [hAmat]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]

private theorem commute_unitriangular_of_centralizer_projStabilizer {p : ℕ} [Fact p.Prime]
    {d : ℕ} {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)}
    (hg : proj 3 (ZMod p) A ∈ Subgroup.centralizer
      ((projStabilizer (flagSpace 3 (ZMod p) d) :
        Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p)))) :
    ∀ u ∈ unitriangular 3 (ZMod p), A * u = u * A := by
  intro u hu
  have hUQ : u ∈ stabilizer (flagSpace 3 (ZMod p) d) :=
    upperTriangular_le_stabilizer_flagSpace d
      (unitriangular_le_upperTriangular 3 (ZMod p) hu)
  have hmem : proj 3 (ZMod p) u ∈ projStabilizer (flagSpace 3 (ZMod p) d) :=
    Subgroup.mem_map_of_mem _ hUQ
  have hcomm := (Subgroup.mem_centralizer_iff.mp hg) (proj 3 (ZMod p) u) hmem
  have hproj : proj 3 (ZMod p) (A * u * A⁻¹) = proj 3 (ZMod p) u := by
    rw [map_mul, map_mul, map_inv]
    rw [← hcomm]
    group
  obtain ⟨m, hum⟩ :=
    CFSG.ASVolI.burnsideF411a_isPGroup_unitriangular (K := ZMod p) p 3 ⟨u, hu⟩
  have hum' : u ^ p ^ m = 1 := by simpa using congrArg Subtype.val hum
  have hconj : (A * u * A⁻¹) ^ p ^ m = 1 := by
    have hconjEq : A * u * A⁻¹ = MulAut.conj A u := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hconjEq, ← map_pow, hum', map_one]
  have h := CFSG.ASVolI.burnsideF411a_eq_of_proj_eq (K := ZMod p) p (n := 3)
    (by norm_num) (g := A * u * A⁻¹) (u := u) m hconj hum' hproj
  calc A * u = (A * u * A⁻¹) * A := by group
    _ = u * A := by rw [h]

private theorem commute_single_of_commute_unitriangular {p : ℕ} [Fact p.Prime]
    {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)}
    (hAU : ∀ u ∈ unitriangular 3 (ZMod p), A * u = u * A) :
    ∀ i j : Fin 3, (i : ℕ) + 1 = (j : ℕ) →
      (A : Matrix (Fin 3) (Fin 3) (ZMod p)) * single i j (1 : ZMod p) =
        single i j (1 : ZMod p) * (A : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
  intro i j hij
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have htrans : Matrix.SpecialLinearGroup.transvection hlt.ne (1 : ZMod p) ∈
      unitriangular 3 (ZMod p) :=
    CFSG.QuasithinUnique.K1.transvection_mem_unitriangular hlt 1
  have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) =>
    (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (hAU _ htrans)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe] at h
  rw [mul_add, add_mul, mul_one, one_mul] at h
  exact add_left_cancel h

private theorem centralizer_projStabilizer_flagSpace_eq_bot {p : ℕ} [Fact p.Prime] {d : ℕ}
    (hd1 : 1 ≤ d) (hd2 : d < 3) :
    Subgroup.centralizer
      ((projStabilizer (flagSpace 3 (ZMod p) d) :
        Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p))) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨A, rfl⟩ := proj_surjective 3 (ZMod p) g
  have hAU := commute_unitriangular_of_centralizer_projStabilizer (d := d) (A := A) hg
  have hM := commute_single_of_commute_unitriangular (A := A) hAU
  obtain ⟨a, b, hab⟩ :=
    CFSG.QuasithinUnique.K1.eq_smul_one_add_single_of_commute (n := 3) (by norm_num)
      (A : Matrix (Fin 3) (Fin 3) (ZMod p)) hM
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · have hb0 := eq_zero_of_centralizer_flagSpace_one hab hg
    rw [hb0] at hab
    simp only [zero_smul, add_zero] at hab
    exact proj_eq_one_of_eq_smul_one hab
  · have hb0 := eq_zero_of_centralizer_flagSpace_two hab hg
    rw [hb0] at hab
    simp only [zero_smul, add_zero] at hab
    exact proj_eq_one_of_eq_smul_one hab

private theorem centralizer_flagSpace_of_centralizer_projStabilizer {p : ℕ} [Fact p.Prime]
    {W : Submodule (ZMod p) (Fin 3 → ZMod p)} {d : ℕ}
    {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)}
    (hh : (flagSpace 3 (ZMod p) d).map
      (mulVecLin (h : Matrix (Fin 3) (Fin 3) (ZMod p))) = W)
    {g : projectiveSL 3 (ZMod p)}
    (hg : g ∈ Subgroup.centralizer
      ((projStabilizer W : Subgroup (projectiveSL 3 (ZMod p))) :
        Set (projectiveSL 3 (ZMod p)))) :
    (proj 3 (ZMod p) h)⁻¹ * g * proj 3 (ZMod p) h ∈ Subgroup.centralizer
      ((projStabilizer (flagSpace 3 (ZMod p) d) :
        Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p))) := by
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro x hx
  have hy : proj 3 (ZMod p) h * x * (proj 3 (ZMod p) h)⁻¹ ∈ projStabilizer W := by
    have hmap : (projStabilizer (flagSpace 3 (ZMod p) d)).map
        (MulAut.conj (proj 3 (ZMod p) h)) = projStabilizer W := by
      rw [projStabilizer_map_conj, hh]
    have hx' : (MulAut.conj (proj 3 (ZMod p) h)) x ∈
        (projStabilizer (flagSpace 3 (ZMod p) d)).map
          (MulAut.conj (proj 3 (ZMod p) h)) :=
      Subgroup.mem_map_of_mem _ hx
    rwa [hmap] at hx'
  have hcomm := hg _ hy
  calc x * ((proj 3 (ZMod p) h)⁻¹ * g * proj 3 (ZMod p) h) =
      (proj 3 (ZMod p) h)⁻¹ * (proj 3 (ZMod p) h * x * (proj 3 (ZMod p) h)⁻¹ * g) *
        proj 3 (ZMod p) h := by group
    _ = (proj 3 (ZMod p) h)⁻¹ * (g * (proj 3 (ZMod p) h * x *
          (proj 3 (ZMod p) h)⁻¹)) * proj 3 (ZMod p) h := by rw [hcomm]
    _ = ((proj 3 (ZMod p) h)⁻¹ * g * proj 3 (ZMod p) h) * x := by group

private theorem centralizer_projStabilizer_eq_bot {p : ℕ} [Fact p.Prime]
    {W : Submodule (ZMod p) (Fin 3 → ZMod p)} (hW : ⊥ < W ∧ W < ⊤) :
    Subgroup.centralizer
      ((projStabilizer W : Subgroup (projectiveSL 3 (ZMod p))) :
        Set (projectiveSL 3 (ZMod p))) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨h1, h2⟩ := one_le_finrank_and_lt (K := ZMod p) (n := 3) hW.1 hW.2
  obtain ⟨h, hh⟩ := exists_map_flagSpace_eq (K := ZMod p) (n := 3) W
  set d := Module.finrank (ZMod p) ↥W with hddef
  have hg' := centralizer_flagSpace_of_centralizer_projStabilizer (d := d) (h := h) hh hg
  have hg'1 : (proj 3 (ZMod p) h)⁻¹ * g * proj 3 (ZMod p) h = 1 := by
    rw [centralizer_projStabilizer_flagSpace_eq_bot (d := d) h1 h2] at hg'
    exact Subgroup.mem_bot.mp hg'
  have hg_eq : g = proj 3 (ZMod p) h * 1 * (proj 3 (ZMod p) h)⁻¹ := by
    calc g = proj 3 (ZMod p) h * ((proj 3 (ZMod p) h)⁻¹ * g * proj 3 (ZMod p) h) *
          (proj 3 (ZMod p) h)⁻¹ := by group
      _ = proj 3 (ZMod p) h * 1 * (proj 3 (ZMod p) h)⁻¹ := by rw [hg'1]
  rw [hg_eq]
  group

private theorem exists_conjNormal_eq_of_centralizes_isMaxParabolicP
    {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime] {K Y : Subgroup A}
    [K.Normal] (e : ↥K ≃* PSL(3, ZMod p))
    (hY : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p K Y) {a : A}
    (ha : ∀ y ∈ Y, a * y = y * a) :
    ∃ k : ↥K, MulAut.conjNormal a = MulAut.conj k := by
  classical
  let F := ZMod p
  let e' : ↥K ≃* projectiveSL 3 F :=
    e.trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F).symm)
  obtain ⟨hYK, U, hU, hNU⟩ := hY.1
  have hUY : U ≤ Y := fun u hu => hNU ⟨hU.le hu, Subgroup.le_normalizer hu⟩
  have haU : ∀ u ∈ U, a * u = u * a := fun u hu => ha u (hUY hu)
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hsurj : Function.Surjective e'.toMonoidHom := fun x => e'.surjective x
  let S : Sylow p (projectiveSL 3 F) :=
    Sylow.mapSurjective (f := e'.toMonoidHom) hsurj Q
  have hScoe : (S : Subgroup (projectiveSL 3 F)) =
      (U.subgroupOf K).map e'.toMonoidHom := by
    change ((Sylow.mapSurjective (f := e'.toMonoidHom) hsurj Q :
      Sylow p (projectiveSL 3 F)) : Subgroup (projectiveSL 3 F)) = _
    rw [Sylow.coe_mapSurjective, hQ]
  let α' : MulAut (projectiveSL 3 F) :=
    e'.symm.trans ((MulAut.conjNormal a).trans e')
  have hα'fix : ∀ s ∈ (S : Subgroup (projectiveSL 3 F)), α' s = s := by
    intro s hs
    rw [hScoe] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    have hqU : (q : A) ∈ U := hq
    have hqfix : MulAut.conjNormal a q = q := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, haU (q : A) hqU]
      group
    calc α' (e' q) = e' (MulAut.conjNormal a q) := by simp [α']
      _ = e' q := by rw [hqfix]
  obtain ⟨g, hg⟩ := CFSG.ASVolI.burnsideF411a_projSL3_inner_of_fix_sylow p α' S hα'fix
  refine ⟨e'.symm g, MulEquiv.ext fun q => ?_⟩
  apply e'.injective
  calc e' (MulAut.conjNormal a q) = α' (e' q) := by simp [α']
    _ = MulAut.conj g (e' q) := by rw [hg]
    _ = e' (MulAut.conj (e'.symm g) q) := by
        simp [MulAut.conj_apply, mul_assoc]

private theorem eq_of_conjNormal_eq_conj {A : Type} [Group A] {K : Subgroup A} [K.Normal]
    {a : A} {k : ↥K} (h : MulAut.conjNormal a = MulAut.conj k)
    (hCK : Subgroup.centralizer (K : Set A) = ⊥) : a = (k : A) := by
  have hker : (k : A)⁻¹ * a ∈ Subgroup.centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hq := congrArg (fun f : MulAut ↥K => f ⟨x, hx⟩) h
    have hval : a * x * a⁻¹ = (k : A) * x * (k : A)⁻¹ := by
      have h1 := congrArg Subtype.val hq
      rw [MulAut.conjNormal_apply] at h1
      simpa [MulAut.conj_apply] using h1
    have h2 : (k : A)⁻¹ * a * x = x * (k : A)⁻¹ * a := by
      calc (k : A)⁻¹ * a * x = (k : A)⁻¹ * (a * x * a⁻¹) * a := by group
        _ = (k : A)⁻¹ * ((k : A) * x * (k : A)⁻¹) * a := by rw [hval]
        _ = x * (k : A)⁻¹ * a := by group
    simpa [mul_assoc] using h2.symm
  rw [hCK] at hker
  have h1 : (k : A)⁻¹ * a = 1 := Subgroup.mem_bot.mp hker
  exact (inv_mul_eq_one.mp h1).symm

private theorem exists_projStabilizer_eq_map_of_isMaxParabolicP {A : Type} [Group A]
    [Finite A] {p : ℕ} [Fact p.Prime] {K Y : Subgroup A}
    (e' : ↥K ≃* projectiveSL 3 (ZMod p))
    (hY : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p K Y) :
    ∃ W : Submodule (ZMod p) (Fin 3 → ZMod p), ⊥ < W ∧ W < ⊤ ∧
      projStabilizer W = (Y.subgroupOf K).map e'.toMonoidHom := by
  obtain ⟨hYK, -, -, -⟩ := hY.1
  have hYsub : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p (⊤ : Subgroup ↥K)
      (Y.subgroupOf K) :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff hYK).mp hY
  have hYe' : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (projectiveSL 3 (ZMod p))) ((Y.subgroupOf K).map e'.toMonoidHom) :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_of_mulEquiv e'
      (Y.subgroupOf K)).mp hYsub
  have hZgrp : IsMaxParabolicGrp p ((Y.subgroupOf K).map e'.toMonoidHom) :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_top_iff_isMaxParabolicGrp _).mp
      hYe'
  have hZmem : (Y.subgroupOf K).map e'.toMonoidHom ∈
      maximalParabolics (projectiveSL 3 (ZMod p)) p :=
    (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicGrp_iff_mem_maximalParabolics _).mp
      hZgrp
  rw [(maximal_parabolics (K := ZMod p) p (by norm_num : 1 ≤ 3)).1] at hZmem
  obtain ⟨W, ⟨hW0, hWtop⟩, hWZ⟩ := hZmem
  exact ⟨W, hW0, hWtop, hWZ⟩

private theorem eq_one_of_eq_coe_centralizes_isMaxParabolicP
    {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime] {K Y : Subgroup A}
    (e : ↥K ≃* PSL(3, ZMod p))
    (hY : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p K Y)
    {k : ↥K} {a : A} (ha_eq : a = (k : A))
    (ha : ∀ y ∈ Y, a * y = y * a) : a = 1 := by
  classical
  let e' : ↥K ≃* projectiveSL 3 (ZMod p) :=
    e.trans (QuotientGroup.quotientMulEquivOfEq
      (scalars_eq_center 3 (ZMod p)).symm)
  obtain ⟨W, hW0, hWtop, hWZ⟩ := exists_projStabilizer_eq_map_of_isMaxParabolicP e' hY
  have hgZ : e' k ∈ Subgroup.centralizer
      (((Y.subgroupOf K).map e'.toMonoidHom : Subgroup (projectiveSL 3 (ZMod p))) :
        Set (projectiveSL 3 (ZMod p))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyY : (y : A) ∈ Y := hy
    have hky : k * y = y * k := by
      apply Subtype.ext
      show (k : A) * (y : A) = (y : A) * (k : A)
      rw [← ha_eq]
      exact ha (y : A) hyY
    have h1 : e' k * e' y = e' (k * y) := by rw [← map_mul]
    have h2 : e' (k * y) = e' (y * k) := by rw [hky]
    have h3 : e' (y * k) = e' y * e' k := by rw [map_mul]
    exact (h1.trans (h2.trans h3)).symm
  have hgW : e' k ∈ Subgroup.centralizer ((projStabilizer W :
      Subgroup (projectiveSL 3 (ZMod p))) : Set (projectiveSL 3 (ZMod p))) := by
    rw [← hWZ] at hgZ
    exact hgZ
  rw [centralizer_projStabilizer_eq_bot (W := W) ⟨hW0, hWtop⟩] at hgW
  have hk1 : k = 1 := e'.injective (by rw [Subgroup.mem_bot.mp hgW, map_one])
  rw [ha_eq, hk1]
  rfl

theorem eq_one_of_commute_isMaxParabolicP_psl_three {A : Type} [Group A] [Finite A] {p : ℕ}
    [Fact p.Prime] {K Y : Subgroup A} (hK : K.Normal) (e : ↥K ≃* PSL(3, ZMod p))
    (hY : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p K Y)
    (hCK : Subgroup.centralizer (K : Set A) = ⊥) {a : A}
    (ha : ∀ y ∈ Y, a * y = y * a) : a = 1 := by
  classical
  haveI : K.Normal := hK
  obtain ⟨k, hk⟩ := exists_conjNormal_eq_of_centralizes_isMaxParabolicP e hY ha
  have ha_eq : a = (k : A) := eq_of_conjNormal_eq_conj hk hCK
  exact eq_one_of_eq_coe_centralizes_isMaxParabolicP e hY ha_eq ha

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
