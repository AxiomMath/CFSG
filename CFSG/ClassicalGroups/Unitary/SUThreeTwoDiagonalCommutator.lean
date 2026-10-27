module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
import CFSG.ClassicalGroups.Unitary.SUThreeTwoDiagHom
import all CFSG.GH74.QTGen4.Leaves.F112.PSU32Model

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.SpecialLinear
open CFSG.GH74.QTGen4.Leaves.F112 CFSG.Open CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape CFSG.AGLEmbedding.SUQ
open CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Phan
open scoped commutatorElement MatrixGroups

private theorem diagGLHom_eq_diagGL {K : Type} [Field K] {d : ℕ} (t : Fin d → Kˣ) :
    diagGLHom d K t = diagGL t := by
  apply Units.ext
  rw [coe_diagGLHom, coe_diagGL]

private theorem suThree_two_S_diag (K : Type) [Field K] (o : OmegaData K) :
    (OmegaData.sS o : GL (Fin 3) K) * diagGLHom 3 K ![1, omegaUnit o ^ 2, 1] =
      (OmegaData.sD o : GL (Fin 3) K) * diagGLHom 3 K ![1, omegaUnit o ^ 2, 1] *
        (OmegaData.sS o : GL (Fin 3) K) := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGLHom]
  change (mS : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, o.ω ^ 2, 1] =
    mD o.ω * diagonal ![1, o.ω ^ 2, 1] * mS
  have hω := o.hω
  have h2 := o.h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mS, mD, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  all_goals grind

theorem diagGLHom_mem_normalizer_unitarySU_two {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) {d : ℕ} (t : Fin d → Kˣ) :
    diagGLHom d K t ∈ Subgroup.normalizer
      (unitarySU 2 1 K d : Set (GL (Fin d) K)) := by
  let : Finite K := h.finite
  let : CharP K 2 := h.charP
  have hK : Nat.card K = 4 := by simpa using h.card
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  let H := unitarySU 2 1 K d
  have key (t : Fin d → Kˣ) (a : GL (Fin d) K) (ha : a ∈ H) :
      diagGLHom d K t * a * (diagGLHom d K t)⁻¹ ∈ H := by
    let e : Su K 2 1 d ≃* H := MulEquiv.subgroupCongr (SUid_eq_statedSU hF d)
    let X : Su K 2 1 d := e.symm ⟨a, ha⟩
    have hn := (e (dconjSu hK t X)).property
    change diagGL t * a * (diagGL t)⁻¹ ∈ H at hn
    simpa only [diagGLHom_eq_diagGL] using hn
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact key t a
  · intro ha
    have hn := key t⁻¹ _ ha
    have heq : diagGLHom d K t⁻¹ *
        (diagGLHom d K t * a * (diagGLHom d K t)⁻¹) * (diagGLHom d K t⁻¹)⁻¹ = a := by
      rw [map_inv]
      group
    rwa [heq] at hn

theorem commutator_unitarySU_three_two_diagonal {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) :
    ⁅unitarySU 2 1 K 3, (diagGLHom 3 K).range⁆ = unitarySU 2 1 K 3 := by
  let : Finite K := h.finite
  let : CharP K 2 := h.charP
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card K = 4 := by simpa using h.card
  let H := unitarySU 2 1 K 3
  let T := (diagGLHom 3 K).range
  let C := ⁅H, T⁆
  change C = H
  apply le_antisymm
  · change ⁅H, T⁆ ≤ H
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨t, rfl⟩ := hb
    have hn' : diagGLHom 3 K t * a⁻¹ * (diagGLHom 3 K t)⁻¹ ∈ H := by
      exact (Subgroup.mem_normalizer_iff.mp
        (diagGLHom_mem_normalizer_unitarySU_two h t) a⁻¹).mp (H.inv_mem ha)
    simpa only [commutatorElement_def, mul_assoc] using H.mul_mem ha hn'
  · obtain ⟨ω, hω, h2⟩ := exists_omega hK
    let o : OmegaData K := ⟨ω, hω, h2⟩
    let s : GL (Fin 3) K := OmegaData.sS o
    let d : GL (Fin 3) K := OmegaData.sD o
    let z : GL (Fin 3) K := sZ o
    let f : GL (Fin 3) K := OmegaData.sF o
    let g : GL (Fin 3) K := OmegaData.sG o
    let δ : GL (Fin 3) K := diagGLHom 3 K (omegaDiag o)
    have hsH : s ∈ H := (OmegaData.sS o).property
    have hfH : f ∈ H := (OmegaData.sF o).property
    have hgH : g ∈ H := (OmegaData.sG o).property
    have hδT : δ ∈ T := ⟨omegaDiag o, rfl⟩
    have hδ3 : δ ^ 3 = 1 := by
      change (diagGLHom 3 K (omegaDiag o)) ^ 3 = 1
      rw [← map_pow]
      have ht : omegaDiag o ^ 3 = 1 := by
        funext i
        exact unit_pow_three hK (omegaDiag o i)
      rw [ht, map_one]
    have hδeq : δ = diagGL (omegaDiag o) := diagGLHom_eq_diagGL _
    have hF : δ * f * δ⁻¹ = f * g := by
      apply Units.ext
      simp only [Units.val_mul]
      change (δ : Matrix (Fin 3) (Fin 3) K) * mF o.ω *
        ((δ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = mF o.ω * mG o.ω
      rw [hδeq, coe_diagGL_omegaDiag, coe_diagGL_omegaDiag_inv]
      exact mat_dconjOmega_F o
    have hG : δ * g * δ⁻¹ = f := by
      apply Units.ext
      simp only [Units.val_mul]
      change (δ : Matrix (Fin 3) (Fin 3) K) * mG o.ω *
        ((δ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = mF o.ω
      rw [hδeq, coe_diagGL_omegaDiag, coe_diagGL_omegaDiag_inv]
      exact mat_dconjOmega_G o
    have hFG : δ * (f * g) * δ⁻¹ = g := by
      have hh : δ * (δ * (δ * g * δ⁻¹) * δ⁻¹) * δ⁻¹ = g := by
        have htriple : δ * δ * δ = δ ^ 3 := by rw [pow_succ, pow_two]
        have hinv : δ⁻¹ * δ⁻¹ * δ⁻¹ = (δ ^ 3)⁻¹ := by
          rw [← htriple]
          simp only [_root_.mul_inv_rev, mul_assoc]
        calc δ * (δ * (δ * g * δ⁻¹) * δ⁻¹) * δ⁻¹ =
            (δ * δ * δ) * g * (δ⁻¹ * δ⁻¹ * δ⁻¹) := by simp only [mul_assoc]
          _ = g := by rw [htriple, hinv, hδ3]; simp
      rwa [hG, hF] at hh
    have hfC : f ∈ C := by
      have hc := Subgroup.commutator_mem_commutator (H.mul_mem hfH hgH) hδT
      have heq : ⁅f * g, δ⁆ = f := by
        rw [commutatorElement_def]
        calc f * g * δ * (f * g)⁻¹ * δ⁻¹ = (f * g) * (δ * (f * g) * δ⁻¹)⁻¹ := by group
          _ = f := by rw [hFG]; group
      rwa [heq] at hc
    have hgC : g ∈ C := by
      have hc := Subgroup.commutator_mem_commutator hgH hδT
      have heq : ⁅g, δ⁆ * f = g := by
        rw [commutatorElement_def]
        calc g * δ * g⁻¹ * δ⁻¹ * f = g * (δ * g * δ⁻¹)⁻¹ * f := by group
          _ = g := by rw [hG]; group
      have hm := C.mul_mem hc hfC
      rwa [heq] at hm
    have hdC : d ∈ C := by
      have hc := Subgroup.commutator_mem_commutator hsH
        (show diagGLHom 3 K ![1, omegaUnit o ^ 2, 1] ∈ T from ⟨_, rfl⟩)
      have heq : ⁅s, diagGLHom 3 K ![1, omegaUnit o ^ 2, 1]⁆ = d := by
        rw [commutatorElement_def]
        rw [show s * diagGLHom 3 K ![1, omegaUnit o ^ 2, 1] =
          d * diagGLHom 3 K ![1, omegaUnit o ^ 2, 1] * s from suThree_two_S_diag K o]
        group
      rwa [heq] at hc
    have hFS : f * s = d * f :=
      congrArg (fun x : SUg K => (x : GL (Fin 3) K)) (sF_mul_sS o)
    have hsC : s ∈ C := by
      have hm := C.mul_mem (C.mul_mem (C.inv_mem hfC) hdC) hfC
      have heq : f⁻¹ * d * f = s := by rw [mul_assoc, ← hFS]; group
      rwa [heq] at hm
    have hSD : s * d = z ^ 2 * (d * s) :=
      congrArg (fun x : SUg K => (x : GL (Fin 3) K)) (sS_mul_sD o)
    have hz3 : z ^ 3 = 1 :=
      congrArg (fun x : SUg K => (x : GL (Fin 3) K)) (sZ_cube o)
    have hzC : z ∈ C := by
      have hc : ⁅s, d⁆ ∈ C := by
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem hsC hdC) (C.inv_mem hsC)) (C.inv_mem hdC)
      have heq : ⁅s, d⁆ = z ^ 2 := by rw [commutatorElement_def, hSD]; group
      rw [heq] at hc
      have hm := C.mul_mem hc hc
      have hp : z ^ 2 * z ^ 2 = z := by
        calc z ^ 2 * z ^ 2 = z ^ 3 * z := by group
          _ = z := by rw [hz3]; group
      rwa [hp] at hm
    let B : Subgroup (SUg K) := C.comap (StatedSU 3 2 K).subtype
    have hsB : OmegaData.sS o ∈ B := hsC
    have hdB : OmegaData.sD o ∈ B := hdC
    have hzB : sZ o ∈ B := hzC
    have hfB : OmegaData.sF o ∈ B := hfC
    have hgB : OmegaData.sG o ∈ B := hgC
    have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
      ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
    have hcard : Nat.card (SUg K) = 216 := by
      have hc := CFSG.SectionRank.OddCover.card_statedSU_three (p := 2) (f := 1)
        (K := K) (by simpa using hK)
      norm_num at hc
      exact hc
    have hG2 : OmegaData.sG o ^ 2 = OmegaData.sF o ^ 2 := by
      rw [sG_sq, CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape.sF_sq]
    have hGF : OmegaData.sG o * OmegaData.sF o * (OmegaData.sG o)⁻¹ =
        (OmegaData.sF o)⁻¹ := by
      rw [sG_mul_sF, ← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape.sF_sq o,
        mul_inv_cancel_right, eq_inv_iff_mul_eq_one]
      calc OmegaData.sF o * OmegaData.sF o ^ 2 * OmegaData.sF o = OmegaData.sF o ^ 4 := by group
        _ = 1 := sF_four o
    have hgen := closure_heisSubgroup_union_eq_top hcard hrel (sZ_ne_one o)
      (sF_four o) (sF_sq_ne_one o) hG2 hGF
    have hEB : heisSubgroup hrel ≤ B := by
      intro x hx
      obtain ⟨i, j, k, rfl⟩ := (mem_heisSubgroup hrel).mp hx
      exact B.mul_mem (B.mul_mem (B.pow_mem hzB i) (B.pow_mem hdB j)) (B.pow_mem hsB k)
    have hcl : Subgroup.closure
        ((heisSubgroup hrel : Set (SUg K)) ∪ {OmegaData.sF o, OmegaData.sG o}) ≤ B := by
      refine (Subgroup.closure_le B).mpr fun x hx => ?_
      rcases hx with hx | hx
      · exact hEB hx
      · rcases hx with rfl | rfl
        · exact hfB
        · exact hgB
    rw [hgen] at hcl
    have hB : B = ⊤ := top_unique hcl
    intro x hx
    have hm : (⟨x, hx⟩ : SUg K) ∈ B := by rw [hB]; exact Subgroup.mem_top _
    exact hm

end CFSG.ClassicalGroups.UnitaryFlag

end
