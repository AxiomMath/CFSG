module

public import CFSG.ClassicalInvolution.Phan.Phan3SL3Pres
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.SL3PresData
public import Certificates.Certificate753504
public import CFSG.Certificates.CosetTableOrders
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.ClassicalInvolution.Phan.Phan3PermModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

scoped instance instFactPrimeSevenONPair : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem wordVal_sl3Gen_rels7 : ∀ r ∈ sl3Rels7, wordVal (sl3Gen (ZMod 7)) r = 1 := by
  decide +kernel

theorem transvection_natCast_eq_pow {i j : Fin 3} (hij : i ≠ j) (n : ℕ) :
    transvection hij (n : ZMod 7) = transvection hij (1 : ZMod 7) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, transvection_add, ih, pow_succ]

theorem sl3Gen7_closure : Subgroup.closure (Set.range (sl3Gen (ZMod 7))) = ⊤ := by
  set H := Subgroup.closure (Set.range (sl3Gen (ZMod 7))) with hH
  have g0 : transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 7) ∈ H :=
    Subgroup.subset_closure ⟨0, rfl⟩
  have g1 : transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 7) ∈ H :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have g2 : transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 7) ∈ H :=
    Subgroup.subset_closure ⟨2, rfl⟩
  have g3 : transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 7) ∈ H :=
    Subgroup.subset_closure ⟨3, rfl⟩
  have g02 : transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 7) ∈ H := by
    have := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 7) 1
    rw [mul_one] at this
    rw [← this, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem g0 g2) (H.inv_mem g0)) (H.inv_mem g2)
  have g20 : transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 7) ∈ H := by
    have := commutatorElement_transvection (show (2 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 7) 1
    rw [mul_one] at this
    rw [← this, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem g3 g1) (H.inv_mem g3)) (H.inv_mem g1)
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j), transvection hij (1 : ZMod 7) ∈ H := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
  rw [eq_top_iff, ← closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 3) (K := ZMod 7),
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, ← ZMod.natCast_zmod_val c,
    transvection_natCast_eq_pow]
  exact H.pow_mem (hall i j hij) _

theorem card_SL3_zmod_seven : Nat.card SL(3, ZMod 7) = 5630688 := by
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.card_SL_three, Nat.card_zmod]
  norm_num


theorem sl3_lift7 {X : Type} [Group X] (x : Fin 4 → X) (hx : ∀ r ∈ sl3Rels7, wordVal x r = 1) :
    ∃ θ : SL(3, ZMod 7) →* X, ∀ i, θ (sl3Gen (ZMod 7) i) = x i := by
  obtain ⟨hfin, hle⟩ := Certificates.certificate753504
  let p : PG 4 sl3Rels7 →* SL(3, ZMod 7) := PresentedGroup.toGroup (f := sl3Gen (ZMod 7)) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact wordVal_sl3Gen_rels7 w hw)
  have hp : ∀ i, p (PresentedGroup.of i) = sl3Gen (ZMod 7) i := fun i =>
    PresentedGroup.toGroup.of _
  have hsurj : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← sl3Gen7_closure, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hp i⟩
  have hbij : Function.Bijective p := by
    have := hfin
    refine hsurj.bijective_of_nat_card_le ?_
    rw [card_SL3_zmod_seven]
    exact hle
  let e : PG 4 sl3Rels7 ≃* SL(3, ZMod 7) := MulEquiv.ofBijective p hbij
  let q : PG 4 sl3Rels7 →* X := PresentedGroup.toGroup (f := x) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact hx w hw)
  refine ⟨q.comp e.symm.toMonoidHom, fun i => ?_⟩
  have : e.symm (sl3Gen (ZMod 7) i) = PresentedGroup.of i := by
    rw [← hp i]
    exact e.symm_apply_apply (PresentedGroup.of i)
  show q (e.symm (sl3Gen (ZMod 7) i)) = x i
  rw [this]
  exact PresentedGroup.toGroup.of _


@[expose] def sl3Omega7 : SL(3, ZMod 7) :=
  ⟨Matrix.scalar (Fin 3) (2 : ZMod 7), by decide⟩

@[expose] def sl3OmegaCodes7 : List Nat :=
  [0, 0, 2, 2, 2, 0, 3, 3, 3, 3, 3, 3, 1, 4, 4, 4, 4, 6, 6, 6, 6, 6, 4, 4, 4, 7, 7, 7, 7, 7, 7,
   5]

theorem wordVal_sl3Omega7 :
    wordVal (sl3Gen (ZMod 7)) (decodeWord 4 sl3OmegaCodes7) = sl3Omega7 := by
  decide +kernel

theorem center_eq_zpowers_sl3Omega7 :
    Subgroup.center SL(3, ZMod 7) = Subgroup.zpowers sl3Omega7 := by
  apply le_antisymm
  · intro A hA
    obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Fintype.card_fin] at hr
    have key : ∀ s : ZMod 7, s ^ 3 = 1 → s = 1 ∨ s = 2 ∨ s = 4 := by decide
    have hr' := key r hr
    rcases hr' with rfl | rfl | rfl
    · have : A = 1 := Subtype.ext (by
        rw [← hAr]
        ext i j
        fin_cases i <;> fin_cases j <;> decide)
      rw [this]
      exact Subgroup.one_mem _
    · have : A = sl3Omega7 := Subtype.ext (by rw [← hAr]; rfl)
      rw [this]
      exact Subgroup.mem_zpowers _
    · have : A = sl3Omega7 ^ 2 := Subtype.ext (by
        rw [← hAr, Matrix.SpecialLinearGroup.coe_pow]
        ext i j
        fin_cases i <;> fin_cases j <;> decide)
      rw [this]
      exact Subgroup.npow_mem_zpowers _ 2
  · rw [Subgroup.zpowers_le]
    exact Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨2, by decide, rfl⟩

theorem ker_eq_center_of_sl3Omega7 {X : Type} [Group X] (θ : SL(3, ZMod 7) →* X)
    (h1 : θ (sl3Gen (ZMod 7) 0) ≠ 1) (hω : θ sl3Omega7 = 1) :
    θ.ker = Subgroup.center SL(3, ZMod 7) := by
  refine le_antisymm (sl3_ker_le_center θ 0 h1) ?_
  rw [center_eq_zpowers_sl3Omega7, Subgroup.zpowers_le]
  exact hω

noncomputable def projectiveSL_mulEquiv_range {X : Type} [Group X] (θ : SL(3, ZMod 7) →* X)
    (h1 : θ (sl3Gen (ZMod 7) 0) ≠ 1) (hω : θ sl3Omega7 = 1) :
    projectiveSL 3 (ZMod 7) ≃* θ.range :=
  (QuotientGroup.quotientMulEquivOfEq
    ((scalars_eq_center 3 (ZMod 7)).trans (ker_eq_center_of_sl3Omega7 θ h1 hω).symm)).trans
    (QuotientGroup.quotientKerEquivRange θ)

theorem card_center_SL3_zmod_seven : Nat.card (Subgroup.center SL(3, ZMod 7)) = 3 := by
  rw [center_eq_zpowers_sl3Omega7, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro h
    have := congrArg (fun A : SL(3, ZMod 7) => (A : Matrix (Fin 3) (Fin 3) (ZMod 7)) 0 0) h
    exact absurd this (by decide)

theorem card_range_of_lift {X : Type} [Group X] (θ : SL(3, ZMod 7) →* X)
    (h1 : θ (sl3Gen (ZMod 7) 0) ≠ 1) (hω : θ sl3Omega7 = 1) : Nat.card θ.range = 1876896 := by
  have h := CFSG.ClassicalInvolution.RouteD.Gaps.card_eq_range_mul_ker θ
  rw [card_SL3_zmod_seven, ker_eq_center_of_sl3Omega7 θ h1 hω, card_center_SL3_zmod_seven] at h
  omega

theorem range_eq_closure_of_lift {X : Type} [Group X] (θ : SL(3, ZMod 7) →* X) :
    θ.range = Subgroup.closure (Set.range fun i => θ (sl3Gen (ZMod 7) i)) := by
  rw [MonoidHom.range_eq_map, ← sl3Gen7_closure, MonoidHom.map_closure, ← Set.range_comp]
  rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
