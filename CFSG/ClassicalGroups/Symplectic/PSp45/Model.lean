module

public import CFSG.ClassicalGroups.Symplectic.PSp45.PresData
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.ClassicalGroups.Symplectic.PSp45

open CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras
open scoped Matrix

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev Sp45 : Type := StatedSp 2 (ZMod 5)

abbrev PSp45 : Type := StatedProj (StatedSp 2 (ZMod 5))

@[expose] def genMat4 : Fin 8 → Matrix (Fin 4) (Fin 4) (ZMod 5) := ![
  !![1,0,0,0; 0,1,0,0; 1,0,1,0; 0,0,0,1],
  !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,1,0,1],
  !![1,0,0,0; 0,1,0,0; 0,3,1,0; 3,0,0,1],
  !![1,0,0,0; 3,1,0,0; 0,0,1,2; 0,0,0,1],
  !![2,0,0,0; 0,1,0,0; 0,0,3,0; 0,0,0,1],
  !![1,0,0,0; 0,2,0,0; 0,0,1,0; 0,0,0,3],
  !![0,1,0,0; 4,0,0,0; 0,0,0,1; 0,0,4,0],
  !![1,0,0,0; 0,0,0,4; 0,0,1,0; 0,1,0,0]]

@[expose] def genMat (i : Fin 8) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (genMat4 i)

theorem genMat_symplectic (i : Fin 8) :
    (genMat i)ᵀ * gram (ZMod 5) 2 * genMat i = gram (ZMod 5) 2 := by
  fin_cases i <;> decide +kernel

@[expose] noncomputable def psp45Gen (i : Fin 8) : Sp45 :=
  ofSymplecticMat (genMat i) (genMat_symplectic i)

@[expose] noncomputable def psp45GenP (i : Fin 8) : PSp45 :=
  QuotientGroup.mk (psp45Gen i)

theorem lift_psp45GenP_rels :
    ∀ r ∈ pspRels, FreeGroup.lift psp45GenP (FreeGroup.mk r) = 1 := by
  have hsinv : ∀ i : Fin 8,
      mat 2 (ZMod 5) ((psp45Gen i)⁻¹) = -(gram (ZMod 5) 2 * (genMat i)ᵀ * gram (ZMod 5) 2) := by
    intro i
    unfold psp45Gen
    rw [mat_inv_eq, mat_ofSymplecticMat]
    rfl
  let evalW : List (Fin 8 × Bool) → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
    fun w => (w.map fun x => cond x.2 (genMat x.1)
      (-(gram (ZMod 5) 2 * (genMat x.1)ᵀ * gram (ZMod 5) 2))).prod
  have hword : ∀ w : List (Fin 8 × Bool), mat 2 (ZMod 5)
      (List.prod (w.map fun x => cond x.2 (psp45Gen x.1) (psp45Gen x.1)⁻¹)) = evalW w := by
    intro w
    induction w with
    | nil => simp [evalW]
    | cons x xs ih =>
      rcases x with ⟨i, b⟩
      cases b
      · simp only [List.map_cons, List.prod_cons, cond_false, evalW, List.map_cons,
          List.prod_cons]
        rw [map_mul, hsinv i, ih]
      · simp only [List.map_cons, List.prod_cons, cond_true, evalW, List.map_cons,
          List.prod_cons]
        rw [map_mul]
        rw [show mat 2 (ZMod 5) (psp45Gen i) = genMat i from by
          unfold psp45Gen
          rw [mat_ofSymplecticMat]]
        rw [ih]
  have hpm : ∀ w ∈ pspRels, evalW w = 1 ∨ evalW w = -1 := by
    intro w hw
    revert w
    decide +kernel
  intro r hr
  rw [FreeGroup.lift_mk]
  have hproj : (List.prod (r.map fun x => cond x.2 (psp45GenP x.1) (psp45GenP x.1)⁻¹)) =
      QuotientGroup.mk (List.prod (r.map fun x => cond x.2 (psp45Gen x.1) (psp45Gen x.1)⁻¹)) := by
    simp only [psp45GenP]
    clear hr
    induction r with
    | nil => simp
    | cons x xs ih =>
      rcases x with ⟨i, b⟩
      cases b <;> simp only [List.map_cons, List.prod_cons, cond_false, cond_true] at ih ⊢
      · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ih]
      · rw [QuotientGroup.mk_mul, ih]
  rw [hproj]
  apply (QuotientGroup.eq_one_iff _).2
  rcases hpm r hr with h1 | hneg1
  ·
    have hx : List.prod (r.map fun x => cond x.2 (psp45Gen x.1) (psp45Gen x.1)⁻¹) = 1 :=
      CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective ((hword r).trans h1)
    rw [hx]
    exact Subgroup.one_mem _
  ·
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    refine ⟨-1, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    have h := (hword r).trans hneg1
    change Matrix.scalar (Fin 2 ⊕ Fin 2) (-1 : ZMod 5) =
      mat 2 (ZMod 5) (List.prod (r.map fun x => cond x.2 (psp45Gen x.1) (psp45Gen x.1)⁻¹))
    rw [h]
    decide +kernel

theorem card_sp45 : Nat.card Sp45 = 9360000 := by
  rw [Sp45, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, Nat.card_zmod]
  norm_num

private theorem card_scalars_sp45 :
    Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5))) = 2 := by
  have h : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf
      (StatedSp 2 (ZMod 5))) = Nat.card {c : (ZMod 5)ˣ // (c : ZMod 5) ^ 2 = 1} := by
    apply Nat.card_congr
    refine {
      toFun := fun x => ⟨Classical.choose x.2, ?_⟩,
      invFun := fun c => ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c.1,
        (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (K := ZMod 5) (by norm_num)
          c.1).2 (by
            apply Units.ext
            simpa using c.2)⟩, ⟨c.1, by rfl⟩⟩,
      left_inv := ?_,
      right_inv := ?_ }
    ·
      have hc := Classical.choose_spec x.2
      have hsp : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Classical.choose x.2) ∈
          StatedSp 2 (ZMod 5) := by rw [hc]; exact x.1.2
      have hsq : Classical.choose x.2 ^ 2 = 1 :=
        (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (K := ZMod 5) (by norm_num)
          (Classical.choose x.2)).1 hsp
      simpa using congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) hsq
    ·
      intro x
      apply Subtype.ext
      apply Subtype.ext
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using Classical.choose_spec x.2
    ·
      intro c
      apply Subtype.ext
      apply Units.ext
      have hspec := Classical.choose_spec (show Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2)
          c.1 ∈ StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5) from ⟨c.1, rfl⟩)
      have h2 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) (ZMod 5) =>
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))) hspec
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_inj] using h2
  rw [h]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_psp45 : Nat.card PSp45 = 4680000 := by
  have hN := card_scalars_sp45
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5)))
  rw [card_sp45, hN] at hcard
  have h2 : Nat.card PSp45 * 2 = 4680000 * 2 :=
    hcard.symm.trans (by norm_num : (9360000 : Nat) = 4680000 * 2)
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) h2

end CFSG.ClassicalGroups.Symplectic.PSp45
