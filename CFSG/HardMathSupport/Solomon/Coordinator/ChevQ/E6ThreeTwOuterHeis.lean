module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlaneStmt
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlanePair
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlaneLift
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.LieType.SeitzGeneration

theorem twOuterHeisPlane_holds :
    TwOuterHeisPlane := by
  intro ℓ f K _ h hq3 hq γ₁ γ₂ hne hcomm h13 h23 hind hout
  set D := Subgroup.closure ({suConj h γ₁, suConj h γ₂} :
    Set (MulAut (unitarySU ℓ f K 3))) with hD
  have haD : suConj h γ₁ ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbD : suConj h γ₂ ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hD3 : ∀ φ ∈ D, φ ^ 3 = 1 := fun φ hφ =>
    twPlane_pow_three_of_mem_closure_pair hcomm h13 h23 hφ
  have hD9 : Nat.card D = 9 := twPlane_card_closure_pair hcomm h13 h23 hind
  have hDle : D ≤ (suConj h).range := by
    rw [hD, Subgroup.closure_le]
    intro φ hφ
    rcases hφ with rfl | hφ
    · exact ⟨γ₁, rfl⟩
    · rcases hφ with rfl
      exact ⟨γ₂, rfl⟩
  obtain ⟨w, hw⟩ := twPlane_exists_comm_scalar hcomm
  have hw3 : w ^ 3 = 1 := twPlane_comm_scalar_cube hw
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hne
    apply Subtype.ext
    rw [map_one, one_mul] at hw
    exact hw.symm
  obtain ⟨α, -, hα⟩ := twPlane_exists_scalar_of_suConj_eq_one (A := γ₁ ^ 3)
    (by rw [map_pow]; exact h13)
  obtain ⟨β, -, hβ⟩ := twPlane_exists_scalar_of_suConj_eq_one (A := γ₂ ^ 3)
    (by rw [map_pow]; exact h23)
  have hx3 : (((γ₁ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (α : K) • 1 := by
    have h1 : (γ₁ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) α := hα
    rw [h1, twPlane_coe_scalar]
  have hy3 : (((γ₂ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (β : K) • 1 := by
    have h1 : (γ₂ : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) β := hβ
    rw [h1, twPlane_coe_scalar]
  haveI : Finite K := h.finite
  have hq' : ℓ ^ f % 3 = 2 := by omega
  have hpos : 0 < ℓ ^ f := pow_pos h.prime.pos f
  have hq2 : 2 < ℓ ^ f := by omega
  have hF3 : 3 ∣ Nat.card K - 1 := by
    have hcard : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq']
    omega
  obtain ⟨a, b, s, hs, hab, hcube⟩ := exists_cube_line (n := 3) hF3
    (x := (γ₁ : GL (Fin 3) K)) (y := (γ₂ : GL (Fin 3) K))
    (w := GeneralLinearGroup.scalar (Fin 3) w) (fun g => (commute_scalar w g).symm)
    (by rw [← map_pow, hw3, map_one]) hw α.ne_zero β.ne_zero hx3 hy3
  have hmoved : ∃ e ∈ D, ∃ t : unitarySU ℓ f K 3, t ^ 3 = 1 ∧ MulAut.conj t ∈ D ∧ e t ≠ t := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      have hc : (((γ₁ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (s ^ 3) • 1 := by simpa only [pow_one, pow_zero, mul_one] using hcube
      exact twPlane_exists_moved hq3 hw1 hs hw hc haD hbD
    ·
      have hc : (((γ₂ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (s ^ 3) • 1 := by simpa only [pow_one, pow_zero, one_mul] using hcube
      have hconj : (γ₁ : GL (Fin 3) K) * γ₂ =
          GeneralLinearGroup.scalar (Fin 3) w⁻¹ * ((γ₂ : GL (Fin 3) K) * γ₁) := by
        rw [hw, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      exact twPlane_exists_moved hq3 (inv_ne_one.2 hw1) hs hconj hc hbD haD
    ·
      have hc : ((((γ₁ * γ₂ : unitaryIsom3 h) : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = (s ^ 3) • 1 := by
        rw [Subgroup.coe_mul]
        simpa only [pow_one] using hcube
      have hconj : (γ₂ : GL (Fin 3) K) * ((γ₁ * γ₂ : unitaryIsom3 h) : GL (Fin 3) K) =
          GeneralLinearGroup.scalar (Fin 3) w *
            (((γ₁ * γ₂ : unitaryIsom3 h) : GL (Fin 3) K) * γ₂) := by
        show (γ₂ : GL (Fin 3) K) * ((γ₁ : GL (Fin 3) K) * γ₂) =
          GeneralLinearGroup.scalar (Fin 3) w * ((γ₁ : GL (Fin 3) K) * γ₂ * γ₂)
        rw [← mul_assoc, hw, mul_assoc]
      refine twPlane_exists_moved hq3 hw1 hs hconj hc ?_ hbD
      rw [map_mul]
      exact D.mul_mem haD hbD
    ·
      have hc : ((((γ₁ * γ₂ ^ 2 : unitaryIsom3 h) : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = (s ^ 3) • 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        simpa only [pow_one] using hcube
      have hconj : (γ₂ : GL (Fin 3) K) * ((γ₁ * γ₂ ^ 2 : unitaryIsom3 h) : GL (Fin 3) K) =
          GeneralLinearGroup.scalar (Fin 3) w *
            (((γ₁ * γ₂ ^ 2 : unitaryIsom3 h) : GL (Fin 3) K) * γ₂) := by
        show (γ₂ : GL (Fin 3) K) * ((γ₁ : GL (Fin 3) K) * (γ₂ : GL (Fin 3) K) ^ 2) =
          GeneralLinearGroup.scalar (Fin 3) w *
            ((γ₁ : GL (Fin 3) K) * (γ₂ : GL (Fin 3) K) ^ 2 * γ₂)
        have e1 : (γ₂ : GL (Fin 3) K) * ((γ₁ : GL (Fin 3) K) * (γ₂ : GL (Fin 3) K) ^ 2) =
            (γ₂ * γ₁) * (γ₂ : GL (Fin 3) K) ^ 2 := by group
        have e2 : GeneralLinearGroup.scalar (Fin 3) w * ((γ₁ : GL (Fin 3) K) * γ₂) *
            (γ₂ : GL (Fin 3) K) ^ 2 = GeneralLinearGroup.scalar (Fin 3) w *
              ((γ₁ : GL (Fin 3) K) * (γ₂ : GL (Fin 3) K) ^ 2 * γ₂) := by
          group
        rw [e1, hw, e2]
      refine twPlane_exists_moved hq3 hw1 hs hconj hc ?_ hbD
      rw [map_mul, map_pow]
      exact D.mul_mem haD (D.pow_mem hbD 2)
  exact CFSG.RankThree.PartTwo.Sec19.seitz199OuterUnitaryDiag_holds ℓ f K h hq' hq2 D hD3 hD9 hout
    hmoved hDle

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
