module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenGroup
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenInner
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenO3
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOT
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.TableBExc.Three (modelN modelN_single)
open CFSG.StandardType.TableBExc.E6Three (gE6 isModel_E6)

set_option linter.unusedSectionVars false

private def e6CenOB_a : Multiplicative (Fin 3 → ZMod 3) := .ofAdd ![1, 2, 0]

private def e6CenOB_b : Multiplicative (Fin 3 → ZMod 3) := .ofAdd ![0, 1, 2]

private theorem e6CenOB_cases : ∀ m n : Fin 3,
    (∃ k : Fin 3, e6CenOB_a ^ (m : ℕ) * e6CenOB_b ^ (n : ℕ) =
      (e6CenOB_a * e6CenOB_b ^ 2) ^ (k : ℕ)) ∨
    ∃ p q r t : Fin 3,
      (e6CenOB_a ^ (m : ℕ) * e6CenOB_b ^ (n : ℕ)) ^ (p : ℕ) *
          (e6CenOB_a * e6CenOB_b ^ 2) ^ (q : ℕ) = e6CenOB_a ∧
        (e6CenOB_a ^ (m : ℕ) * e6CenOB_b ^ (n : ℕ)) ^ (r : ℕ) *
          (e6CenOB_a * e6CenOB_b ^ 2) ^ (t : ℕ) = e6CenOB_b := by
  decide +kernel

private theorem e6CenOB_g (i : Fin 3) : modelN isModel_E6 (.ofAdd (Pi.single i 1)) = gE6 i := by
  rw [modelN_single, show (1 : ZMod 3).val = 1 from rfl, pow_one]

private theorem e6CenOB_hA : gE6 0 * gE6 1 ^ 2 = modelN isModel_E6 e6CenOB_a := by
  rw [show e6CenOB_a = .ofAdd (Pi.single 0 1) * .ofAdd (Pi.single 1 1) ^ 2 by decide +kernel,
    map_mul, map_pow, e6CenOB_g, e6CenOB_g]

private theorem e6CenOB_hB : gE6 1 * gE6 2 ^ 2 = modelN isModel_E6 e6CenOB_b := by
  rw [show e6CenOB_b = .ofAdd (Pi.single 1 1) * .ofAdd (Pi.single 2 1) ^ 2 by decide +kernel,
    map_mul, map_pow, e6CenOB_g, e6CenOB_g]

private theorem e6CenOB_hz : e6CenZ = modelN isModel_E6 (e6CenOB_a * e6CenOB_b ^ 2) := by
  rw [show e6CenOB_a * e6CenOB_b ^ 2 =
      .ofAdd (Pi.single 0 1) * .ofAdd (Pi.single 1 1) * .ofAdd (Pi.single 2 1) by decide +kernel,
    map_mul, map_mul, e6CenOB_g, e6CenOB_g, e6CenOB_g]
  rfl

section Census

variable
  {K : Type} [Field K] {ω : Kˣ}

theorem e6Cen_OB [Finite K] (hK : 3 ∣ Nat.card K - 1) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcube : E6CenCube K E)
    (hF : E6CenFrame e6CenOB E) : E6CenConcl K E := by
  obtain ⟨hE, -, -, hEi, -, hA⟩ := hcube
  have hK4 := e6Cen_four_le_card hK
  obtain ⟨X, hXE, hX⟩ := hF.2 (gE6 0 * gE6 1 ^ 2) (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨Y, hYE, hY⟩ := hF.2 (gE6 1 * gE6 2 ^ 2)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hc : ∀ V ∈ E, X * V = V * X := fun V hVE =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨X, hXE⟩ : E) ⟨V, hVE⟩)
  have hWi := e6Cen_inner_OB hK hX hY (hE.2 _ hXE) (hE.2 _ hYE) (hc Y hYE)
  have hWE : X * Y ^ 2 ∈ E := mul_mem hXE (pow_mem hYE 2)
  have hW : BmMono (X * Y ^ 2) e6CenZ := by
    have h := hX.mul (hY.pow 2)
    rw [e6CenOB_hA, e6CenOB_hB, ← map_pow, ← map_mul, ← e6CenOB_hz] at h
    exact h
  have hzI : modelN isModel_E6 (e6CenOB_a * e6CenOB_b ^ 2) ∈
      e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) := by
    rw [← e6CenOB_hz]
    exact mem_e6CenImage.2 ⟨_, Subgroup.mem_inf.2 ⟨hWE, hWi⟩, hW⟩
  have hXI : gE6 0 * gE6 1 ^ 2 ∈ e6CenImage E := mem_e6CenImage.2 ⟨X, hXE, hX⟩
  have hYI : gE6 1 * gE6 2 ^ 2 ∈ e6CenImage E := mem_e6CenImage.2 ⟨Y, hYE, hY⟩
  refine (hA fun s hs hs1 => ?_).elim
  obtain ⟨v, hv, hsv⟩ := hF.1 _ hs
  obtain ⟨m, n, hm, hn, rfl⟩ := e6Cen_mem_closure_pair (e6CenImage_mul_comm hK4 hE hXI hYI)
    (e6CenImage_pow_three hK4 hE hXI) (e6CenImage_pow_three hK4 hE hYI) hv
  have hvI : (gE6 0 * gE6 1 ^ 2) ^ m * (gE6 1 * gE6 2 ^ 2) ^ n ∈
      e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) :=
    mem_e6CenImage.2 ⟨_, Subgroup.mem_inf.2 ⟨hs, ⟨s, rfl⟩⟩, hsv⟩
  rw [e6CenOB_hA, e6CenOB_hB, ← map_pow, ← map_pow, ← map_mul] at hvI hsv
  rcases e6CenOB_cases ⟨m, hm⟩ ⟨n, hn⟩ with ⟨k, hk⟩ | ⟨p, q, r, t, hpq, hrt⟩
  · refine e6Cen_finrank_eq_24_of_zpowers hK4 h3 h1 hE hWE hW
      (fun a b c hd => e6Cen_Tz_fix_g0g1sq h3 h1 hX (hc _ hd)) hs hs1 hsv ?_
    have hk' : e6CenOB_a ^ m * e6CenOB_b ^ n = (e6CenOB_a * e6CenOB_b ^ 2) ^ (k : ℕ) := hk
    rw [hk', map_pow, ← e6CenOB_hz]
    exact Subgroup.npow_mem_zpowers _ _
  · have hAI : gE6 0 * gE6 1 ^ 2 ∈
        e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) := by
      rw [e6CenOB_hA, ← hpq, map_mul, map_pow, map_pow]
      exact mul_mem (pow_mem hvI _) (pow_mem hzI _)
    have hBI : gE6 1 * gE6 2 ^ 2 ∈
        e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) := by
      rw [e6CenOB_hB, ← hrt, map_mul, map_pow, map_pow]
      exact mul_mem (pow_mem hvI _) (pow_mem hzI _)
    refine (hEi (e6Cen_le_innerAut_of_frame h3 h1 hE hF hWE hW ?_)).elim
    rintro _ (rfl | rfl)
    exacts [hAI, hBI]

end Census

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
