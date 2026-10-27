module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem pointRightCosetMul_injective (H : Subgroup G) (g : G) :
    Function.Injective (fun a : pointRightCosetSpace H => pointRightCosetMul H a g) := by
  intro a b hab
  have hh := congrArg (fun c : pointRightCosetSpace H => pointRightCosetMul H c g⁻¹) hab
  simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one] using hh

theorem point_right_transporter (H : Subgroup G) (a b : pointRightCosetSpace H) :
    ∃ g : G, pointRightCosetMul H a g = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  refine ⟨x⁻¹ * y, ?_⟩
  rw [pointRightCosetMul_eq_translate]
  change rightCosetMk H (x * (x⁻¹ * y)) = rightCosetMk H y
  rw [mul_inv_cancel_left]

theorem ambient_sylow_restrict_to_point (p : ℕ) (H : Subgroup G) (P : Sylow p G)
    (hPH : (P : Subgroup G) ≤ H) :
    ∃ R : Sylow p H, (R : Subgroup H).map H.subtype = (P : Subgroup G) := by
  have hrange : (P : Subgroup G) ≤ H.subtype.range := by
    rwa [Subgroup.range_subtype]
  let R := P.comapOfInjective H.subtype H.subtype_injective hrange
  refine ⟨R, ?_⟩
  rw [Sylow.coe_comapOfInjective, Subgroup.map_comap_eq_self hrange]

theorem point_subgroup_transitive_of_base_pair_sylows [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (P : Sylow p G)
    (hPH : (P : Subgroup G) ≤ H)
    (beta : pointRightCosetSpace H)
    (hPfixed : pointFixedSet H (P : Subgroup G) = {rightCosetMk H 1, beta})
    (hpairs : ∀ b : pointRightCosetSpace H, b ≠ rightCosetMk H 1 →
      ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H ⊓ rightCosetStabilizer H b) :
    ∀ b : pointRightCosetSpace H, b ≠ rightCosetMk H 1 →
      ∃ g ∈ H, pointRightCosetMul H beta g = b := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨PH, hPHimage⟩ := ambient_sylow_restrict_to_point p H P hPH
  intro b hb
  obtain ⟨Q, hQ⟩ := hpairs b hb
  obtain ⟨QH, hQHimage⟩ := ambient_sylow_restrict_to_point p H Q (hQ.trans inf_le_left)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H QH PH
  have hconj : rightConjugate (Q : Subgroup G) (g : G)⁻¹ = (P : Subgroup G) := by
    have hh := sylow_ambient_image_smul p H QH g
    rw [hg, hPHimage, hQHimage] at hh
    simpa only [rightConjugate, Subgroup.conjBy, inv_inv] using hh.symm
  have hbQ : b ∈ pointFixedSet H (Q : Subgroup G) :=
    (mem_pointFixedSet_iff H (Q : Subgroup G) b).mpr (hQ.trans inf_le_right)
  have hbP := pointFixedSet_rightConjugate_mem H (Q : Subgroup G) (g : G)⁻¹ hbQ
  rw [hconj, hPfixed] at hbP
  have hbase : pointRightCosetMul H (rightCosetMk H 1) (g : G)⁻¹ = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H _).mpr (H.inv_mem g.property)
  have hnotbase : pointRightCosetMul H b (g : G)⁻¹ ≠ rightCosetMk H 1 := by
    intro heq
    exact hb (pointRightCosetMul_injective H (g : G)⁻¹ (heq.trans hbase.symm))
  have hback : pointRightCosetMul H b (g : G)⁻¹ = beta := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, hnotbase, false_or] using hbP
  refine ⟨g, g.property, ?_⟩
  rw [← hback, pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]

theorem point_right_doubly_transitive_of_point_subgroup
    (H : Subgroup G)
    (hpoint : ∀ b c : pointRightCosetSpace H,
      b ≠ rightCosetMk H 1 → c ≠ rightCosetMk H 1 →
      ∃ g ∈ H, pointRightCosetMul H b g = c) :
    ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d := by
  intro a b c d hab hcd
  obtain ⟨x, hx⟩ := point_right_transporter H a (rightCosetMk H 1)
  obtain ⟨y, hy⟩ := point_right_transporter H c (rightCosetMk H 1)
  have hb : pointRightCosetMul H b x ≠ rightCosetMk H 1 := by
    intro heq
    exact hab (pointRightCosetMul_injective H x (hx.trans heq.symm))
  have hd : pointRightCosetMul H d y ≠ rightCosetMk H 1 := by
    intro heq
    exact hcd (pointRightCosetMul_injective H y (hy.trans heq.symm))
  obtain ⟨n, hn, hbn⟩ := hpoint _ _ hb hd
  have hnbase : pointRightCosetMul H (rightCosetMk H 1) n = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H n).mpr hn
  refine ⟨x * n * y⁻¹, ?_, ?_⟩
  · rw [← pointRightCosetMul_mul, ← pointRightCosetMul_mul, hx, hnbase, ← hy,
      pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
  · rw [← pointRightCosetMul_mul, ← pointRightCosetMul_mul, hbn,
      pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]

theorem point_right_doubly_transitive_of_base_pair_sylows [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (P : Sylow p G)
    (hPH : (P : Subgroup G) ≤ H)
    (beta : pointRightCosetSpace H)
    (hPfixed : pointFixedSet H (P : Subgroup G) = {rightCosetMk H 1, beta})
    (hpairs : ∀ b : pointRightCosetSpace H, b ≠ rightCosetMk H 1 →
      ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H ⊓ rightCosetStabilizer H b) :
    ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d := by
  have ht := point_subgroup_transitive_of_base_pair_sylows H p hp P hPH beta
    hPfixed hpairs
  apply point_right_doubly_transitive_of_point_subgroup H
  intro b c hb hc
  obtain ⟨nb, hnb, hbetab⟩ := ht b hb
  obtain ⟨nc, hnc, hbetac⟩ := ht c hc
  refine ⟨nb⁻¹ * nc, H.mul_mem (H.inv_mem hnb) hnc, ?_⟩
  rw [← hbetab, pointRightCosetMul_mul]
  simp only [mul_inv_cancel_left]
  exact hbetac

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
