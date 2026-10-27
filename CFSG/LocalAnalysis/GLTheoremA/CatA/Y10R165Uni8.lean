module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial Polynomial
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open CFSG.LinearGroups

section General

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n p q : ℕ} {h : UnitaryFieldData 2 n K}
variable {B : V →ₛₗ[h.bar] V →ₗ[K] K}

theorem four_le_orderOf_neg_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : ¬ p ∣ 3) :
    4 ≤ orderOf (-(2 : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx0 : (-(2 : ZMod p)) ≠ 0 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by rw [← neg_eq_zero]; exact h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  have hfin : IsOfFinOrder (-(2 : ZMod p)) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by have := hp.two_le; omega,
      ZMod.pow_card_sub_one_eq_one hx0⟩
  have hpos : 0 < orderOf (-(2 : ZMod p)) := hfin.orderOf_pos
  have hp3' : (3 : ZMod p) ≠ 0 := by
    intro h
    exact hp3 ((ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h))
  rcases Nat.lt_or_ge (orderOf (-(2 : ZMod p))) 4 with h | h
  · have h1 : orderOf (-(2 : ZMod p)) = 1 ∨ orderOf (-(2 : ZMod p)) = 2 ∨
        orderOf (-(2 : ZMod p)) = 3 := by omega
    rcases h1 with h1 | h1 | h1
    · have hx : (-(2 : ZMod p)) = 1 := orderOf_eq_one_iff.mp h1
      have hzero : (3 : ZMod p) = 0 := by
        calc (3 : ZMod p) = 1 + 2 := by norm_num
          _ = -(2 : ZMod p) + 2 := by rw [hx]
          _ = 0 := by ring
      exfalso; exact hp3' hzero
    · have hx : (-(2 : ZMod p)) ^ 2 = 1 := by
        rw [← h1]; exact pow_orderOf_eq_one _
      have hzero : (3 : ZMod p) = 0 := by
        have h4 : (4 : ZMod p) = 1 := by
          calc (4 : ZMod p) = (-(2 : ZMod p)) ^ 2 := by ring
            _ = 1 := hx
        calc (3 : ZMod p) = 4 - 1 := by norm_num
          _ = 1 - 1 := by rw [h4]
          _ = 0 := by ring
      exfalso; exact hp3' hzero
    · have hx : (-(2 : ZMod p)) ^ 3 = 1 := by
        rw [← h1]; exact pow_orderOf_eq_one _
      have hzero : (3 : ZMod p) = 0 := by
        have h9 : (9 : ZMod p) = 0 := by
          have h8 : (-(8 : ZMod p)) = 1 := by
            calc (-(8 : ZMod p)) = (-(2 : ZMod p)) ^ 3 := by ring
              _ = 1 := hx
          have h8' : (8 : ZMod p) = -1 := by
            rw [← neg_neg (8 : ZMod p), h8]
          calc (9 : ZMod p) = 8 + 1 := by norm_num
            _ = -1 + 1 := by rw [h8']
            _ = 0 := by ring
        have h3sq : (3 : ZMod p) ^ 2 = 0 := by
          calc (3 : ZMod p) ^ 2 = 9 := by norm_num
            _ = 0 := h9
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3sq
      exfalso; exact hp3' hzero
  · exact h


theorem isQuasisimple_pointwiseStab_of_isCompl [Finite K] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hBsym : B.IsSymm) (hBn : B.SeparatingLeft) {U : Submodule K V}
    (hc : IsCompl U (Submodule.orthogonalBilin B U))
    (hdim : 2 ≤ Module.finrank K (Submodule.orthogonalBilin B U))
    (hq2 : Module.finrank K (Submodule.orthogonalBilin B U) = 2 → 4 ≤ 2 ^ n)
    (hq3 : Module.finrank K (Submodule.orthogonalBilin B U) = 3 → 3 ≤ 2 ^ n) :
    CFSG.IsQuasisimple ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) U) := by
  have hW : (B.domRestrict₁₂ (Submodule.orthogonalBilin B U)
      (Submodule.orthogonalBilin B U)).SeparatingLeft :=
    separatingLeft_domRestrict_orthogonalBilin hBsym.isRefl hBn hc
  have hSU : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂
      (Submodule.orthogonalBilin B U) (Submodule.orthogonalBilin B U))) := by
    rcases Nat.lt_or_ge (Module.finrank K (Submodule.orthogonalBilin B U)) 3 with h2 | h3
    · obtain ⟨e2⟩ := sesqSpecialUnitaryGroupLE_mulEquiv (B := B.domRestrict₁₂
        (Submodule.orthogonalBilin B U) (Submodule.orthogonalBilin B U))
      refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm ?_
      exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup h
        (hBsym.domRestrict _) hW (by omega) (hq2 (by omega))
    · obtain ⟨e2⟩ := sesqSpecialUnitaryGroupLE_mulEquiv (B := B.domRestrict₁₂
        (Submodule.orthogonalBilin B U) (Submodule.orthogonalBilin B U))
      refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm ?_
      refine CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_sesqSpecialUnitaryGroup_of_three_le
        h (hBsym.domRestrict _) hW h3 ?_
      intro hcon
      have h1 : Module.finrank K (Submodule.orthogonalBilin B U) = 3 := congrArg Prod.fst hcon
      have h2 : 2 ^ n = 2 := congrArg Prod.snd hcon
      rw [h1] at hq3
      have h3' := hq3 rfl
      omega
  obtain ⟨e⟩ := pointwiseStab_sesqSpecialUnitaryGroup_mulEquiv (B := B) hBsym.isRefl hc
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU


end General

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
