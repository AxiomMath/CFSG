module

public import CFSG.ClassicalInvolution.Asc77.AscR31Recog

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal (minusCoeffs_irr)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C23_chainMinus4 : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 6 (!piSign p f) →
          ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
            (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
            (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

variable {p f}

theorem c23_recogMinus4_of_chain (h : C23_chainMinus4 p f) : R31.C23_recogMinus4 p f := by
  intro hq G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  have hΩ := hs.stand.hyp.conjInvariant
  have hcls : ∀ (U : Fin 3 → Subgroup G), U 0 ∈ Ω → ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U 0) := by
    intro U hU0 J hJ
    obtain ⟨g, hg⟩ := (hs.stand.of_mem hU0).trans J hJ
    exact ⟨g, hg.symm⟩
  obtain ⟨U, hU0, hc02, ⟨_, hp01⟩, ⟨_, ht12⟩, hgen⟩ := h hq G Ω K K' W z u e g hs hd hα hE hY
  have hcomm : ∀ i j : Fin (4 - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j,
      a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exact hc02
  have hpair : ∀ i j : Fin (4 - 1), i.val + 1 = j.val → j.val + 2 < 4 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exact ⟨_, hp01⟩
  have htw : ∀ i j : Fin (4 - 1), i.val + 3 = 4 → j.val + 2 = 4 →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact ⟨_, ht12⟩
  obtain ⟨D, hc, i, ht, hr⟩ := exists_lieSystemData_of_chain_minus (n := 4) hs.stand.odd
    hs.stand.five (by norm_num) (CFSG.ClassicalInvolution.RouteD.spinMinus6Generated_galois
      hs.stand.odd) hΩ U hU0 (hcls U hU0) hcomm hpair htw hgen
  exact ⟨D, hc, i, ht, hr⟩

end CHN

end CFSG.ClassicalInvolution.Asc77
