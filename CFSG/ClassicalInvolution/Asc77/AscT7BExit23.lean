module

public import CFSG.ClassicalInvolution.Asc77.AscT7BLocal23
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup23
public import CFSG.ClassicalInvolution.Asc77.AscT7BChain23
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_chain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) →
        (SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
          SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f)) →
          (∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
              (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
              (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤) ∨
          (∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
              (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
              (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤)

variable {p f}

theorem c23_10_of (h9 : C23_9 p f) (hchain : C23_chain p f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_10 p f := by
  intro G _ _ _ Ω K K' W z u e g h
  obtain ⟨⟨hα, hgen⟩, hE, hY⟩ := h9 G Ω K K' W z u e g h
  have hst : AscStand p f Ω K := h.std.1.stand
  have hΩ : ConjInvariant Ω := hst.hyp.conjInvariant
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    obtain ⟨x, -, y, -, hxy⟩ :=
      (hst.hyp.isQuatSub_of_mem_RSet hst.odd (mem_RSet_of_isSylow2In hst.mem hV)).exists_not_commute
    exact ⟨x, y, hxy⟩
  have hcls : ∀ (U : Fin 3 → Subgroup G), U 0 ∈ Ω → ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U 0) := by
    intro U hU0 J hJ
    obtain ⟨g, hg⟩ := (hst.of_mem hU0).trans J hJ
    exact ⟨g, hg.symm⟩
  rcases hchain G Ω K K' W z u e g h.std.setting h.data ⟨hα, hgen⟩ hE hY with
    ⟨U, hU0, hc02, hp01, hs12, hgenU⟩ | ⟨U, hU0, hc02, hp01, ht12, hgenU⟩
  · refine Or.inl (Or.inl (oddLieType_of_chain_odd hst.odd hst.five (n := 3) (by norm_num) hΩ U
      hU0 (hcls U hU0) ?_ ?_ ?_ hgenU hnab))
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      exact hc02
    · intro i j hij hj
      fin_cases i <;> fin_cases j <;> simp at hij hj
      exact hp01
    · intro i j hi hj
      fin_cases i <;> fin_cases j <;> simp at hi hj
      exact hs12
  · refine Or.inl (Or.inl (oddLieType_of_chain_minus hst.odd hst.five (n := 4) (by norm_num) hg6 hΩ
      U hU0 (hcls U hU0) ?_ ?_ ?_ hgenU hnab))
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      exact hc02
    · intro i j hij hj
      fin_cases i <;> fin_cases j <;> simp at hij hj
      exact hp01
    · intro i j hi hj
      fin_cases i <;> fin_cases j <;> simp at hi hj
      exact ht12

theorem c23_3_of_inputs (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hfuse : C23_2_fuse p f) (hsetup : C23_setupSetting p f) (h4 : C23_4 p f)
    (h5 : C23_5 p f) (h7 : C23_7 p f) (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZ p f)
    (hgen : C23_9_gen p f) (hchain : C23_chain p f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_steps (c23_setup_of hsetup)
    (c23_10_of (c23_9_of (c23_2_of hE htr hfuse) h4 h5 h7 hΓ hnoZ hgen) hchain hg6)

end CFSG.ClassicalInvolution.Asc77
