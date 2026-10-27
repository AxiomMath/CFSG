module

public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer
public import CFSG.ClassicalInvolution.Asc77.AscT7BFinal23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_4X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      rLayer Ω e ≤ oddCoreOf (rLayer Ω e) ⊔ (rLayer Ω e ⊓ Subgroup.normalizer (W : Set G)) ∨
        LayerOrthType p f Ω e 6 (piSign p f)

@[expose] def C23_5X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      (Odd (Nat.card ↥(alphaOf (Subgroup.closure {u, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {u * e, u, z} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u, z})) ∧
      (∀ WY ∈ WSet (restrictFamily (exactFamily Ω u) (rLayer Ω u)),
        MuIsoE4 (restrictFamily (exactFamily Ω u) (rLayer Ω u)) WY) ∧
      (u * e ∈ zStarOf (rLayer Ω u) ∨ LayerOrthType p f Ω u 5 true ∨
        LayerOrthType p f Ω u 6 (!piSign p f))

@[expose] def C23_9X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) ∧
      LayerOrthType p f Ω e 6 (piSign p f) ∧
      (LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f))

@[expose] def C23_9_noZX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        LayerOrthType p f Ω e 6 (piSign p f) → u * e ∉ zStarOf (rLayer Ω u)

@[expose] def C23_9_genX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g → LayerOrthType p f Ω e 6 (piSign p f) →
        (LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f)) →
          rLayer Ω e ⊔ rLayer Ω u = ⊤

@[expose] def C23_chainX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) →
        (LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f)) →
          (∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
              (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
              (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤) ∨
          (∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
              (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
              (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤)

variable {p f}

theorem c23_9_ofX (h2 : C23_2 p f) (h4 : C23_4X p f) (h5 : C23_5X p f) (h7 : C23_7 p f)
    (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) : C23_9X p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hE : LayerOrthType p f Ω e 6 (piSign p f) :=
    (h4 G Ω K K' W z u e g h).resolve_left (h7 G Ω K K' W z u e g h)
  obtain ⟨⟨hodd, halpha⟩, -, hY⟩ := h5 G Ω K K' W z u e g h
  have hset : Hyp23Setting p f Ω K K' z := h.std.setting
  have hY' : LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f) :=
    hY.resolve_left (hnoZ G Ω K K' W z u e g hset h.data hE)
  obtain ⟨hΓz, hΓu⟩ := hΓ G Ω K K' W z u e g hset h.data
  have hG := h2 G Ω K K' z h.std W h.hW h.hzW u h.hu h.huW h.hu1 h.huz h.hu2
  have hN : Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (hΓu.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  have hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard h.std.1.hz)
  exact ⟨⟨hα, hgen G Ω K K' W z u e g hset h.data hE hY'⟩, hE, hY'⟩

theorem c23_10_ofX (h9 : C23_9X p f) (hchain : C23_chainX p f)
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

theorem c23_3_of_inputsX (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hsetup : C23_setupSetting p f) (h4 : C23_4X p f) (h5 : C23_5X p f) (h7 : C23_7 p f)
    (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f)
    (hchain : C23_chainX p f) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_steps (c23_setup_of hsetup)
    (c23_10_ofX (c23_9_ofX (c23_2_of_trans hE htr) h4 h5 h7 hΓ hnoZ hgen) hchain hg6)

end CFSG.ClassicalInvolution.Asc77
