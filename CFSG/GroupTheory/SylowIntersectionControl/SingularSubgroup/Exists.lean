module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Baumann
import CFSG.GroupTheory.SylowIntersectionControl.Regular

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

structure GomiThm45Inputs : Prop where
  fact22 : GomiFact22
  fact23 : GomiFact23
  fact31 : GomiFact31
  fact32 : GomiFact32
  fact33 : GomiFact33
  fact35 : GomiFact35
  fact36 : GomiFact36
  fact37CSP : GomiFact37OneCSP
  fact37Two : GomiFact37Two
  fact37Three : GomiFact37Three
  fact37Four : GomiFact37Four
  lemma44 : GomiLemma44
  bender : GomiBender
  benderSL2 : GomiBenderSL2

variable {Ω : Type} [Group Ω] [Finite Ω]

namespace GomiThm45Counterexample

variable {c : GNPairChoice Ω} {G S : Subgroup Ω}

theorem isGomiQ (h : GomiThm45Counterexample c G S)
    (hin : GomiThm45Inputs) : IsGomiQ S G := by
  obtain ⟨Lb, hL⟩ := h.exists_isGomiStepE hin.fact31 hin.fact33 hin.lemma44
  have hg := h.isGomiStepG hin.fact31 hin.fact36 hin.fact37Two hL
    (h.isGomiStepF hin.bender hin.benderSL2 hin.fact22 hin.fact23 hL)
  have hi := h.le_conjClosure_baum hin.fact31 hin.fact33 hL hg
  exact
    { sylow := h.isSylowTwoOf
      charTwo := h.hyp43.charTwo
      natural := h.natural hin.fact31 hin.fact32 hin.fact37CSP hin.fact37Three
        hin.fact37Four hL hg hi
      sylowCent := h.isSylowTwoOf_pCoreOf_centralizer
      not_commutator_le :=
        h.not_commutator_le_gomiV hin.fact31 hin.fact32 hin.fact37CSP
          hin.fact37Three hin.fact37Four hL hg hi
      uniqueMax := h.exists_isUniqueMaxOver hL hg
      le_conjClosure_baum := hi }

theorem false (h : GomiThm45Counterexample c G S)
    (hc : ∀ T : Subgroup Ω, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      IsGomiCharPairGN T (c.fst T) (c.snd T)) (hin : GomiThm45Inputs) : False := by
  obtain ⟨Lb, hL⟩ := h.exists_isGomiStepE hin.fact31 hin.fact33 hin.lemma44
  have hg := h.isGomiStepG hin.fact31 hin.fact36 hin.fact37Two hL
    (h.isGomiStepF hin.bender hin.benderSL2 hin.fact22 hin.fact23 hL)
  have hi := h.le_conjClosure_baum hin.fact31 hin.fact33 hL hg
  have hK : baum S = S :=
    h.baum_eq hin.fact31 hin.fact32 hin.fact35 hin.fact37CSP hin.fact37Three
      hin.fact37Four hL hg hi
  have hSne : S ≠ ⊥ := by
    rintro rfl
    apply h.isSylowTwoOf.2.2
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact even_iff_two_dvd.mp h.hyp43.even
  obtain ⟨⟨hle₁, -, hle₂, -, hall⟩, -⟩ := hc S h.isSylowTwoOf.2.1 hK hSne
  have hQ : IsGomiQ S.subtype.range G := by
    rw [S.range_subtype]
    exact h.isGomiQ hin
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S G :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr h.isSylowTwoOf
  rcases hall Ω G S.subtype S.subtype_injective hQ with hN | hN
  · rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle₁] at hN
    refine h.not_isRegular (PSubgroupSelection.isRegular_of_le_normalizer hSyl
      (F := c.C₁ S) (by simp [GNPairChoice.selection]) ?_)
    rwa [GNPairChoice.C₁, hK]
  · rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle₂] at hN
    refine h.not_isRegular (PSubgroupSelection.isRegular_of_le_normalizer hSyl
      (F := c.C₂ S) (by simp [GNPairChoice.selection]) ?_)
    rwa [GNPairChoice.C₂, hK]

end GomiThm45Counterexample

theorem GNPairChoice.gomiThm45At (c : GNPairChoice Ω)
    (hc : ∀ T : Subgroup Ω, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      IsGomiCharPairGN T (c.fst T) (c.snd T)) (hin : GomiThm45Inputs) (G : Subgroup Ω) :
    GomiThm45At c G := by
  by_contra hG
  obtain ⟨G', S, h⟩ := exists_gomiThm45Counterexample c hG
  exact h.false hc hin

end CFSG.GroupTheory
