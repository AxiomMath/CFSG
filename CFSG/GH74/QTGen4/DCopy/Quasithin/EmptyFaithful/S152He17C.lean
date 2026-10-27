module

public import CFSG.Quasithin.EmptyFaithful.S152He17C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He16D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He17A

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15204QuasiRest2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) →
    C27Rest2 (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) Lc
      (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) → False

theorem input15204BranchBQuasi_of_rest2_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (h : Input15204QuasiRest2_F4) :
    Input15204BranchBQuasi_F4 := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  obtain ⟨y, hyY, hyN, hy5⟩ := exists_five_element_F4 (hC27 G) c tail hYL hq
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRN : rOf T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) := tail.hyp.radical.1.trans hNG
  obtain ⟨-, -, h3⟩ := hC27 G (g0Of T Mc M K₁) (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) Lc _
    tail.hyp tail.comp (isQuasisimple_quot tail.comp hq)
    (CFSG.Quasithin.CT.CharTwo.of_normal tail.charTwo hLG tail.normal) tail.not_le hRN rfl
  have hrest := h G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  rcases h3 with ⟨hblk, ha⟩ | hb | hc3 | hd | he | hf | hg | hh
  · rcases ha with ⟨hlin, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -, e, P, hP, hmap⟩ | ⟨hA7, -, e, P, hP, hmap⟩
    · exact false_of_chi0 c tail hYL ⟨hblk.1, Or.inl hlin⟩
    · exact false_of_chi0 c tail hYL ⟨hblk.1, Or.inr (Or.inr hA5)⟩
    · exact false_of_partition c hYL hyY hyN hy5 e (sizes := {4, 3}) (by decide) (by decide) hP hmap
    · exact false_of_partition c hYL hyY hyN hy5 e (sizes := {2, 2, 2, 1}) (by decide) (by decide)
        hP hmap
  · exact hrest (Or.inl hb)
  · exact false_of_hatA6 c hYL hc3.1 hc3.2.1
  · exact false_of_excA7 c hYL hd.1 hd.2
  · exact hrest (Or.inr (Or.inl he))
  · exact hrest (Or.inr (Or.inr (Or.inl hf)))
  · exact hrest (Or.inr (Or.inr (Or.inr (Or.inl hg))))
  · exact hrest (Or.inr (Or.inr (Or.inr (Or.inr hh))))

end CFSG.Quasithin.He17
