module

public import CFSG.Quasithin.EmptyFaithful.S152He17D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He17C

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15204QuasiRest3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) →
    C27Rest3 (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) Lc
      (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) → False

theorem input15204QuasiRest2_of_rest3_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (h : Input15204QuasiRest3_F4) :
    Input15204QuasiRest2_F4 := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot hq hrest
  obtain ⟨y, hyY, hyN, hy5⟩ := exists_five_element_F4 (hC27 G) c tail hYL hq
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨⟨h11, h12, -⟩, -, -⟩ := hC27 G (g0Of T Mc M K₁) R (M ⊓ g0Of T Mc M K₁) Lc V tail.hyp
    tail.comp (isQuasisimple_quot tail.comp hq)
    (CFSG.Quasithin.CT.CharTwo.of_normal tail.charTwo hLG tail.normal) tail.not_le hRN rfl
  have hVN : Lc ⊔ R ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R))
      (le_normalizer_pCoreOf 2 (Lc ⊔ R) hg)
  have hYM : ∀ m ∈ M ⊓ g0Of T Mc M K₁, ∀ z ∈ yOf152 T Mc M, m * z * m⁻¹ ∈ yOf152 T Mc M :=
    fun m hm z hz => (Subgroup.mem_normalizer_iff.mp (c.y.normal hm.1) z).mp hz
  have hrest' := h G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  rcases hrest with ⟨⟨n, α, hn5, -, -, hα, t, htR, htV, hRt, -, σ, hσ, hconj⟩, hMK⟩ | he | hf | hg | hh
  · exact false_of_altBlock hLG (subnormal_of_mem_cComp tail.comp) hRG hRN hVN h11 h12
      (Y_le_inf c hYL) hYM (card_Y c) hyY hyN hy5 hn5 hα htR htV hRt hσ hconj hMK
  · rcases he with ⟨⟨-, α, hα⟩ | hsp, hmax⟩
    · exact false_of_a6Block hLG (subnormal_of_mem_cComp tail.comp) hRG hRN hVN h11 h12
        (Y_le_inf c hYL) hYM (card_Y c) hyY hyN hy5 hα hmax.1
    · exact hrest' (Or.inl ⟨hsp, hmax⟩)
  · exact false_of_g2 (hYL hyY) hyN hy5 hf.2.1
  · exact hrest' (Or.inr (Or.inl hg))
  · exact hrest' (Or.inr (Or.inr hh))

theorem input15204BranchBQuasi_of_rest3_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (h : Input15204QuasiRest3_F4) :
    Input15204BranchBQuasi_F4 :=
  input15204BranchBQuasi_of_rest2_F4 hC27 (input15204QuasiRest2_of_rest3_F4 hC27 h)

end CFSG.Quasithin.He17
