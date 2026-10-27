module

public import CFSG.Quasithin.EmptyFaithful.T1515dF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem lemma15121InputU_of_F4 (hSt : Struct15121) (hI20 : Lemma15120InputU_F4)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) : Lemma15121InputU_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hx18 hLc hant
  by_contra hnot
  have hq := hC.qtfe
  have hM := hC.mf
  have hS := hC.setting
  have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hant with ⟨-, hbl, hty⟩ | ⟨hco, -⟩
    · exact isQuasisimple_pCoreQuot_of_block1521d hbl.1 hty
    · exact isQuasisimple_pCoreQuot_of_component1521d hco h19.one
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hqs, hnot⟩
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18.four hpc
  have h15' := h15 G T Mc M hq hM hC.ce
  have h20 : Lemma15120Concl T Mc M Z₁ L := by
    obtain ⟨h2, h3⟩ := hI20 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL hx18
    exact ⟨lemma_15_1_20_sylow h18.four hL20,
      lemma_15_1_20_one (h1416 G T Mc hq).1 hM h15' hL20, h2,
      fun hc => ⟨isPGroup_two_center_of_isComponentOf1515c hc h19.one, h3 hc⟩⟩
  have hS1 : s1516 T Z₁ ≠ ⊥ := fun h =>
    hpc (le_bot_iff.1 (h ▸ pCoreOf_le_of_isSylowTwoOf h18.four))
  have hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS h18.four.2.1 hS1).trans h17.cgs
  have h197 := h19.seven L hLc hqs hnot
  have hV2V : V₂ ≤ V154 T Mc M := hS.v2_le
  rcases hSt G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 hant with
    ⟨B₀, hBZ, hBN, hB2, hBS⟩ | hb
  ·
    have hBM : B₀ ≤ M := hBN.trans hNJ
    have hB1 : B₀ ≤ M ⊓ Mc ⊓ g1_1516 Z₁ := fun b hb => ⟨⟨hBM hb, (hBZ hb).2⟩, (hBZ hb).1⟩
    have hBC : B₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
      have h1 : oTwoUpper B₀ ≤ oTwoUpper (M ⊓ Mc ⊓ g1_1516 Z₁) := oTwoUpper_mono hB1
      rw [hB2, hx18.two_eq] at h1
      exact h1.trans (oTwoUpper_le _)
    apply h197.2
    have hc : L ≤ Subgroup.centralizer (V₂ : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hBS v hv (fun b hb => Subgroup.mem_centralizer_iff.mp (hBC hb).2 v (hV2V hv)) l hl
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hc
  ·
    obtain ⟨p, hp, Y, hYMG, hYJ, hYp, hSY, hVY⟩ := hS.p_sub
    have hYJ' : Y ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) := by
      rw [h17.jS]
      exact hYJ
    have hLY : ⁅L, Y⁆ = ⊥ := hb p Y hp hYMG hYJ' hYp hSY hVY
    have hV2N : V₂ ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans h197.1
    have h1 : ⁅⁅Y, L⁆, V₂⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Y L, hLY, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅L, V₂⁆, Y⁆ = ⊥ := by
      have hle : ⁅L, V₂⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hV2N
      exact le_bot_iff.1 ((Subgroup.commutator_mono hle le_rfl).trans hLY.le)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hVY] at h3
    exact h197.2 (by rw [Subgroup.commutator_comm]; exact h3)

end CFSG.Quasithin
