module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246DoubleBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238Four246

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank

namespace L246Double

variable {G : Type} [Group G] [Finite G]

theorem lemma246_blocks
    (hin : Lemma246Inputs) (h37 : Vol2Native.A37ForSQTKCat)
    {T M H S L : Subgroup G} (hcs : ConstrainedSetting G T M H S L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (conjJoin S L : Set G) := by
  classical
  obtain ⟨hQne, hXΓ, -, hSX, hSXM, -, -⟩ := hcs.gamma0.core_normalizer hcs.setting hcs.sylow_inf
  obtain ⟨hXc, hQeq⟩ := hcs.gamma0.charTwo_core_normalizer hcs.setting hcs.sylow_inf hcs.charTwo
  set X : Subgroup G := Subgroup.normalizer (pCoreOf 2 H : Set G) with hXdef
  have hSXM' : IsSylowTwoOf S (X ⊓ M) := by rwa [inf_comm]
  have hHX : H ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hcgs : cgsIn X S ≤ X ⊓ M := L238.cgsIn_le_inf hcs.setting hXΓ hXc hSXM'
  have hX2 : pCoreOf 2 X ≠ ⊥ := by rw [hQeq]; exact hQne
  have hSQ : IsSQTKCat X := positiveTwoCoreSQTK G T M hcs.setting X hX2
  have h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
    hin.a38 _ (Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQ)
  have hHU : H ∈ uFamHat X S := L238.mem_uFamHat_of_isMinimalParabolic hHX hcs.minParabolic
  have hUK : H = S ⊔ conjClosure L S := by
    rw [hcs.eq_join, sup_comm, L238.conjJoin_eq_conjClosure]
  have hKM : ¬ L ≤ X ⊓ M := fun h => hcs.not_le (h.trans inf_le_right)
  obtain ⟨Lh, hLhchi, hLhJ, hLLh, hLhM⟩ := L238.exists_chiBlock_of_chi0Block_catJ (hin.c127 G)
    (hin.c123 G) (hin.b42 G) hXc hSQ h38 hSX hcgs hHU hcs.block hcs.thompson hUK hKM
  have hLhchi0 : IsChi0Block X Lh :=
    L238.isChi0Block_of_isChiBlock_cat (hin.a7 G) hXc hSQ hSX hcgs inf_le_left hLhchi hLhJ hLhM
  have hLcH : L ∈ cComp H := L238.mem_cComp_of_isChi0Block_nonsolvable hcs.block.1 hL
  have hnorm : conjJoin S L ≤ Subgroup.normalizer (L : Set G) := by
    rcases hcs.blocks with hj | ⟨t, -, -, hjoin, hcomm⟩
    · rw [hj]
      exact Subgroup.le_normalizer
    · rw [hjoin]
      refine sup_le Subgroup.le_normalizer ?_
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer.1 ?_).trans
        (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.commutator_comm]
      exact hcomm
  have hLeq : L = Lh := eq_of_le_isChi0Block_conj hSX hLhchi0 hL hLLh (ne_bot_of_mem_cComp hLcH)
    (perfect_of_mem_cComp hLcH) hnorm
  have hLX : L ∈ cComp X := by
    have h1 := L238.mem_cComp_of_isChi0Block_nonsolvable hLhchi0.1 (hLeq ▸ hL)
    rwa [← hLeq] at h1
  have h2 := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hcs.setting.qtke.1 h37 hin.a38 hX2 hSX
    hLX
  rwa [← L238.conjJoin_eq_conjClosure] at h2

end L246Double

@[expose] def L246Double.Lemma246DoubleLin2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L ≠ L → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (conjJoin S L : Set G)

theorem L246Double.lemma246DoubleLin2_of_inputs (hin : Lemma246Inputs)
    (h37 : Vol2Native.A37ForSQTKCat) : L246Double.Lemma246DoubleLin2 := by
  intro G _ _ T M H S L hcs _ hL
  exact L246Double.lemma246_blocks hin h37 hcs (Or.inl hL)

theorem L246Double.lemma246DoubleLin2_proved
    (hin : Lemma246Inputs) :
    L246Double.Lemma246DoubleLin2 :=
  L246Double.lemma246DoubleLin2_of_inputs hin Vol2Native.a37ForSQTKCat_proved

end CFSG.QuasithinUnique
