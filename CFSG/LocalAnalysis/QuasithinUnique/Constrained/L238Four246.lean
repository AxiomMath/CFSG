module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourRank1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourBlocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank

namespace L238

variable {G : Type} [Group G] [Finite G]

theorem mem_uFamHat_of_isMinimalParabolic {X S H : Subgroup G} (hHX : H ≤ X)
    (h : IsMinimalParabolic S H) : H ∈ uFamHat X S := by
  obtain ⟨M₀, hM₀⟩ := minParabolic_exists_iff.2 h
  refine ⟨⟨hHX, hM₀.lt, ?_⟩, hM₀.not_normal⟩
  have hmax : maxOver H S = {M₀} := hM₀.uniqueMax
  rw [hmax]
  exact Set.ncard_singleton M₀

theorem lemma246_single (hin : Lemma246Inputs)
    {T M H S L : Subgroup G} (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  classical
  obtain ⟨hQne, hXΓ, -, hSX, hSXM, -, -⟩ := hcs.gamma0.core_normalizer hcs.setting hcs.sylow_inf
  obtain ⟨hXc, hQeq⟩ := hcs.gamma0.charTwo_core_normalizer hcs.setting hcs.sylow_inf hcs.charTwo
  set X : Subgroup G := Subgroup.normalizer (pCoreOf 2 H : Set G) with hXdef
  have hSXM' : IsSylowTwoOf S (X ⊓ M) := by rwa [inf_comm]
  have hHX : H ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hcgs : cgsIn X S ≤ X ⊓ M := cgsIn_le_inf hcs.setting hXΓ hXc hSXM'
  have hSQ : IsSQTKCat X :=
    positiveTwoCoreSQTK G T M hcs.setting X (by rw [hQeq]; exact hQne)
  have h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
    hin.a38 _ (Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQ)
  have hHU : H ∈ uFamHat X S := mem_uFamHat_of_isMinimalParabolic hHX hcs.minParabolic
  have hUK : H = S ⊔ conjClosure L S := by
    rw [hcs.eq_join, sup_comm, conjJoin_eq_conjClosure]
  have hKM : ¬ L ≤ X ⊓ M := fun h => hcs.not_le (h.trans inf_le_right)
  obtain ⟨Lh, hLhchi, hLhJ, hLLh, hLhM⟩ := exists_chiBlock_of_chi0Block_catJ (hin.c127 G)
    (hin.c123 G) (hin.b42 G) hXc hSQ h38 hSX hcgs hHU hcs.block hcs.thompson hUK hKM
  have hLhchi0 : IsChi0Block X Lh :=
    isChi0Block_of_isChiBlock_cat (hin.a7 G) hXc hSQ hSX hcgs inf_le_left hLhchi hLhJ hLhM
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := C56.S_le_normalizer hj
  have hLeq : L = Lh := eq_of_le_isChi0Block hSX hLhchi0 hL hLLh (inf_le_left.trans hSN)
  have hLblock : IsBlock2 X L := hLeq ▸ hLhchi.1
  exact le_normalizer_of_sylow_le_normalizer h38 hSX
    (mem_cComp_of_isChi0Block_nonsolvable hLblock hL) hSN

theorem lemma246Chi_of_inputs
    (hin : Lemma246Inputs) : Lemma246Chi := by
  intro G _ _ T M H S L hcs hj hL
  exact lemma246_single hin hcs hj hL

end L238

end CFSG.QuasithinUnique
