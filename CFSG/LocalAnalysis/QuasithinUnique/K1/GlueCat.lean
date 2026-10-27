module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase

public section

namespace CFSG.QuasithinUnique.K1

section Main

theorem sqtkSimpleListCat_iff (X : Type) [Group X] :
    CFSG.Milestones.SQTKSimpleList X ↔
      AltFamily X ∨ OddClassicalFamily X ∨ EvenClassicalFamily X ∨ ExceptionalFamilyCat X ∨
        SmallLinearFamily X ∨ SporadicFamilyCat X := by
  unfold CFSG.Milestones.SQTKSimpleList EvenClassicalFamily ExceptionalFamilyCat
  constructor
  · rintro (h | h | (⟨f, h | h | h | h | h | h | h | h⟩ | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inl h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inr (Or.inl h)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inr (Or.inr (Or.inl h))⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inr (Or.inr (Or.inr h))⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inl h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inl h)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl h))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr h))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rintro (h | h | ⟨f, h | h | h | h⟩ | (⟨f, h | h | h | h⟩ | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inl h⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inl h)⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl h))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem centralQuotientRankOneRecognition_of_families
    (h1 : K1FamilyRecognition AltFamily) (h2 : K1FamilyRecognition OddClassicalFamily)
    (h3 : K1FamilyRecognition EvenClassicalFamily)
    (h4 : K1FamilyRecognition ExceptionalFamilyCat)
    (h5 : K1FamilyRecognition SmallLinearFamily) (h6 : K1FamilyRecognition SporadicFamilyCat) :
    CFSG.QuasithinUnique.CentralQuotientRankOneRecognition := by
  intro G _ _ T M U z hd u hu hu1 hH S hS hUS L hL hUL
  obtain ⟨-, -, -, hloc⟩ := hd.escaping_centralizer_local_structure hu hu1 hH
  obtain ⟨-, hcl, w, -, hwU, hwS, -, hwC, -⟩ := hloc S hS hUS
  obtain ⟨-, -, hnocomp⟩ := hd.escaping_centralizer_odd_core_components hu hu1 hH
  obtain ⟨-, -, hLodd, hwchar⟩ :=
    hd.escaping_component_central_involution hu hu1 hH hS hUS hwU hwS hwC hL
  have hLM : ¬ L ≤ M := by
    intro hle
    apply hnocomp _ hL.2
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL.1]
    exact hle
  have hwnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G) := fun hle => hLM (hle.trans hwC)
  have hQ : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hSC : StrongClosureComponent (Subgroup.centralizer ({u} : Set G)) S U L :=
    ⟨hS, hUS, hd.elem, hcl, hL.1, Subgroup.isPerfect_iff.mp hQ.1, hL.2.2, hUL⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hQ.2.1
  have hLX : L ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    hL.1.trans (centralizer_singleton_le_normalizer_zpowers u)
  have hX : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (Subgroup.normalizer (Subgroup.zpowers u : Set G)) ≤ 2 := fun p hp hp2 =>
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _
      (isTwoLocal_normalizer_zpowers hd.elem hu hu1)).trans hd.setting.qtke.2.2
  have hSQT : CFSG.IsStronglyQuasithin (L ⧸ Subgroup.center L) :=
    CFSG.SectionRank.isStronglyQuasithin_iff.mpr fun p hp hp2 =>
      stronglyQuasithin_quotient hLX hX (Subgroup.center L)
        (isPGroup_two_center_of_oddCore_eq_bot hLodd) p hp hp2
  have hcore : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
    intro hbot
    have hle : Subgroup.zpowers u ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
      CFSG.QuasithinUnique.le_pCoreOf_of_normalizes
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
        (centralizer_singleton_le_normalizer_zpowers u)
        (isPGroup_zpowers_of_mem_elem hd.elem hu)
    rw [hbot] at hle
    exact hu1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers u)))
  have hCK : CFSG.SectionRank.IsKGroupCat (Subgroup.centralizer ({u} : Set G)) :=
    (hd.setting.qtke.1 _ hcore).2
  have hLK : CFSG.SectionRank.IsKGroupCat L :=
    (hCK.subgroup (L.subgroupOf (Subgroup.centralizer ({u} : Set G)))).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hL.1).symm
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list_simple (L ⧸ Subgroup.center L) hQ.2.2
    ⟨hSQT, hLK.quotient (Subgroup.center L)⟩
  have key : ∀ P : (∀ (X : Type) [Group X], Prop), K1FamilyRecognition P →
      P (L ⧸ Subgroup.center L) → CFSG.Open.fusionIsBenderGroup (L ⧸ Subgroup.center L) :=
    fun P hP hPL => hP G _ S U L hSC hPL w hwU hwS hwnc hwchar
  rcases (sqtkSimpleListCat_iff _).1 hlist with h | h | h | h | h | h
  · exact key _ h1 h
  · exact key _ h2 h
  · exact key _ h3 h
  · exact key _ h4 h
  · exact key _ h5 h
  · exact key _ h6 h

theorem localComponentRecognition_of_families
    (h1 : K1FamilyRecognition AltFamily) (h2 : K1FamilyRecognition OddClassicalFamily)
    (h3 : K1FamilyRecognition EvenClassicalFamily)
    (h4 : K1FamilyRecognition ExceptionalFamilyCat)
    (h5 : K1FamilyRecognition SmallLinearFamily) (h6 : K1FamilyRecognition SporadicFamilyCat) :
    CFSG.QuasithinUnique.LocalComponentRecognition :=
  localComponentRecognition_of_centralQuotient
    (centralQuotientRankOneRecognition_of_families h1 h2 h3 h4 h5 h6)

end Main

end CFSG.QuasithinUnique.K1
