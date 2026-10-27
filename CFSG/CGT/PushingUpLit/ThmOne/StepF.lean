module

public import CFSG.CGT.PushingUpLit.CGT6.EightOneCore
public import CFSG.CGT.PushingUpLit.CGT6.SixFiveArrow
public import CFSG.CGT.PushingUpLit.CGT6.EmbK

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_top_of_isMaximalTwoLocal (htop : CFSG.IsPLocal 2 (⊤ : Subgroup G))
    {N : Subgroup G} (hN : CFSG.IsMaximalTwoLocal N) : N = ⊤ := by
  by_contra hne
  exact hN.2 ⊤ (lt_top_iff_ne_top.mpr hne) htop

omit [Finite G] in
theorem maximalTwoLocalsContaining_eq_top (htop : CFSG.IsPLocal 2 (⊤ : Subgroup G))
    (X : Set G) : CFSG.maximalTwoLocalsContaining X = {⊤} := by
  ext N
  simp only [CFSG.maximalTwoLocalsContaining, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, -⟩
    exact eq_top_of_isMaximalTwoLocal htop hN
  · rintro rfl
    exact ⟨⟨htop, fun H hH => (not_top_lt hH).elim⟩, fun x _ => Subgroup.mem_top x⟩

@[expose] def ArrowTransHyp (G : Type) [Group G] [Finite G] : Prop :=
  ∀ X Y Z : Subgroup G, InClassX ↥X → InClassX ↥Y → Arrow X Y → Arrow Y Z → Arrow X Z

@[expose] def ThreeKHyp (G : Type) [Group G] [Finite G] : Prop :=
  (∀ N : Subgroup G, CFSG.IsMaximalTwoLocal N → CFSG.IsKGroup ↥N) →
    ∀ X : Subgroup G, IsMaximalInClassXG X →
      ∃ M : Subgroup G, CFSG.maximalTwoLocalsContaining (X : Set G) = {M} ∧
        (X.subgroupOf M).IsSubnormal

theorem arrowTransHyp_holds (G : Type) [Group G] [Finite G] : ArrowTransHyp G :=
  fun _ _ _ hX hY h1 h2 => CGT6.arrow_trans_of_inClassX hX hY h1 h2

theorem threeKHyp_of_eightOneK (h81 : CGT6.AschbacherEightOneK) (hK : KProper InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) : ThreeKHyp G :=
  fun hKG _ hX => CGT6.factorizationThree_of_eightOneK h81 hK hchar hKG hX

theorem exists_maximalInClassXG_above (htrans : ArrowTransHyp G) {X : Subgroup G}
    (hX : InClassXG X) : ∃ Y : Subgroup G, IsMaximalInClassXG Y ∧ Arrow X Y := by
  obtain ⟨Y, ⟨hY, hXY⟩, hmax⟩ := Set.exists_max_image
    {Y : Subgroup G | InClassXG Y ∧ Arrow X Y} (fun Y => Nat.card Y) (Set.toFinite _)
    ⟨X, hX, arrow_refl X⟩
  refine ⟨Y, ⟨hY, fun Z hZ hYZ => ?_⟩, hXY⟩
  have hXZ : Arrow X Z := htrans X Y Z hX.1 hY.1 hXY hYZ
  exact (Subgroup.eq_of_le_of_card_ge (arrow_le hYZ) (hmax Z ⟨hZ, hXZ⟩)).symm

theorem theoremOne_of_inClassXG (hK : KProper InCatalog G) (htrans : ArrowTransHyp G)
    (h3 : ThreeKHyp G) {X : Subgroup G} (hX : InOmega X)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X)
    (hXG : ¬ CFSG.IsPLocal 2 (⊤ : Subgroup G) → InClassXG X) :
    ∃ M : Subgroup G, CFSG.maximalTwoLocalsContaining (X : Set G) = {M} := by
  by_cases htop : CFSG.IsPLocal 2 (⊤ : Subgroup G)
  · exact ⟨⊤, maximalTwoLocalsContaining_eq_top htop _⟩
  · have hKG : ∀ N : Subgroup G, CFSG.IsMaximalTwoLocal N → CFSG.IsKGroup ↥N := fun N hN =>
      CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup hK N
        (fun h => htop (h ▸ hN.1))
    obtain ⟨Y, hY, hXY⟩ := exists_maximalInClassXG_above htrans (hXG htop)
    obtain ⟨N, hN, hYN⟩ := h3 hKG Y hY
    have hNmem : N ∈ CFSG.maximalTwoLocalsContaining (Y : Set G) := by
      rw [hN]
      exact Set.mem_singleton N
    have hYX : Y = X := hmax Y ⟨hY.1.1, N, hNmem.1, hNmem.2, hYN⟩ hXY
    subst hYX
    exact ⟨N, hN⟩

@[expose] def SectionThreeContent : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ¬ CFSG.IsPLocal 2 (⊤ : Subgroup G) →
    ∀ X : Subgroup G, InOmega X → (∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) →
      InClassXG X

theorem aschbacherTheoremOneK_of_sectionThree
    (htrans : ∀ (G : Type) [Group G] [Finite G], ArrowTransHyp G)
    (h3 : ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G →
      CFSG.Assembly.IsCharTwoType G → ThreeKHyp G)
    (hS3 : SectionThreeContent) : AschbacherTheoremOneK := by
  intro G _ _ hK hchar X hX hmax
  exact theoremOne_of_inClassXG hK (htrans G) (h3 G hK hchar) hX hmax
    (fun htop => hS3 G hK hchar htop X hX hmax)

theorem aschbacherTheoremOneK_of_eightOneK (h81 : CGT6.AschbacherEightOneK)
    (hS3 : SectionThreeContent) : AschbacherTheoremOneK :=
  aschbacherTheoremOneK_of_sectionThree (fun G _ _ => arrowTransHyp_holds G)
    (fun _ _ _ hK hchar => threeKHyp_of_eightOneK h81 hK hchar) hS3

theorem aschbacherTheoremOneK_of_embeddingK (hE : CGT6.AschbacherEmbeddingK)
    (hS3 : SectionThreeContent) : AschbacherTheoremOneK :=
  aschbacherTheoremOneK_of_eightOneK
    (CGT6.eightOneK_of_core (CGT6.aschbacherSixThreeCore_of_embeddingK hE)) hS3

end CFSG.CGT.PushingUpLit.ThmOne
