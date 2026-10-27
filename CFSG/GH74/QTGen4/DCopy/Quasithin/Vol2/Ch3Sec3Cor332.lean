module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch3Sec3Cor332

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique.Vol2Native

@[expose] def Stmt3_3_1A_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T →
      ∀ M L : Subgroup G, quasithinIsMaxTwoLocal M → T ≤ M → quasithinIsMaximalLocal T L →
        L ≤ M → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
          Subgroup.normalizer (T : Set G) ≤ M

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem corollary_3_3_2_of_F4 (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h331 : Stmt3_3_1A_F4) {T L : Subgroup G} (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : QuasithinUnique.quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (quasithinIsMaxTwoLocal (Subgroup.normalizer (conjClosure L T : Set G)) ∧
        L ⊔ T ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
          M' = Subgroup.normalizer (conjClosure L T : Set G)) ∧
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
      ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H →
        IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (conjClosure L T : Set G)) ∧
          ¬ H ≤ Subgroup.normalizer (T : Set G) := by
  have hU := lemma_1_2_7_three hK hs hnab (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
    (a39ForSQTK_of_cat h39) hT hL
  have hTM : T ≤ Subgroup.normalizer (conjClosure L T : Set G) := le_sup_right.trans hU.1.2
  have hLM : L ≤ Subgroup.normalizer (conjClosure L T : Set G) := le_sup_left.trans hU.1.2
  have hN : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
    h331 G T hs hnab hK hT _ L hU.1.1 hTM hL hLM hq
  refine ⟨⟨hU.1.1, hU.1.2, fun M' hM' hle => hU.2 M' ⟨hM', hle⟩⟩, hN, fun H hH => ?_⟩
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  exact ⟨hH.isUniqueMaxOver S hTM, hH.not_le_normalizer hN⟩

theorem stmt3_3_1_of_F4 (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h331 : Stmt3_3_1A_F4) (h332 : Stmt3_3_2MTwo) : Stmt3_3_1_F4 := by
  intro G _ _ T hs hnab hK hT
  refine ⟨h331 G T hs hnab hK hT, fun L hL hq => ?_⟩
  obtain ⟨h1, h3, h4⟩ := corollary_3_3_2_of_F4 h37 h38 h39 h331 hs hnab hK hT hL hq
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hTM₁, hTM₂⟩ := h332 G T hs hnab hK hT L hL hq
  have hHstar : ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H := by
    by_cases h₁ : M₁ = Subgroup.normalizer (conjClosure L T : Set G)
    · exact exists_isHStar_of h1.1 hM₂ hTM₂ (fun h₂ => hne (h₁.trans h₂.symm))
    · exact exists_isHStar_of h1.1 hM₁ hTM₁ h₁
  exact ⟨h1, ⟨M₁, M₂, hne, hM₁, hM₂, hTM₁, hTM₂⟩, hHstar, h3, h4⟩

end CFSG.Quasithin.H13
