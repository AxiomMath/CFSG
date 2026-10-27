module

public import CFSG.GH74.Milestone
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.GH74

open Blueprint

@[expose] def S_restrictedEvenThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.IsRestrictedEvenType G →
        Assembly.evenRank G ≤ 2

@[expose] def S_AS_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → GLS.IsEvenType G → Assembly.evenRank G ≤ 2 → Catalog G

theorem restrictedEven_of_AS (hAS : S_AS_even) (hE2 : S_restrictedEvenThin) :
    S_restrictedEven :=
  fun G _ _ hs hnonab hrank hgen hK hnab hLx hre =>
    hAS G hs hnonab (kProper_of_kgh hK) hre.isEvenType
      (hE2 G hs hnonab hrank hgen hK hnab hLx hre)

@[expose] def S_QTKE_evenChar_native : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → Assembly.Quasithin.quasithinEvenCharacteristic G →
      Assembly.evenRank G ≤ 2 → Catalog G

theorem s_QTKE_evenChar_native_of_milestone
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      QuasithinUnique.quasithinIsQTKECat G → Catalog G) : S_QTKE_evenChar_native :=
  fun G _ _ hs hnonab hK hev he => by
    have := hs
    exact h G hnonab ⟨hK, hev, he⟩

@[expose] def S_ALSS3121 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → GLS.IsEvenType G → Assembly.evenRank G ≤ 2 →
      ¬ Assembly.Quasithin.quasithinEvenCharacteristic G → NativeSporadic.IsSporadic G .J1

theorem AS_even_of_parts (hQ : S_QTKE_evenChar_native) (h : S_ALSS3121) : S_AS_even := by
  intro G _ _ hs hnonab hK hev he
  by_cases hec : Assembly.Quasithin.quasithinEvenCharacteristic G
  · exact hQ G hs hnonab hK hec he
  · exact catalog_of_isSporadic (h G hs hnonab hK hev he hec)

theorem s_QTKE_Gen4_of_evenChar (h : S_QTKE_evenChar_native) : S_QTKE_Gen4 :=
  fun G _ _ hs hnonab _ _ hK hev he => h G hs hnonab (kProper_of_kgh hK) hev he

theorem qtke_native_of_evenChar (h : S_QTKE_evenChar_native) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      Assembly.KProper Catalog G → Assembly.IsCharTwoType G → Assembly.evenRank G ≤ 2 →
        Catalog G :=
  fun G _ _ _ hnonab hK hchar he =>
    h G inferInstance hnonab hK (quasithinEvenCharacteristic_of_isCharTwoType hchar) he

@[expose] def S_generic' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.L2Meets G GLS.InG2 → Catalog G

theorem generic_of_catalog
    (h : S_generic') : S_generic :=
  fun G _ _ hs hnonab hrank hgen hK hnab hLx hg =>
    s_filter G (h G hs hnonab hrank hgen hK hnab hLx hg) hnonab hrank hgen

@[expose] def S_C23_native : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → GLS.IsSpecialOddType G → GLS.C23List G

theorem specialOdd_of_C23_native (h : S_C23_native) : S_specialOdd :=
  fun G _ _ hs hnonab _ _ hK _ _ hSO => h G hs hnonab (kProper_of_kgh hK) hSO

theorem milestone_forms_of_refined_inputs
    (hW : S_walterNative) (hQ : S_QTKE_evenChar_native)
    (hALSS : S_ALSS3121) (hE2 : S_restrictedEvenThin) (hGen : S_generic')
    (hC23 : S_C23_native) : ModelsFormStatement ∧ OrderFormStatement :=
  milestone_forms_of_inputs hW (s_QTKE_Gen4_of_evenChar hQ)
    (restrictedEven_of_AS (AS_even_of_parts hQ hALSS) hE2) (generic_of_catalog hGen)
    (specialOdd_of_C23_native hC23)

end CFSG.GH74
