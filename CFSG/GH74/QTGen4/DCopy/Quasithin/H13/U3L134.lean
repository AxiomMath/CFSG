module

public import CFSG.Quasithin.H13.U3L134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5RawNat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6HatPlusB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15U

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem part1_of_a6_F4 (h1332 : Stmt13_3_2_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (hH : QTH13 G T L)
    (hA6 : A6.A6CentralQuotient L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hVT : V ≤ T) :
    V ⊓ centralizer (L : Set G) ≤ fsuV1 T V ∧
      Nat.card ↥(fsuV1 T V) = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      ∀ W : Subgroup G, V ⊓ centralizer (L : Set G) ≤ W → W ≤ V →
        T ≤ normalizer (W : Set G) →
        Nat.card W = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) → W = fsuV1 T V := by
  by_cases hZV : V ⊓ centralizer (L : Set G) = ⊥
  · obtain ⟨S⟩ := A6.exists_setting4_of_1332_F4 h1332 hH hA6 hV hZV
    exact part1_of_card_two hVT hZV S.card_V1
  · obtain ⟨S⟩ := A6.exists_setting134_F4 h1332 hH hV hZV
    exact part1_of_setting134 S

theorem stmt13_3_4_of_F4
    (h1332 : Stmt13_3_2_F4) : A6.Stmt13_3_4_F4 := by
  intro G _ _ T L V hH hV
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ, ⟨hTL, -, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨hVT, hTV, -, ⟨hab, hmod⟩⟩ := hall V hV
  have uniqueM : IsUniqueM (L ⊔ T) (normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le le_normalizer hTL⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have hne : ¬ L ≤ centralizer (V : Set G) := by
    intro hle
    have h1 : ⁅V, L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hle)
    exact hV.2.1 (hV.2.2.2.1.symm.trans h1)
  have hloc := hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTL)
  have hOT : pCoreOf 2 L ≤ T := (A6.pCoreOf_le_pCoreOf_sup hTL).trans
    (F7.isSylowTwoOf_pCoreOf_le (A5.isSylowTwoOf_of_le hH.sylow le_sup_right))

  have h3 : ∀ X : Subgroup G, T ≤ X → X < L ⊔ T → A6.IsTwoThreeGroup X := fun X hTX hX =>
    isTwoThreeGroup_of_overgroup hH.sylow.1 hTL hsyl hOT (sylOvergroupProp_of_qt13Five hQ) hTX hX

  have h1 : V ⊓ centralizer (L : Set G) ≤ fsuV1 T V ∧
      Nat.card ↥(fsuV1 T V) = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      ∀ W : Subgroup G, V ⊓ centralizer (L : Set G) ≤ W → W ≤ V →
        T ≤ normalizer (W : Set G) →
        Nat.card W = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) → W = fsuV1 T V := by
    rcases hQ with ⟨⟨e⟩⟩ | hlin | ⟨⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | hU3
    ·
      obtain ⟨-, hZV⟩ := A5.modules13_3_2_of_A5 ⟨e⟩ hLV hne hmod
      have hK5 : quasithinO2QuotientIso L (alternatingGroup (Fin 5)) :=
        (quasithinO2QuotientIso_iff L _).2 ⟨e⟩
      obtain ⟨R⟩ := A5.stmt13_3_2_three_A5_of_F4 h1332 G T L hH L hH.faithful hK5 V hV
      have hV2 : IsPGroup 2 V := hH.sylow.1.to_le hVT
      have hNL : normalizer (V : Set G) ≤ normalizer (L : Set G) := by
        obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
          (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (normalizer (V : Set G)))
        have := uniqueM.2 M' ⟨hM', (sup_le hLV hTV).trans hM'le⟩
        exact this ▸ hM'le
      obtain ⟨F⟩ := A5.exists_frame R hNL hH.sylow.1 hTV hsyl
      exact part1_of_card_two hVT hZV (card_fsuV1_of_a5Frame F hVT)
    ·
      obtain ⟨hnat, hZV⟩ := modules13_3_2_of_L32 hlin hLV hne hmod
      exact part1_of_card_two hVT hZV
        (card_fsuV1_of_L32 hH.sylow.1 hH.sylow.2 hLV hTV hVT hV.2.1 hnat)
    · exact part1_of_a6_F4 h1332 hH (a6CentralQuotient_of_mulEquiv e) hV hVT
    · exact part1_of_a6_F4 h1332 hH ⟨e⟩ hV hVT
    ·
      obtain ⟨z, hF⟩ := u3_frame_of_irrPlus_F4 h1332 hH hU3 hV
      have hc : Nat.card (fsuV1 T V) = 2 := by
        rw [fsuV1_eq hF, hF.2.2.2.2.2.2.2.2.2.2.2.1, Nat.card_zpowers,
          hF.2.2.2.2.2.2.2.2.2.2.2.2]
      exact part1_of_card_two hVT (inf_centralizer_L_eq_bot hF) hc
  exact ⟨h1, conjClosure_eq_of_part1 hV h1.1 h1.2.1, h3⟩

end CFSG.Quasithin.H13.U3
