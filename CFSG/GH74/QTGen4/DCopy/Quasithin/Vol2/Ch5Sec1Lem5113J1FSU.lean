module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL5C
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1FSU

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L34Orders J1Orders
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem false_of_j1_of_faithful_F4
    (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C_F4)
    {T L : Subgroup G} (hsG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hq : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hmax : quasithinIsMaximalLocal T L) (hLf : quasithinIsFaithfulLocal T L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hJ : IsSporadic .J1 (O2Q L)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : ⁅L, L⁆ = L := hmax.1.2.1.2.1
  have hs : IsSimpleGroup (O2Q L) := by
    obtain ⟨f⟩ := hJ
    exact (MulEquiv.isSimpleGroup_congr f).mpr CFSG.Sporadic.J1.isSimpleGroup_J1
  have hqs : CFSG.IsQuasisimple (O2Q L) := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
    have : Group.IsPerfect (O2Q L) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact isQuasisimple_of_isSimpleGroup_of_isPerfect
  obtain ⟨V₀, hV₀, hfsu⟩ := exists_fsu_of_faithful h323 hsG hnab hq hT hmax hLf hL hs hqs hTL
  have hLL : L = conjClosure L T := (Vol2.Ch11.SecA.conjClosure_eq_of_le_normalizer hTL).symm
  have hR : V₀ ≤ reducedAggregate (L ⊔ T) := hV₀.1
  have hLV₀ : L ≤ Subgroup.normalizer (V₀ : Set G) := hV₀.2.2.1
  have hne₀ : ¬ L ≤ Subgroup.centralizer (V₀ : Set G) := not_le_centralizer_of_isIrrPlusIn hV₀
  have hLV : L ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    le_normalizer_conjClosure_of_le hTL hLV₀
  have hVR : conjClosure V₀ T ≤ reducedAggregate (L ⊔ T) :=
    Hyp5_1_14.conjClosure_le_reducedAggregate hR
  have hneV : ¬ L ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV := card_autOn_j1 hJ hTL hLV hVR hneV
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hLL
  have hVeq : V₀ = conjClosure V₀ T := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hlist, -⟩
    · exact h1
    · exact h1
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact card_SL3_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · exact card_statedSp_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 6 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL4_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL5_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 7 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
  have hcard := card_autOn_j1 hJ hTL hLV₀ hR hne₀
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T
  obtain ⟨k, hk⟩ := exists_card_autOn_sup hLV₀ hTV₀ hTL hT.1
  rw [hcard] at hk
  have hc : IsMulCommutative ↥V₀ :=
    ⟨⟨fun a b => Subtype.ext ((reducedAggregate_props _).2.1 _ (hR a.2) _ (hR b.2))⟩⟩
  obtain ⟨hk1, hk2, hk3, hk4⟩ := mul_two_pow_ne_j1 k
  by_cases hFF : IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn L V₀ : Set (MulAut ↥V₀))))
  ·
    obtain ⟨_, hcases⟩ := h328 G T L V₀ hfsu hLL hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, hl, -⟩ | ⟨⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ, ⟨e⟩, -⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨he, -⟩ | ⟨⟨e⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_two_pow_ne_j1 _ h1.symm
    · exact card_SL3_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_SL3_ne_j1 (F := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)
        ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_statedSp_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_G2_derived_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 5 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_alt 7 (by norm_num), show Nat.factorial 7 / 2 = 2520 by decide] at h1
      exact hk1 h1
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(autOn L V₀))
      rw [hcard, hZ, Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · rcases hm with rfl | rfl
      · have h1 := Nat.card_congr e.toEquiv
        rw [hk, card_SL4_two] at h1
        exact hk2 h1
      · have h1 := Nat.card_congr e.toEquiv
        rw [hk, card_SL5_two] at h1
        exact hk3 h1
    · obtain ⟨e⟩ := he
      have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_SL4_two] at h1
      norm_num at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_SL5_two] at h1
      exact hk3 h1
  ·
    obtain ⟨_, hcases⟩ := h329 G T L V₀ hfsu hLL hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, -, hl, -⟩ | ⟨m, hSU, -⟩ | ⟨f, hSz, -⟩ |
      ⟨m, F, _, _, _, hm, hF, hl, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, -, ⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_two_pow_ne_j1 _ h1.symm
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := BinaryNaturalSU3.exists_equiv hSU
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := F)
        rw [hF] at this
        norm_num at this
      have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := m * 2) (by omega)
        (by rw [hF, pow_mul])
      exact card_statedSU_ne_j1 hF ((Nat.card_congr e.toEquiv).trans hcard)
    · obtain ⟨a, F, _, _, ha, hf, hF, ⟨e⟩⟩ := BinaryNaturalSz.exists_equiv hSz
      have hSzM : SuzukiModel ↥(autOn L V₀) 2 f := ⟨rfl, a, ha, F, inferInstance,
        inferInstance, hf, hF, ⟨e.symm⟩⟩
      obtain ⟨-, a', -, hf', hc'⟩ := CFSG.GH74.card_of_suzukiModel hSzM
      rw [hcard] at hc'
      apply not_three_dvd_ordSuzuki (f := f) ⟨a', hf'⟩
      rw [← hc']
      norm_num
    · rcases hl with hl | he
      · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
        rw [hcard] at h1
        exact ordA_two_two_pow_ne_j1 _ h1.symm
      · obtain ⟨e⟩ := he
        exact card_statedSL3_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, CFSG.ComponentClassification.M12Cover.card_mulAut] at h1
      exact hk4 h1
    · have h1 := Subgroup.card_quotient_dvd_card (Subgroup.center ↥(autOn L V₀))
      rw [Nat.card_congr e.toEquiv, hcard, CFSG.Sporadic.Mathieu.card_M22] at h1
      norm_num at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hcard, CFSG.Sporadic.Mathieu.card_M22] at h1
      norm_num at h1
    · have h23 := twentyThree_dvd_card_M23
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      norm_num at h23
    · have h23 := twentyThree_dvd_card_M24
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      norm_num at h23

end CFSG.Quasithin.H13
