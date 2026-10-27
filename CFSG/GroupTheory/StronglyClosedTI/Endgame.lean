module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCBasic
import CFSG.GroupTheory.StronglyClosedTI.OddCore
import CFSG.GroupTheory.StronglyClosedTI.Frattini
import CFSG.GroupTheory.StronglyClosedTI.Components
import CFSG.GroupTheory.StronglyClosedTI.OuterBound
import CFSG.LocalAnalysis.OddStandard.ThmCO2GorNormal
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.GroupTheory.StronglyClosedTI

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76X
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC (OutCyc)

section Private

variable {G : Type} [Group G] [Finite G]

private abbrev GoldQuot (Y : Subgroup G) : Type :=
  ↥(normalClosure (Y : Set G)) ⧸ goldschmidtOddCore ↥(normalClosure (Y : Set G))

private abbrev goldImage (Y : Subgroup G) : Subgroup (GoldQuot Y) :=
  (Y.subgroupOf (normalClosure (Y : Set G))).map
    (QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (Y : Set G))))

private abbrev oddImage (Y : Subgroup G) : Subgroup G :=
  (goldschmidtOddCore ↥(normalClosure (Y : Set G))).map (normalClosure (Y : Set G)).subtype

private noncomputable def conjHom (Y : Subgroup G) : G →* MulAut (GoldQuot Y) :=
  MonoidHom.mk' (conjQuot (normalClosure_normal (s := (Y : Set G))))
    (conjQuot_mul (normalClosure_normal (s := (Y : Set G))))

private theorem isMulCommutative_of_mul_self {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1) :
    IsMulCommutative Y := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have h1 : ∀ x : Y, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (Subtype.ext (hY2 x x.2))
  have h2 : (a * b)⁻¹ = a * b := h1 (a * b)
  rw [mul_inv_rev, h1, h1] at h2
  exact h2.symm

private theorem oddImage_normal_odd (Y : Subgroup G) :
    (oddImage Y).Normal ∧ Odd (Nat.card (oddImage Y)) := by
  constructor
  · haveI : (goldschmidtOddCore ↥(normalClosure (Y : Set G))).Characteristic := by
      rw [Subgroup.characteristic_iff_map_eq]
      intro φ
      exact oddCore_map_mulEquiv' φ
    exact ConjAct.normal_of_characteristic_of_normal
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact CFSG.ComponentClassification.OddCore.odd_card _

private theorem commute_oddImage {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G)) :
    ∀ o ∈ oddImage Y, ∀ x ∈ normalClosure (Y : Set G), o * x = x * o := by
  exact commute_normalClosure_of_odd_normal hY2 hY4 hTI (oddImage_normal_odd Y).1
    (oddImage_normal_odd Y).2

private theorem oddCore_le_center {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G)) :
    goldschmidtOddCore ↥(normalClosure (Y : Set G)) ≤ center ↥(normalClosure (Y : Set G)) := by
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro x
  have h := commute_oddImage hY2 hY4 hTI (o : G) ⟨o, ho, rfl⟩ (x : G) x.2
  exact Subtype.ext h.symm

private theorem pCore_goldQuot_eq_bot (hO2 : CFSG.pCore 2 G = ⊥) {Y : Subgroup G}
    (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G)) :
    CFSG.pCore 2 (GoldQuot Y) = ⊥ := by
  have hM : CFSG.pCore 2 ↥(normalClosure (Y : Set G)) = ⊥ := by
    have h := CFSG.OddStandard.ThmC.O2.Gor.gn_pCore_normal_le (normalClosure (Y : Set G))
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
      at h
    exact h
  exact pCore_quotient_eq_bot (oddCore_le_center hY2 hY4 hTI) hM

private theorem oddCore_goldQuot (Y : Subgroup G) :
    ∀ K : Subgroup (GoldQuot Y), K.Normal → Odd (Nat.card K) → K = ⊥ := by
  intro K hK hKodd
  have h : CFSG.oddCore (GoldQuot Y) = ⊥ :=
    oddCore_quotient_oddCore ↥(normalClosure (Y : Set G))
  rw [eq_bot_iff, ← h]
  exact le_sSup ⟨hK, hKodd⟩

private theorem center_goldQuot_eq_bot {Y : Subgroup G} (hP : CFSG.pCore 2 (GoldQuot Y) = ⊥) :
    center (GoldQuot Y) = ⊥ := by
  exact center_eq_bot_of (oddCore_goldQuot Y) fun N hN hN2 =>
    le_bot_iff.mp ((le_openPCore hN hN2).trans hP.le)

private theorem nontrivial_goldQuot {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY4 : 4 ≤ Nat.card Y) : Nontrivial (GoldQuot Y) := by
  haveI : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : Y)
  have hyM : y ∈ normalClosure (Y : Set G) := subset_normalClosure hy
  refine nontrivial_of_ne
    (QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (Y : Set G))) ⟨y, hyM⟩) 1 ?_
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hodd := CFSG.ComponentClassification.OddCore.odd_card ↥(normalClosure (Y : Set G))
  have hdvd : orderOf (⟨y, hyM⟩ : ↥(normalClosure (Y : Set G))) ∣
      Nat.card (goldschmidtOddCore ↥(normalClosure (Y : Set G))) :=
    Subgroup.orderOf_dvd_natCard _ h
  have h2 : orderOf (⟨y, hyM⟩ : ↥(normalClosure (Y : Set G))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext (hY2 y hy))
  have hcop : Nat.gcd 2 (Nat.card (goldschmidtOddCore ↥(normalClosure (Y : Set G)))) = 1 :=
    Nat.coprime_two_left.mpr hodd
  have h1 := Nat.dvd_gcd h2 hdvd
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact hy1 (Subtype.ext (by simpa using congrArg Subtype.val h1))

private theorem goldImage_mul_self {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1) :
    ∀ a ∈ goldImage Y, a * a = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul]
  have : y * y = 1 := Subtype.ext (hY2 y hy)
  rw [this, map_one]

private theorem card_goldImage_le (Y : Subgroup G) : Nat.card (goldImage Y) ≤ Nat.card Y := by
  calc Nat.card (goldImage Y) ≤ Nat.card (Y.subgroupOf (normalClosure (Y : Set G))) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ = Nat.card Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe subset_normalClosure).toEquiv

private theorem goldImage_TI {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G)) :
    ∀ a ∈ goldImage Y, a ≠ 1 → ∀ x : GoldQuot Y, x * a = a * x →
      x ∈ normalizer (goldImage Y : Set (GoldQuot Y)) := by
  intro a ha ha1 x hxa
  exact mem_normalizer_map_of_commute subset_normalClosure
    (oddCore_le_center hY2 hY4 hTI) (CFSG.ComponentClassification.OddCore.odd_card _) hY2 hTI
    ha ha1 hxa

private theorem gold_facts (hGold : GoldschmidtTheoremA) (S : Sylow 2 G) {Y : Subgroup G}
    (hYS : Y ≤ (S : Subgroup G)) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y)
    (hP : CFSG.pCore 2 (GoldQuot Y) = ⊥) :
    CFSG.layer (GoldQuot Y) = ⊤ ∧
      (∃ T : Sylow 2 (GoldQuot Y), ∀ t ∈ (T : Subgroup (GoldQuot Y)), t * t = 1 → t ∈ goldImage Y) ∧
      ∀ K : Subgroup (GoldQuot Y), CFSG.IsComponent K → goldschmidtSimpleType (↥K ⧸ center ↥K) := by
  obtain ⟨ha, hb, hc⟩ := hGold G S Y hYS (isMulCommutative_of_mul_self hY2) hsc
  have hlayer : CFSG.layer (GoldQuot Y) = ⊤ := by
    have ha' : CFSG.pCore 2 (GoldQuot Y) ⊔ goldschmidtLayer (GoldQuot Y) = ⊤ := ha
    rwa [hP, bot_sup_eq, CFSG.Adapters.goldschmidtLayer_eq_foundations] at ha'
  refine ⟨hlayer, ?_, fun K hK => hc K ((CFSG.isComponent_iff_open K).mp hK)⟩
  obtain ⟨P, hP'⟩ :=
    CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal S (normalClosure (Y : Set G))
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective _), fun t ht ht2 => ?_⟩
  have hb' : goldImage Y = CFSG.pCore 2 (GoldQuot Y) ⊔ closure {t | t ∈
      ((S : Subgroup G).subgroupOf (normalClosure (Y : Set G))).map
        (QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (Y : Set G)))) ⊓
        goldschmidtLayer (GoldQuot Y) ∧ t ^ 2 = 1} := hb
  rw [hb', hP, bot_sup_eq]
  refine subset_closure ⟨?_, by rw [pow_two]; exact ht2⟩
  rw [CFSG.Adapters.goldschmidtLayer_eq_foundations, hlayer, inf_top_eq]
  rw [Sylow.coe_mapSurjective, hP'] at ht
  exact ht

private theorem goldQuot_simple (hGold : GoldschmidtTheoremA) (hO2 : CFSG.pCore 2 G = ⊥)
    (S : Sylow 2 G) {Y : Subgroup G} (hYS : Y ≤ (S : Subgroup G)) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y) :
    IsSimpleGroup (GoldQuot Y) ∧ goldschmidtSimpleType (GoldQuot Y) := by
  have hP := pCore_goldQuot_eq_bot hO2 hY2 hY4 hTI
  have hZ := center_goldQuot_eq_bot hP
  obtain ⟨hL, ⟨T, hT⟩, hK⟩ := gold_facts hGold S hYS hY2 hsc hP
  haveI := nontrivial_goldQuot hY2 hY4
  have htop := isComponent_top hL hZ (oddCore_goldQuot Y) T (goldImage_mul_self hY2) hT
    (goldImage_TI hY2 hY4 hTI)
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_top hZ
  exact ⟨isSimpleGroup_of_isComponent_top hZ htop,
    goldschmidtSimpleType_of_mulEquiv e (hK ⊤ htop)⟩

private theorem card_le_of_goldQuot (hGold : GoldschmidtTheoremA) (hO2 : CFSG.pCore 2 G = ⊥)
    (S : Sylow 2 G) {Y : Subgroup G} (hYS : Y ≤ (S : Subgroup G)) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y)
    (E : Subgroup (GoldQuot Y)) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card Y := by
  obtain ⟨-, ⟨T, hT⟩, -⟩ := gold_facts hGold S hYS hY2 hsc (pCore_goldQuot_eq_bot hO2 hY2 hY4 hTI)
  exact (card_le_of_forall_sylow_mem T hT hE2).trans (card_goldImage_le Y)

private theorem mem_centralizer_of_conjHom_eq_one {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G)) {g : G}
    (hg : conjHom Y g = 1) : g ∈ centralizer (normalClosure (Y : Set G) : Set G) := by
  have hodd := (oddImage_normal_odd Y).2
  refine mem_centralizer_closure (s := Group.conjugatesOfSet (Y : Set G)) ?_ hodd ?_ ?_
  · intro v hv
    obtain ⟨a, ha, hav⟩ := Group.mem_conjugatesOfSet_iff.mp hv
    obtain ⟨c, rfl⟩ := isConj_iff.mp hav
    calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [hY2 a ha]; group
  · intro c hc v hv
    exact commute_oddImage hY2 hY4 hTI c hc v (conjugatesOfSet_subset_normalClosure hv)
  · intro v hv
    have hvM : v ∈ normalClosure (Y : Set G) := conjugatesOfSet_subset_normalClosure hv
    have h1 := congrArg (fun φ : MulAut (GoldQuot Y) =>
      φ (QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (Y : Set G))) ⟨v, hvM⟩)) hg
    simp only [conjHom, MonoidHom.mk'_apply, conjQuot_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1.symm
    exact ⟨_, h2, rfl⟩

private theorem conjHom_injOn (hO2 : CFSG.pCore 2 G = ⊥) (S : Sylow 2 G) {Y N : Subgroup G}
    (hYS : Y ≤ (S : Subgroup G)) (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y)
    (hN2 : ∀ x ∈ N, x * x = 1) (hNY : normalizer (Y : Set G) ≤ normalizer (N : Set G))
    {n : G} (hn : n ∈ N) (h1 : conjHom Y n = 1) : n = 1 := by
  have hM := sup_normalizer_eq_top S (M := normalClosure (Y : Set G)) hYS subset_normalClosure hsc
  have hbot := inf_centralizer_eq_bot hO2 hM hNY hN2
  have hc := mem_centralizer_of_conjHom_eq_one hY2 hY4 hTI h1
  have h : n ∈ N ⊓ centralizer (normalClosure (Y : Set G) : Set G) := ⟨hn, hc⟩
  rw [hbot] at h
  exact h

end Private

theorem card_le_two_mul_of_stronglyClosed_TI (hGold : GoldschmidtTheoremA)
    (hOut : ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
      goldschmidtSimpleType L → OutCyc L)
    {G : Type} [Group G] [Finite G] (hO2 : CFSG.pCore 2 G = ⊥)
    (S : Sylow 2 G) {Y N : Subgroup G} (hYS : Y ≤ (S : Subgroup G))
    (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y)
    (hN2 : ∀ x ∈ N, x * x = 1) (hNY : normalizer (Y : Set G) ≤ normalizer (N : Set G)) :
    Nat.card N ≤ 2 * Nat.card Y := by
  obtain ⟨hs, htype⟩ := goldQuot_simple hGold hO2 S hYS hY2 hY4 hTI hsc
  have hOutL := @hOut (GoldQuot Y) _ _ hs htype
  have hZ := center_goldQuot_eq_bot (pCore_goldQuot_eq_bot hO2 hY2 hY4 hTI)
  set f := (conjHom Y).comp N.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro n hn1
    exact Subtype.ext (conjHom_injOn hO2 S hYS hY2 hY4 hTI hsc hN2 hNY n.2 hn1)
  have hA : ∀ a ∈ f.range, a * a = 1 := by
    rintro _ ⟨n, rfl⟩
    rw [← map_mul]
    have : n * n = 1 := Subtype.ext (hN2 n n.2)
    rw [this, map_one]
  have h8 := card_le_two_mul_of_outCyc hZ hOutL
    (card_le_of_goldQuot hGold hO2 S hYS hY2 hY4 hTI hsc) hA
  rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h8

theorem false_of_stronglyClosed_TI (hGold : GoldschmidtTheoremA)
    (hOut : ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
      goldschmidtSimpleType L → OutCyc L)
    {G : Type} [Group G] [Finite G] (hO2 : CFSG.pCore 2 G = ⊥)
    (S : Sylow 2 G) {Y N : Subgroup G} (hYS : Y ≤ (S : Subgroup G))
    (hY2 : ∀ y ∈ Y, y * y = 1) (hY4 : 4 ≤ Nat.card Y)
    (hTI : ∀ y ∈ Y, y ≠ 1 → ∀ g : G, g * y = y * g → g ∈ normalizer (Y : Set G))
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y)
    (hN2 : ∀ x ∈ N, x * x = 1) (hNY : normalizer (Y : Set G) ≤ normalizer (N : Set G))
    (hNq : 2 * Nat.card Y < Nat.card N) : False :=
  absurd (card_le_two_mul_of_stronglyClosed_TI hGold hOut hO2 S hYS hY2 hY4 hTI hsc hN2 hNY)
    (not_le.mpr hNq)

end CFSG.GroupTheory.StronglyClosedTI

end
