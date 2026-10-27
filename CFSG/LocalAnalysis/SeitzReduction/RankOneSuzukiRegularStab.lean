module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiPartition

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem card_outer_dvd_of_lieModel_twistedB2 {Y : Type} [Group Y]
    {f : ℕ} (h : LieModel Y .twistedB2 0 2 f) : Nat.card (Outer Y) ∣ f := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2

theorem zpowers_mem_gmsRootConjugates_szA {G : Type*} [Group G] (L T : Subgroup G) (t : G) :
    zpowers t ∈ gmsRootConjugates (szA L T t) (zpowers t) :=
  SzPartitionData.zpowers_mem

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_normalizer_szT₁_inf_of_card_sylow
    (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (normalizer (szT₁ L T : Set G) ⊓ L : Subgroup G) = (2 ^ f) ^ 2 * (2 ^ f - 1) := by
  obtain ⟨-, -, Q, hQ⟩ := h.eq_sup_of_card_sylow hS2
  obtain ⟨-, -, -, hB⟩ := exists_benderType_of_lieModel_twistedB2 h.model
  obtain ⟨t₀, hcore⟩ := hB.exists_benderCore Q
  have h1 := hcore.card_borel
  rw [CFSG.GH74.Uniqueness.Bender.borel, hQ, ← subgroupOf_normalizer_eq (szT₁_le_right L T),
    mul_one] at h1
  rw [← h1, ← inf_subgroupOf_right]
  exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem not_mem_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) : t ∉ L := by
  obtain ⟨hTeq, hdisj, -⟩ := h.eq_sup_of_card_sylow hS2
  intro htL
  have htT : t ∈ T := by
    rw [hTeq]
    exact mem_sup_right (mem_zpowers t)
  have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨mem_inf.mpr ⟨htT, htL⟩, mem_zpowers t⟩
  rw [hdisj, mem_bot] at ht1
  have h2 := h.inv
  rw [ht1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem card_normalizer_szA_inf_centralizer_dvd_of_card_sylow
    (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (normalizer (szA L T t : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∣
      2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := by
  have hst := h.setting.standardSetting
  obtain ⟨-, -, -, -, -, -, -, hCA, -⟩ := h.facts_of_card_sylow hS2
  have hHN := (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    hst.standard h.mem h.inv).1
  have hCt := (inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv
    (hst.core t h.inv)).le
  set M := normalizer (szA L T t : Set G) ⊓ centralizer ({t} : Set G)
  have hML : M ≤ normalizer (L : Set G) := inf_le_right.trans hHN
  have hMT : M ≤ normalizer (szT₁ L T : Set G) := by
    refine le_trans (le_inf ?_ hML) (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := L))
    refine inf_le_left.trans ?_
    have h1 := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (szA L T t)
    rwa [hCA] at h1
  have hkey := card_dvd_card_sup_mul_card_outer hML hMT inf_le_right h.mem hCt
    (szT₁_le_right L T)
  have hdisj : (normalizer (szT₁ L T : Set G) ⊓ L) ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hxt⟩ := mem_inf.mp hx
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hxt with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.mp hx1).2 (h.not_mem_of_card_sylow hS2)
  rw [card_sup_zpowers_of_disjoint (centralizer_le inf_le_right h.mem) h.inv hdisj,
    h.card_normalizer_szT₁_inf_of_card_sylow hS2] at hkey
  refine hkey.trans ?_
  have hout := card_outer_dvd_of_lieModel_twistedB2 h.model
  calc (2 ^ f) ^ 2 * (2 ^ f - 1) * 2 * Nat.card (Outer L) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * 2 * f :=
        Nat.mul_dvd_mul_left _ hout
    _ = 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := by ring

theorem card_normalizer_szA_inf_centralizer_eq_of_card_sylow
    (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) :
    Nat.card (normalizer (szA L T t : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) =
      Nat.card ((gmsRootConjugateAction (szA L T t) (zpowers t)).range ⊓
        MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))
          (⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩ :
            gmsRootConjugates (szA L T t) (zpowers t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))) * Nat.card T := by
  have hD := h.partitionData_of_card_sylow hS2 hT
  obtain ⟨-, -, -, -, -, -, -, hCA, -⟩ := h.facts_of_card_sylow hS2
  set NA := normalizer (szA L T t : Set G)
  set α : gmsRootConjugates (szA L T t) (zpowers t) :=
    ⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩
  have key := card_stabilizer_eq_card_range_inf_mul (H := NA) α
  have hstab : (MulAction.stabilizer NA α).map NA.subtype =
      NA ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hl
      have h1 : (zpowers t).map (MulAut.conj (l : G)).toMonoidHom = zpowers t :=
        congrArg Subtype.val hl
      exact mem_inf.mpr ⟨l.2, mem_centralizer_singleton_iff.mpr
        ((hD.map_conj_zpowers_eq_iff l).mp h1)⟩
    · intro hx
      obtain ⟨hxN, hxC⟩ := mem_inf.mp hx
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      exact (hD.map_conj_zpowers_eq_iff x).mpr (mem_centralizer_singleton_iff.mp hxC)
  have hker : (MulAction.toPermHom NA (gmsRootConjugates (szA L T t) (zpowers t))).ker.map
      NA.subtype = T := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (h.action_eq_one_iff_of_card_sylow hS2 hT l).mp (MonoidHom.mem_ker.mp hl)
    · intro hx
      have hxN : x ∈ NA := by
        rw [← hCA] at hx
        exact centralizer_le_normalizer _ hx
      exact ⟨⟨x, hxN⟩, MonoidHom.mem_ker.mpr
        ((h.action_eq_one_iff_of_card_sylow hS2 hT ⟨x, hxN⟩).mpr hx), rfl⟩
  have hkerc : Nat.card (MulAction.toPermHom NA (gmsRootConjugates (szA L T t) (zpowers t))).ker =
      Nat.card T := by
    rw [← Subgroup.card_map_of_injective NA.subtype_injective, hker]
  rw [← hstab, Subgroup.card_map_of_injective NA.subtype_injective, key, hkerc]
  rfl

theorem stabilizer_odd_dvd_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) :
    Odd (Nat.card ((gmsRootConjugateAction (szA L T t) (zpowers t)).range ⊓
        MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))
          (⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩ :
            gmsRootConjugates (szA L T t) (zpowers t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))))) ∧
    Nat.card ((gmsRootConjugateAction (szA L T t) (zpowers t)).range ⊓
        MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))
          (⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩ :
            gmsRootConjugates (szA L T t) (zpowers t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))) ∣
      (2 ^ f - 1) * f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := h.card_normalizer_szA_inf_centralizer_eq_of_card_sylow hS2 hT
  have hdvd := h.card_normalizer_szA_inf_centralizer_dvd_of_card_sylow hS2
  obtain ⟨-, -, hcardT, -⟩ := h.facts_of_card_sylow hS2
  set n := Nat.card ((gmsRootConjugateAction (szA L T t) (zpowers t)).range ⊓
        MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))
          (⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩ :
            gmsRootConjugates (szA L T t) (zpowers t)) :
          Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))))
  have hTpos : 0 < Nat.card T := Nat.card_pos
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨P, hP⟩ := h.sylow
    have hidx := P.not_dvd_index
    have hC := Subgroup.card_mul_index (P : Subgroup (centralizer ({t} : Set G)))
    rw [hP, Nat.card_congr (subgroupOfEquivOfLe h.le).toEquiv] at hC
    rw [hP] at hidx
    have hMC := Subgroup.card_dvd_of_le
      (inf_le_right : normalizer (szA L T t : Set G) ⊓ centralizer ({t} : Set G) ≤
        centralizer ({t} : Set G))
    rw [hcard, ← hC, mul_comm n] at hMC
    have h2 := Nat.dvd_of_mul_dvd_mul_left hTpos hMC
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2n => hidx (h2n.trans h2)
  · rw [hcard, hcardT] at hdvd
    have hq : 0 < 2 * (2 ^ f) ^ 2 := by positivity
    refine Nat.dvd_of_mul_dvd_mul_left hq ?_
    calc 2 * (2 ^ f) ^ 2 * n = n * (2 * 2 ^ f * 2 ^ f) := by ring
      _ ∣ 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := hdvd

end SzStart

end CFSG.SeitzReduction.RankOne
