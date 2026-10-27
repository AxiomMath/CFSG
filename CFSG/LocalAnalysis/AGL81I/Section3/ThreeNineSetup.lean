module

public import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn)

local notation "pRank" => CFSG.Open.pRank

variable {G : Type} [Group G] [Finite G]

theorem gammaIn_mono_right {k p : ℕ} {A H T : Subgroup G} (hp : 1 < p) (hHT : H ≤ T) :
    gammaIn k p A H ≤ gammaIn k p A T := by
  rw [gammaIn, gammaIn]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff k p (A.subgroupOf H)
    ((gammaIn k p A T).comap H.subtype)).mpr ?_
  intro Q hQ hQrank
  let Q' : Subgroup T := Q.map (Subgroup.inclusion hHT)
  have hQ'le : Q' ≤ A.subgroupOf T := by
    intro q hq
    dsimp [Q'] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using hQ hq₀
  have hQ'rank : k ≤ pRank p Q' := by
    have hQtop : k ≤ pRank p (⊤ : Subgroup ↥Q) := by
      rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Q] at hQrank
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Q']
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp
      (Q.equivMapOfInjective (Subgroup.inclusion hHT) (Subgroup.inclusion_injective hHT))]
  have hNmap : (Subgroup.normalizer (Q : Set ↥H)).map H.subtype ≤ gammaIn k p A T := by
    have hN₁ : (Subgroup.normalizer (Q : Set ↥H)).map (Subgroup.inclusion hHT) ≤
        Subgroup.normalizer (Q' : Set T) :=
      Subgroup.le_normalizer_map (Subgroup.inclusion hHT)
    have hN₂ : Subgroup.normalizer (Q' : Set T) ≤
        CFSG.Open.rankThreeGamma k p (A.subgroupOf T) :=
      CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le k p (A.subgroupOf T) Q'
        hQ'le hQ'rank
    have hmap : ((Subgroup.normalizer (Q : Set ↥H)).map (Subgroup.inclusion hHT)).map
          T.subtype = (Subgroup.normalizer (Q : Set ↥H)).map H.subtype := by
      rw [Subgroup.map_map, Subgroup.subtype_comp_inclusion]
    rw [← hmap]
    simpa only [gammaIn] using Subgroup.map_mono (hN₁.trans hN₂)
  exact Subgroup.map_le_iff_le_comap.mp hNmap

theorem le_gammaIn_self {k p : ℕ} {D T : Subgroup G} (hDT : D ≤ T)
    (hrank : k ≤ pRank p (D.subgroupOf T)) : D ≤ gammaIn k p D T := by
  have hself : D.subgroupOf T ≤ Subgroup.normalizer ((D.subgroupOf T : Subgroup T) : Set T) :=
    Subgroup.le_normalizer
  have hcore : Subgroup.normalizer ((D.subgroupOf T : Subgroup T) : Set T) ≤
      CFSG.Open.rankThreeGamma k p (D.subgroupOf T) :=
    CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le k p (D.subgroupOf T)
      (D.subgroupOf T) le_rfl hrank
  calc
    D = (D.subgroupOf T).map T.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDT]
    _ ≤ (Subgroup.normalizer ((D.subgroupOf T : Subgroup T) : Set T)).map T.subtype :=
      Subgroup.map_mono hself
    _ ≤ (CFSG.Open.rankThreeGamma k p (D.subgroupOf T)).map T.subtype :=
      Subgroup.map_mono hcore
    _ = gammaIn k p D T := rfl

theorem threeNine_gammaE_lt_K (X : Type) [Group X] [Finite X]
    (K E D X₁ : Subgroup X) (p d : ℕ)
    (hp : p.Prime) (_hp2 : p ≠ 2)
    (_hKq : CFSG.IsQuasisimple ↥K)
    (_hOp : CFSG.pPrimeCore p ↥K = ⊥)
    (_hKcat : CFSG.SectionRank.IsKGroupCat ↥K)
    (_hKnorm : K.Normal)
    (_hrank1 : 1 < CFSG.Open.pRank p (⊤ : Subgroup X))
    (_hrank3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (_hEel : CFSG.Open.IsElemAbelian p E) (_hEcard : Nat.card E = p ^ 2)
    (hdp : d.Prime) (_hd2 : d ≠ 2) (_hdpne : d ≠ p)
    (hDsyl : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hDne : D ≠ ⊥)
    (hX1 : X₁ < K ⊔ D)
    (hΓE : gammaIn 1 p E (K ⊔ D) ≤ X₁)
    (hΓD : gammaIn 1 d D (K ⊔ D) ≤ X₁)
    (_hN : ∀ Q : Subgroup X, IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set X) ⊓ (K ⊔ D) ≤ X₁) :
    gammaIn 1 p E K < K := by
  have hp1 : 1 < p := by
    have h2 := hp.two_le
    omega
  have hfact : Fact d.Prime := ⟨hdp⟩
  have hDp : IsPGroup d D := hDsyl.isPGroup
  have hDsubp : IsPGroup d (D.subgroupOf (K ⊔ D)) :=
    hDp.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_right : D ≤ K ⊔ D)).symm
  have hDsubne : D.subgroupOf (K ⊔ D) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff, inf_eq_left.mpr (le_sup_right : D ≤ K ⊔ D)] at hbot
    exact hDne hbot
  have hDrank : 1 ≤ pRank d (D.subgroupOf (K ⊔ D)) := by
    have hdvd : d ∣ Nat.card (D.subgroupOf (K ⊔ D)) :=
      hDsubp.card_eq_or_dvd.resolve_left fun h =>
        hDsubne (Subgroup.card_eq_one.mp h)
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d)
      (D.subgroupOf (K ⊔ D))]
    exact CFSG.one_le_pRank_of_dvd_card hdp hdvd
  have hDleΓ : D ≤ gammaIn 1 d D (K ⊔ D) :=
    le_gammaIn_self (le_sup_right : D ≤ K ⊔ D) hDrank
  have hDleX1 : D ≤ X₁ := hDleΓ.trans hΓD
  refine lt_of_le_of_ne (gammaIn_le 1 p E K) ?_
  intro hEq
  have hmono : gammaIn 1 p E K ≤ gammaIn 1 p E (K ⊔ D) :=
    gammaIn_mono_right hp1 (le_sup_left : K ≤ K ⊔ D)
  have hKleΓ : K ≤ gammaIn 1 p E (K ⊔ D) := hEq.ge.trans hmono
  have hKleX1 : K ≤ X₁ := hKleΓ.trans hΓE
  have hKDleX1 : K ⊔ D ≤ X₁ := sup_le hKleX1 hDleX1
  exact (ne_of_lt hX1) (le_antisymm hX1.le hKDleX1)

theorem threeNine_mp_KE_le_three (X : Type) [Group X] [Finite X]
    (K E D X₁ : Subgroup X) (p d : ℕ)
    (hp : p.Prime) (_hp2 : p ≠ 2)
    (_hKq : CFSG.IsQuasisimple ↥K)
    (_hOp : CFSG.pPrimeCore p ↥K = ⊥)
    (_hKcat : CFSG.SectionRank.IsKGroupCat ↥K)
    (_hKnorm : K.Normal)
    (_hrank1 : 1 < CFSG.Open.pRank p (⊤ : Subgroup X))
    (hrank3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (_hEel : CFSG.Open.IsElemAbelian p E) (_hEcard : Nat.card E = p ^ 2)
    (_hdp : d.Prime) (_hd2 : d ≠ 2) (_hdpne : d ≠ p)
    (_hDsyl : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (_hDne : D ≠ ⊥)
    (_hX1 : X₁ < K ⊔ D)
    (_hΓE : gammaIn 1 p E (K ⊔ D) ≤ X₁)
    (_hΓD : gammaIn 1 d D (K ⊔ D) ≤ X₁)
    (_hN : ∀ Q : Subgroup X, IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set X) ⊓ (K ⊔ D) ≤ X₁) :
    pRank p (K ⊔ E) ≤ 3 := by
  have hp1 : 1 < p := by
    have h2 := hp.two_le
    omega
  exact (CFSG.SectionRank.pRank_mono hp1 (le_top : K ⊔ E ≤ ⊤)).trans hrank3

theorem threeNine_D_faithful (X : Type) [Group X] [Finite X]
    (K E D X₁ : Subgroup X) (p d : ℕ)
    (_hp : p.Prime) (_hp2 : p ≠ 2)
    (_hKq : CFSG.IsQuasisimple ↥K)
    (_hOp : CFSG.pPrimeCore p ↥K = ⊥)
    (_hKcat : CFSG.SectionRank.IsKGroupCat ↥K)
    (hKnorm : K.Normal)
    (_hrank1 : 1 < CFSG.Open.pRank p (⊤ : Subgroup X))
    (_hrank3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (_hEel : CFSG.Open.IsElemAbelian p E) (_hEcard : Nat.card E = p ^ 2)
    (hdp : d.Prime) (_hd2 : d ≠ 2) (_hdpne : d ≠ p)
    (hDsyl : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (_hDne : D ≠ ⊥)
    (hX1 : X₁ < K ⊔ D)
    (_hΓE : gammaIn 1 p E (K ⊔ D) ≤ X₁)
    (hΓD : gammaIn 1 d D (K ⊔ D) ≤ X₁)
    (_hN : ∀ Q : Subgroup X, IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set X) ⊓ (K ⊔ D) ≤ X₁) :
    D ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  have hfact : Fact d.Prime := ⟨hdp⟩
  have hKN : K.Normal := hKnorm
  have hDp : IsPGroup d D := hDsyl.isPGroup
  have hNil : Group.IsNilpotent ↥D := hDp.isNilpotent
  by_contra hne
  set T : Subgroup X := K ⊔ D with hT
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hC
  set H : Subgroup X := D ⊓ C with hH
  have hDT : D ≤ T := by rw [hT]; exact le_sup_right
  have hKT : K ≤ T := by rw [hT]; exact le_sup_left
  have hHD : H ≤ D := by rw [hH]; exact inf_le_left
  have hHne : H ≠ ⊥ := by rw [hH]; exact hne
  have hΓD' : gammaIn 1 d D T ≤ X₁ := by rw [hT]; exact hΓD
  have hX1' : X₁ < T := by rw [hT]; exact hX1
  have hCN : C.Normal := by rw [hC]; infer_instance
  have hHsubne : H.subgroupOf D ≠ ⊥ := by
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff, inf_eq_left.mpr hHD] at hbot
    exact hHne hbot
  have hHnorm : (H.subgroupOf D).Normal := by
    have hCH : H.subgroupOf D = C.subgroupOf D := by
      rw [hH]
      exact Subgroup.inf_subgroupOf_left C D
    rw [hCH]
    infer_instance
  let A : Subgroup ↥D := H.subgroupOf D ⊓ Subgroup.center (↥D)
  have hAne : A ≠ ⊥ := by
    dsimp [A]
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥D) hHsubne
  have hAp : IsPGroup d A := hDp.to_subgroup A
  let Q : Subgroup T := A.map (Subgroup.inclusion hDT)
  have hQne : Q ≠ ⊥ := by
    dsimp [Q]
    rw [Subgroup.map_eq_bot_iff_of_injective (H := A) (Subgroup.inclusion_injective hDT)]
    exact hAne
  have hQp : IsPGroup d Q := by
    dsimp [Q]
    exact hAp.of_equiv (A.equivMapOfInjective (Subgroup.inclusion hDT)
      (Subgroup.inclusion_injective hDT))
  have hQleD : Q ≤ D.subgroupOf T := by
    intro q hq
    dsimp [Q] at hq
    obtain ⟨a, _ha, rfl⟩ := Subgroup.mem_map.mp hq
    exact Subgroup.mem_subgroupOf.mpr a.2
  have hQdvd : d ∣ Nat.card Q :=
    hQp.card_eq_or_dvd.resolve_left fun h => hQne (Subgroup.card_eq_one.mp h)
  have hQrank : 1 ≤ pRank d Q := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) Q]
    exact CFSG.one_le_pRank_of_dvd_card hdp hQdvd
  have hAleH : A ≤ H.subgroupOf D := by dsimp [A]; exact inf_le_left
  have hAleZ : A ≤ Subgroup.center (↥D) := by dsimp [A]; exact inf_le_right
  have hQK : Q ≤ Subgroup.centralizer (K.subgroupOf T : Set T) := by
    intro q hq
    dsimp [Q] at hq
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    have haH : ((a : D) : X) ∈ H := hAleH ha
    have haH' : ((a : D) : X) ∈ D ⊓ C := by rwa [hH] at haH
    have haC : ((a : D) : X) ∈ Subgroup.centralizer (K : Set X) := haH'.2
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro k hk
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp haC (k : X)
      (Subgroup.mem_subgroupOf.mp hk))
  have hQD : Q ≤ Subgroup.centralizer (D.subgroupOf T : Set T) := by
    intro q hq
    dsimp [Q] at hq
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    have haZ : a ∈ Subgroup.center (↥D) := hAleZ ha
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro d hd
    exact Subtype.ext (congrArg (fun z : ↥D => (z : X))
      (Subgroup.mem_center_iff.mp haZ ⟨(d : X), Subgroup.mem_subgroupOf.mp hd⟩))
  have hKQT : K.subgroupOf T ≤ Subgroup.centralizer (Q : Set T) :=
    (Subgroup.le_centralizer_iff).mp hQK
  have hDQT : D.subgroupOf T ≤ Subgroup.centralizer (Q : Set T) :=
    (Subgroup.le_centralizer_iff).mp hQD
  have hTQ : (⊤ : Subgroup T) ≤ Subgroup.centralizer (Q : Set T) := by
    have hsup : K.subgroupOf T ⊔ D.subgroupOf T = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKT hDT, hT, Subgroup.subgroupOf_self]
    rw [← hsup]
    exact sup_le hKQT hDQT
  have hQnorm : Subgroup.normalizer (Q : Set T) = ⊤ :=
    eq_top_iff.mpr (hTQ.trans (Subgroup.centralizer_le_normalizer (Q : Set T)))
  have hcore : CFSG.Open.rankThreeGamma 1 d (D.subgroupOf T) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hQnorm]
    exact CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 d
      (D.subgroupOf T) Q hQleD hQrank
  have hgamma : gammaIn 1 d D T = T := by
    rw [gammaIn, hcore, Subgroup.map_top, Subgroup.range_subtype]
  have hTleX1 : T ≤ X₁ := by
    rw [← hgamma]
    exact hΓD'
  exact (ne_of_lt hX1') (le_antisymm hX1'.le hTleX1)

end CFSG.LocalAnalysis.AGL81I.Section3
