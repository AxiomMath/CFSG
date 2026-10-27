module

import CFSG.LocalAnalysis.ABGTheoremB.V4Hall
public import CFSG.LocalAnalysis.GH72.Sec4C
public import CFSG.LocalAnalysis.GH72.Sec5DTools

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

namespace G5d

open CFSG.ABGLocalTools (IsSylowOf)

section Permutable

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem O_eq_self_of_odd {H : Subgroup G} (hH : Odd (Nat.card H)) : O H = H := by
  refine le_antisymm (map_subtype_le _) (fun h hh => ?_)
  have hle : (⊤ : Subgroup H) ≤ CFSG.oddCore H :=
    CFSG.ABGLocalTools.le_oddCore_of_normal inferInstance (by rwa [card_top])
  exact ⟨⟨h, hh⟩, hle (mem_top _), rfl⟩

omit [Finite G] in
theorem card_sup_of_mul_comm {H K : Subgroup G}
    (h : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) (hHK : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  have hcoe := coe_sup_eq_mul_of_mul_comm h
  let φ : H × K → (H ⊔ K : Subgroup G) := fun x => ⟨x.1 * x.2, mul_mem_sup x.1.2 x.2.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
      have h1 : a * b = a' * b' := congrArg Subtype.val hab
      have h2 : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
          _ = b' * b⁻¹ := by group
      have h3 : a'⁻¹ * a ∈ H ⊓ K :=
        ⟨H.mul_mem (H.inv_mem ha') ha, h2 ▸ K.mul_mem hb' (K.inv_mem hb)⟩
      rw [hHK, mem_bot] at h3
      have hae : a = a' := (inv_mul_eq_one.mp h3).symm
      subst hae
      have hbe : b = b' := mul_left_cancel h1
      subst hbe
      rfl
    · rintro ⟨g, hg⟩
      have hg' : g ∈ ((H ⊔ K : Subgroup G) : Set G) := hg
      rw [hcoe] at hg'
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective φ hφ).symm

variable {p t : ℕ} [hp : Fact p.Prime] [ht : Fact t.Prime]

omit [Finite G] in
include hp ht in
theorem inf_eq_bot_of_ne (hpt : p ≠ t) {P F : Subgroup G} (hP : IsPGroup p P)
    (hF : IsPGroup t F) : P ⊓ F = ⊥ :=
  (IsPGroup.disjoint_of_ne p t hpt P F hP hF).eq_bot

omit [Finite G] in
include hp ht in
theorem card_sup_of_mul_comm' (hpt : p ≠ t) {P F : Subgroup G} (hP : IsPGroup p P)
    (hF : IsPGroup t F) (hPF : (P : Set G) * (F : Set G) = (F : Set G) * (P : Set G)) :
    Nat.card (P ⊔ F : Subgroup G) = Nat.card P * Nat.card F :=
  card_sup_of_mul_comm hPF (inf_eq_bot_of_ne hpt hP hF)

include hp ht in
theorem isSylowOf_right_of_mul_comm (hpt : p ≠ t) {P F : Subgroup G} (hP : IsPGroup p P)
    (hF : IsPGroup t F) (hPF : (P : Set G) * (F : Set G) = (F : Set G) * (P : Set G)) :
    IsSylowOf t F (P ⊔ F) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_right, hF, fun hdvd => ?_⟩
  have h1 := relIndex_mul_card F (P ⊔ F)
  rw [inf_eq_left.mpr (le_sup_right : F ≤ P ⊔ F), card_sup_of_mul_comm' hpt hP hF hPF] at h1
  have h2 : F.relIndex (P ⊔ F) = Nat.card P := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [h2] at hdvd
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at hdvd
  exact hpt ((Nat.prime_dvd_prime_iff_eq ht.out hp.out).mp (ht.out.dvd_of_dvd_pow hdvd)).symm

include hp ht in
theorem pPrimeCore_eq_bot_of_pCore_eq_bot (hpt : p ≠ t) {P F : Subgroup G} (hP : IsPGroup p P)
    (hF : IsPGroup t F) (hPF : (P : Set G) * (F : Set G) = (F : Set G) * (P : Set G))
    (hcore : CFSG.pCore p ↥(P ⊔ F) = ⊥) : CFSG.pPrimeCore t ↥(P ⊔ F) = ⊥ := by
  set N : Subgroup ↥(P ⊔ F) := CFSG.pPrimeCore t ↥(P ⊔ F) with hN
  have hNn : N.Normal := CFSG.pPrimeCore_normal
  have hcop : Nat.Coprime t (Nat.card N) := CFSG.pPrimeCore_coprime_card
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  obtain ⟨b, hb⟩ := hF.exists_card_eq
  have hdvd : Nat.card N ∣ p ^ a * t ^ b := by
    rw [← ha, ← hb, ← card_sup_of_mul_comm' hpt hP hF hPF]
    exact card_subgroup_dvd_card N
  have hdvd' : Nat.card N ∣ p ^ a :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right b hcop.symm) hdvd)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd'
  have hNp : IsPGroup p N := IsPGroup.of_card hk
  have hle : N ≤ CFSG.pCore p ↥(P ⊔ F) := le_sSup ⟨hNn, hNp⟩
  rwa [hcore, le_bot_iff] at hle

omit [Finite G] hp ht in
theorem pCore_sup_eq_bot_of_le {A P T F : Subgroup G} (hP : IsMaxInvIn p A ⊤ P)
    (hAF : A ≤ normalizer (F : Set G)) (hTF : T ≤ F) (hT : CFSG.pCore p ↥(P ⊔ T) = ⊥) :
    CFSG.pCore p ↥(P ⊔ F) = ⊥ := by
  obtain ⟨R, hR⟩ : ∃ R : Subgroup G, R = (CFSG.pCore p ↥(P ⊔ F)).map (P ⊔ F).subtype :=
    ⟨_, rfl⟩
  have hRp : IsPGroup p R := by
    rw [hR]
    exact CFSG.pCore_isPGroup.map _
  have hPFR : P ⊔ F ≤ normalizer (R : Set G) := by
    rw [hR]
    exact le_normalizer.trans (normalizer_le_normalizer_pCore_map p _)
  have hAR : A ≤ normalizer (R : Set G) := by
    intro a ha
    rw [hR]
    exact normalizer_le_normalizer_pCore_map p _ (mem_normalizer_sup (hP.2.2.1 ha) (hAF ha))
  have hRP : R ≤ P := by
    have h2 : IsPGroup p (R ⊔ P : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hRp hP.2.1 (le_sup_left.trans hPFR)
    have h3 := hP.2.2.2 (R ⊔ P) le_top h2 (fun a ha => mem_normalizer_sup (hAR ha) (hP.2.2.1 ha))
      le_sup_right
    exact le_sup_left.trans h3.le
  have hRPT : R ≤ P ⊔ T := hRP.trans le_sup_left
  have hRn : (R.subgroupOf (P ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRPT).mpr ((sup_le_sup_left hTF P).trans hPFR)
  have hle : R.subgroupOf (P ⊔ T) ≤ CFSG.pCore p ↥(P ⊔ T) :=
    le_sSup ⟨hRn, hRp.comap_subtype⟩
  rw [hT, le_bot_iff] at hle
  have hR1 : R = ⊥ := by
    rw [← map_subgroupOf_eq_of_le hRPT, hle, Subgroup.map_bot]
  rwa [hR, map_eq_bot_iff_of_injective _ (P ⊔ F).subtype_injective] at hR1

omit hp in
include ht in
theorem le_normalizer_ambientMaxCardZJ_of_odd {K U : Subgroup G} (hK : Odd (Nat.card K))
    (hU : IsSylowOf t U K) (hcore : CFSG.pPrimeCore t K = ⊥) :
    K ≤ normalizer (CFSG.ambientMaxCardZJ U : Set G) := by
  have : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
  obtain ⟨S, hS⟩ := hU.exists_sylow_eq_subgroupOf
  have h62 := CFSG.theorem_6_2 hK S
  rw [hcore, sup_bot_eq, hS] at h62
  have hmap : (CFSG.ambientMaxCardZJ (U.subgroupOf K)).map K.subtype =
      CFSG.ambientMaxCardZJ U := by
    rw [CFSG.map_ambientMaxCardZJ_of_injective K.subtype _
      (K.subtype_injective.comp Subtype.val_injective), map_subgroupOf_eq_of_le hU.le]
  have : (CFSG.ambientMaxCardZJ (U.subgroupOf K)).Normal := h62
  have hN := CFSG.ABGLocalTools.le_normalizer_map_subtype K (CFSG.ambientMaxCardZJ (U.subgroupOf K))
  rwa [hmap] at hN

end Permutable

section Bar

variable {G : Type*} [Group G]

theorem mem_iff_mk_mem_bar {J R : Subgroup G} (hOR : O J ≤ R) (k : J) :
    (k : G) ∈ R ↔ QuotientGroup.mk' (CFSG.oddCore J) k ∈ bar J R := by
  refine ⟨fun hk => mem_map_of_mem _ (show k ∈ R.subgroupOf J from hk), fun hk => ?_⟩
  obtain ⟨r, hr, hrk⟩ := hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrk
  have hrk' : (r : G)⁻¹ * k ∈ O J := ⟨_, hrk, rfl⟩
  have : (k : G) = r * ((r : G)⁻¹ * k) := by group
  rw [this]
  exact R.mul_mem hr (hOR hrk')

theorem le_iff_bar_le_bar {J K R : Subgroup G} (hKJ : K ≤ J) (hOR : O J ≤ R) :
    K ≤ R ↔ bar J K ≤ bar J R := by
  refine ⟨fun h => G4c.bar_mono h, fun h k hk => ?_⟩
  exact (mem_iff_mk_mem_bar hOR ⟨k, hKJ hk⟩).mpr
    (h (mem_map_of_mem _ (show (⟨k, hKJ hk⟩ : J) ∈ K.subgroupOf J from hk)))

theorem exists_preimage (J : Subgroup G) (K : Subgroup (Bar J)) :
    ∃ R : Subgroup G, O J ≤ R ∧ R ≤ J ∧ bar J R = K := by
  refine ⟨(K.comap (QuotientGroup.mk' (CFSG.oddCore J))).map J.subtype, ?_, map_subtype_le _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.oddCore J) x ∈ K
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact K.one_mem
  · unfold bar
    rw [show ((K.comap (QuotientGroup.mk' (CFSG.oddCore J))).map J.subtype).subgroupOf J =
        K.comap (QuotientGroup.mk' (CFSG.oddCore J)) from
      comap_map_eq_self_of_injective J.subtype_injective _]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem subgroupOf_eq_comap_bar {J R : Subgroup G} (hOR : O J ≤ R) :
    R.subgroupOf J = (bar J R).comap (QuotientGroup.mk' (CFSG.oddCore J)) := by
  unfold bar
  rw [comap_map_eq, QuotientGroup.ker_mk']
  refine (sup_eq_left.mpr fun x hx => ?_).symm
  exact hOR ⟨x, hx, rfl⟩

theorem card_eq_card_bar_mul [Finite G] {J R : Subgroup G} (hOR : O J ≤ R) (hRJ : R ≤ J) :
    Nat.card R = Nat.card (bar J R) * Nat.card (O J) := by
  set π := QuotientGroup.mk' (CFSG.oddCore J) with hπ
  have hR : Nat.card R = Nat.card ((bar J R).comap π) := by
    rw [← subgroupOf_eq_comap_bar hOR]
    exact (Nat.card_congr (subgroupOfEquivOfLe hRJ).toEquiv).symm
  have h1 := card_mul_index ((bar J R).comap π)
  rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  have h2 := card_mul_index (bar J R)
  have h3 : Nat.card J = Nat.card (Bar J) * Nat.card (CFSG.oddCore J) :=
    card_eq_card_quotient_mul_card_subgroup _
  have h4 : Nat.card (O J) = Nat.card (CFSG.oddCore J) := card_map_of_injective J.subtype_injective
  have hidx : 0 < (bar J R).index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  rw [hR, h4]
  apply Nat.eq_of_mul_eq_mul_right hidx
  rw [h1, h3, ← h2]
  ring

theorem relIndex_bar_dvd {J U K : Subgroup G} (hKJ : K ≤ J) :
    (bar J U).relIndex (bar J K) ∣ U.relIndex K := by
  have h1 : (bar J U).relIndex (bar J K) =
      ((bar J U).comap (QuotientGroup.mk' (CFSG.oddCore J))).relIndex (K.subgroupOf J) := by
    rw [relIndex_comap]
    rfl
  rw [h1, ← relIndex_subgroupOf hKJ]
  exact relIndex_dvd_of_le_left _ (le_comap_map _ _)

theorem bar_eq_of_isSylowOf [Finite G] {q : ℕ} [Fact q.Prime] {J U K : Subgroup G}
    (hU : IsSylowOf q U K) (hKJ : K ≤ J) (hK : IsPGroup q (bar J K)) : bar J U = bar J K := by
  have hdvd := relIndex_bar_dvd (U := U) hKJ
  have hcop : ¬ q ∣ U.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hU).2.2
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have h2 : (bar J U).relIndex (bar J K) ∣ q ^ n := hn ▸ relIndex_dvd_card _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp h2
  have hk0 : k = 0 := by
    by_contra hk0
    exact hcop ((dvd_pow_self q hk0).trans (hk ▸ hdvd))
  rw [hk0, pow_zero, relIndex_eq_one] at hk
  exact le_antisymm (G4c.bar_mono hU.le) hk

theorem bar_mul_comm {J P F : Subgroup G} (hPJ : P ≤ J) (hFJ : F ≤ J)
    (hPF : (P : Set G) * (F : Set G) = (F : Set G) * (P : Set G)) :
    ((bar J P : Subgroup (Bar J)) : Set (Bar J)) * (bar J F : Set (Bar J)) =
      (bar J F : Set (Bar J)) * (bar J P : Set (Bar J)) := by
  have key : ∀ {X Y : Subgroup G}, X ≤ J → Y ≤ J → (X : Set G) * Y = (Y : Set G) * X →
      ((bar J X : Subgroup (Bar J)) : Set (Bar J)) * (bar J Y : Set (Bar J)) ⊆
        (bar J Y : Set (Bar J)) * (bar J X : Set (Bar J)) := by
    intro X Y hXJ hYJ hXY
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    have hxy : (x : G) * y ∈ (Y : Set G) * (X : Set G) := by
      rw [← hXY]
      exact ⟨x, hx, y, hy, rfl⟩
    obtain ⟨y', hy', x', hx', he⟩ := hxy
    refine ⟨_, ⟨⟨y', hYJ hy'⟩, hy', rfl⟩, _, ⟨⟨x', hXJ hx'⟩, hx', rfl⟩, ?_⟩
    dsimp only
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext he
  exact Set.Subset.antisymm (key hPJ hFJ hPF) (key hFJ hPJ hPF.symm)

theorem bar_le_centralizer {J X P : Subgroup G} (h : X ≤ centralizer (P : Set G)) :
    bar J X ≤ centralizer (bar J P : Set (Bar J)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp (h hx) y hy)

theorem le_normalizer_of_bar_le_normalizer [Finite G] {J A R : Subgroup G} (hAJ : A ≤ J)
    (hOR : O J ≤ R) (hRJ : R ≤ J) (h : bar J A ≤ normalizer (bar J R : Set (Bar J))) :
    A ≤ normalizer (R : Set G) := by
  intro a ha
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨g, hg, rfl⟩
  have hgJ := hRJ hg
  have hπ := (mem_normalizer_iff.mp (h (mem_map_of_mem _
    (show (⟨a, hAJ ha⟩ : J) ∈ A.subgroupOf J from ha)))
    (QuotientGroup.mk' (CFSG.oddCore J) ⟨g, hgJ⟩)).mp
    ((mem_iff_mk_mem_bar hOR ⟨g, hgJ⟩).mp hg)
  rw [← map_inv, ← map_mul, ← map_mul] at hπ
  exact (mem_iff_mk_mem_bar hOR _).mpr hπ

end Bar

section CoprimeBar

variable {G : Type*} [Group G] [Finite G]

theorem isMaxInvIn_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A P J : Subgroup G}
    (hA2 : IsPGroup 2 A) (hAJ : A ≤ J) (hPJ : P ≤ J) (hP : IsMaxInvIn p A ⊤ P) :
    IsMaxInvIn p (bar J A) ⊤ (bar J P) := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨le_top, G4c.isPGroup_bar hP.2.1, G4c.bar_le_normalizer hP.2.2.1, ?_⟩
  intro R' _ hR' hAR' hPR'
  obtain ⟨R, hOR, hRJ, hRbar⟩ := exists_preimage J R'
  subst hRbar
  have hPR : P ≤ R := (le_iff_bar_le_bar hPJ hOR).mpr hPR'
  have hAR : A ≤ normalizer (R : Set G) := le_normalizer_of_bar_le_normalizer hAJ hOR hRJ hAR'
  have hRodd : Odd (Nat.card R) := by
    rw [card_eq_card_bar_mul hOR hRJ]
    obtain ⟨n, hn⟩ := hR'.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow.mul (card_O_odd J)
  have hsyl := isSylowOf_inf_O_of_isMaxInvIn hp hA2 hAR (IsMaxInvIn.of_le hP hPR le_top)
  rw [O_eq_self_of_odd hRodd, inf_eq_left.mpr hPR] at hsyl
  exact (bar_eq_of_isSylowOf hsyl hRJ hR').symm

theorem isSylowOf_bar_centralizer {A J : Subgroup G} (hA2 : IsPGroup 2 A) (hAJ : A ≤ J)
    (hsyl : IsSylowOf 2 A (centralizer (A : Set G))) :
    IsSylowOf 2 (bar J A) (centralizer (bar J A : Set (Bar J))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAc : A ≤ centralizer (A : Set G) := hsyl.le
  have hĀ2 : IsPGroup 2 (bar J A) := G4c.isPGroup_bar hA2
  have hĀc : bar J A ≤ centralizer (bar J A : Set (Bar J)) := bar_le_centralizer hAc
  obtain ⟨S₀, hS₀⟩ := (hĀ2.comap_subtype (K := centralizer (bar J A : Set (Bar J)))).exists_le_sylow
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (Bar J), S =
      (S₀ : Subgroup (centralizer (bar J A : Set (Bar J)))).map (centralizer _).subtype :=
    ⟨_, rfl⟩
  have hSsyl : IsSylowOf 2 S (centralizer (bar J A : Set (Bar J))) := ⟨S₀, hS.symm⟩
  have hĀS : bar J A ≤ S := by
    rw [hS]
    exact fun x hx => ⟨⟨x, hĀc hx⟩, hS₀ hx, rfl⟩
  obtain ⟨B₁, hOB, hBJ, hBbar⟩ := exists_preimage J S
  have hAB₁ : A ≤ B₁ := (le_iff_bar_le_bar hAJ hOB).mpr (hBbar ▸ hĀS)
  obtain ⟨B₀, hB₀⟩ := (hA2.comap_subtype (K := B₁)).exists_le_sylow
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = (B₀ : Subgroup B₁).map B₁.subtype := ⟨_, rfl⟩
  have hBsyl : IsSylowOf 2 B B₁ := ⟨B₀, hB.symm⟩
  have hAB : A ≤ B := by
    rw [hB]
    exact fun a ha => ⟨⟨a, hAB₁ ha⟩, hB₀ ha, rfl⟩
  have hBA : B ≤ centralizer (A : Set G) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro a ha
    have hbJ : b ∈ J := hBJ (hBsyl.le hb)
    have haJ : a ∈ J := hAJ ha
    have hc1 : b * a * b⁻¹ * a⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem hb (hAB ha)) (B.inv_mem hb)) (B.inv_mem (hAB ha))
    have hc2 : b * a * b⁻¹ * a⁻¹ ∈ O J := by
      have hbS : QuotientGroup.mk' (CFSG.oddCore J) ⟨b, hbJ⟩ ∈ S := by
        rw [← hBbar]
        exact mem_map_of_mem _ (show (⟨b, hbJ⟩ : J) ∈ B₁.subgroupOf J from hBsyl.le hb)
      have haA : QuotientGroup.mk' (CFSG.oddCore J) ⟨a, haJ⟩ ∈ bar J A :=
        mem_map_of_mem _ (show (⟨a, haJ⟩ : J) ∈ A.subgroupOf J from ha)
      have hcomm := mem_centralizer_iff.mp (hSsyl.le hbS) _ haA
      have h1 : QuotientGroup.mk' (CFSG.oddCore J)
          ((⟨b, hbJ⟩ : J) * ⟨a, haJ⟩ * (⟨b, hbJ⟩ : J)⁻¹ * (⟨a, haJ⟩ : J)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    have hbot : O J ⊓ B = ⊥ :=
      G4c.inf_eq_bot_of_odd_of_isPGroup (card_O_odd J) hBsyl.isPGroup
    have h1 : b * a * b⁻¹ * a⁻¹ ∈ O J ⊓ B := ⟨hc2, hc1⟩
    rw [hbot, mem_bot] at h1
    calc a * b = (b * a * b⁻¹ * a⁻¹)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, inv_one, one_mul]
  have hBA' : B = A := hsyl.eq_of_le hAB hBA hBsyl.isPGroup
  have hSeq : S = bar J A := by
    rw [← hBbar, ← bar_eq_of_isSylowOf hBsyl hBJ (hBbar ▸ hSsyl.isPGroup), hBA']
  rw [hSeq] at hSsyl
  exact hSsyl

end CoprimeBar

section Hall

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_mul_comm {p t : ℕ} [hp : Fact p.Prime] [ht : Fact t.Prime] (hpt : p ≠ t)
    {A K P F : Subgroup G} (hA2 : IsPGroup 2 A) (hAK : A ≤ normalizer (K : Set G))
    (hK : Odd (Nat.card K)) (hP : IsMaxInvIn p A ⊤ P) (hPK : P ≤ K) (hF : IsPGroup t F)
    (hFK : F ≤ K) (hAF : A ≤ normalizer (F : Set G))
    (hPF : (P : Set G) * (F : Set G) = (F : Set G) * (P : Set G)) :
    ∃ F' : Subgroup G, F ≤ F' ∧ IsSylowOf t F' K ∧ A ≤ normalizer (F' : Set G) ∧
      (P : Set G) * (F' : Set G) = (F' : Set G) * (P : Set G) := by
  set π : Set Nat.Primes := {⟨p, hp.out⟩, ⟨t, ht.out⟩} with hπ
  have hmemπ : ∀ q : Nat.Primes, (q : ℕ) = p ∨ (q : ℕ) = t → q ∈ π := by
    rintro q (hq | hq)
    · exact Or.inl (Subtype.ext hq)
    · exact Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext hq))
  have hPFπ : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card (P ⊔ F : Subgroup G) → q ∈ π := by
    intro q hq
    rw [card_sup_of_mul_comm' hpt hP.2.1 hF hPF] at hq
    obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
    obtain ⟨b, hb⟩ := hF.exists_card_eq
    rw [ha, hb] at hq
    refine hmemπ q ?_
    rcases (Nat.Prime.dvd_mul q.2).mp hq with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.2 hp.out).mp (q.2.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.2 ht.out).mp (q.2.dvd_of_dvd_pow h))
  obtain ⟨H, hHK, hPFH, hAH, hHπ, hHidx⟩ := CFSG.ABGTheoremB.V4.exists_invariant_hall hA2 hAK hK
    (sup_le hPK hFK) (fun a ha => mem_normalizer_sup (hP.2.2.1 ha) (hAF ha)) π hPFπ
  have hHodd : Odd (Nat.card H) := G4c.odd_card_of_le hHK hK
  have hOH : O H = H := O_eq_self_of_odd hHodd
  obtain ⟨F', hF'max, hFF'⟩ := exists_isMaxInvIn_ge (A := A) (H := H)
    (le_sup_right.trans hPFH) hF hAF
  have hF'H : IsSylowOf t F' H := by
    have h := isSylowOf_inf_O_of_isMaxInvIn ht.out hA2 hAH hF'max
    rwa [hOH, inf_eq_left.mpr hF'max.1] at h
  have hPH : IsSylowOf p P H := by
    have h := isSylowOf_inf_O_of_isMaxInvIn hp.out hA2 hAH
      (IsMaxInvIn.of_le hP (le_sup_left.trans hPFH) le_top)
    rwa [hOH, inf_eq_left.mpr (le_sup_left.trans hPFH)] at h
  have hF'K : IsSylowOf t F' K := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hF'max.1.trans hHK, hF'max.2.1, fun hdvd => ?_⟩
    rw [← relIndex_mul_relIndex F' H K hF'max.1 hHK] at hdvd
    rcases (Nat.Prime.dvd_mul ht.out).mp hdvd with h | h
    · exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hF'H).2.2 h
    · exact hHidx ⟨t, ht.out⟩ (Or.inr rfl) h
  have hHprimes : ∀ d : ℕ, d.Prime → d ∣ Nat.card H → d = p ∨ d = t := by
    intro q hq hqH
    rcases hHπ ⟨q, hq⟩ hqH with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val (Set.mem_singleton_iff.mp h))
  obtain ⟨h1, h2⟩ := CFSG.ABGTheoremB.V4.coe_eq_mul_of_isSylowOf hpt hPH hF'H hHprimes
  exact ⟨F', hFF', hF'K, hF'max.2.2.1, h1.symm.trans h2⟩

end Hall

end G5d

end CFSG.GH72
