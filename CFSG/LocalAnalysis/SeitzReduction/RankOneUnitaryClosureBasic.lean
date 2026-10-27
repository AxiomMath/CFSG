module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXStrictRankStrongClosure
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace StrongClosureMod

variable {G : Type*} [Group G]

theorem exists_pow_not_mem {R S : Subgroup G} (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S)
    (hxR : x ∉ R) : ∃ j : ℕ, x ^ 2 ^ j ∉ R ∧ (x ^ 2 ^ j) ^ 2 ∈ R := by
  classical
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hex : ∃ k : ℕ, x ^ 2 ^ k ∈ R := ⟨k, hk' ▸ one_mem R⟩
  have hk₀ : x ^ 2 ^ Nat.find hex ∈ R := Nat.find_spec hex
  have hk₀0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk₀
    exact hxR hk₀
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk₀0)]
  exact hk₀

variable {A : Subgroup G}

theorem mem_map_mk_iff {H : Subgroup G} (hAH : A ≤ H) (x : normalizer (A : Set G)) :
    QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))) x ∈
        (H.subgroupOf (normalizer (A : Set G))).map
          (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G)))) ↔ (x : G) ∈ H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : y⁻¹ * x ∈ A.subgroupOf (normalizer (A : Set G)) := QuotientGroup.eq.mp hyx
    have hy' : (y : G) ∈ H := mem_subgroupOf.mp hy
    rw [mem_subgroupOf] at h1
    have h2 : ((y : G) * ((y⁻¹ * x : normalizer (A : Set G)) : G)) ∈ H :=
      mul_mem hy' (hAH h1)
    simpa using h2
  · intro hx
    exact ⟨x, mem_subgroupOf.mpr hx, rfl⟩

theorem card_map_mk {H : Subgroup G} (hHN : H ≤ normalizer (A : Set G)) :
    Nat.card ((H.subgroupOf (normalizer (A : Set G))).map
        (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))) = A.relIndex H := by
  rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hHN]

theorem relIndex_mul_card_of_le {H : Subgroup G} (hAH : A ≤ H) :
    A.relIndex H * Nat.card A = Nat.card H := by
  have := relIndex_mul_card A H
  rwa [inf_of_le_left hAH] at this

end StrongClosureMod

theorem pRank_le_one_of_unique_involution {Q : Type*} [Group Q] [Finite Q] (u : Q)
    (hu : ∀ q : Q, q ≠ 1 → q ^ 2 = 1 → q = u) : CFSG.pRank 2 Q ≤ 1 := by
  classical
  refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun B hB => ?_
  have := hB
  have hsub : (B : Set Q) ⊆ {1, u} := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · exact Or.inr (hu b hb1 (CFSG.elemPow_eq_one_of_isElementaryAbelian (A := B) b hb))
  calc Nat.card B = (B : Set Q).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, u} : Set Q).ncard := Set.ncard_le_ncard hsub
    _ ≤ 2 ^ 1 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]; norm_num)

open StrongClosureMod in
theorem strongClosed_mod_of_rank {G : Type*} [Group G] [Finite G] {A R S C : Subgroup G} {v : G}
    {a c : ℕ} (hAR : A ≤ R) (hRS : R ≤ S) (hSN : S ≤ normalizer (A : Set G))
    (hSR : S ≤ normalizer (R : Set G)) (hS : IsPGroup 2 S) (hsq : ∀ r ∈ R, r ^ 2 ∈ A)
    (hcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ A) (hcard : Nat.card R = 2 ^ a * Nat.card A)
    (hvS : v ∈ S) (huniq : ∀ x ∈ S, x ∉ R → x ^ 2 ∈ R → v⁻¹ * x ∈ R) (hAC : A ≤ C) (hCR : C ≤ R)
    (hCcard : Nat.card C ≤ 2 ^ c * Nat.card A)
    (hCv : ∀ e ∈ R, e * v * e⁻¹ * v⁻¹ ∈ A → e ∈ C) (hca : c + 1 < a)
    (hsyl : ∃ P : Sylow 2 (normalizer (A : Set G)),
      (P : Subgroup (normalizer (A : Set G))) = S.subgroupOf (normalizer (A : Set G))) :
    ∀ g ∈ normalizer (A : Set G), ∀ r ∈ R, g⁻¹ * r * g ∈ S → g⁻¹ * r * g ∈ R := by
  classical
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (A : Set G) with hXdef
  set N := A.subgroupOf X with hNdef
  set π := QuotientGroup.mk' N with hπdef
  set Sb := (S.subgroupOf X).map π with hSb
  set Rb := (R.subgroupOf X).map π with hRb
  set Cb := (C.subgroupOf X).map π with hCb
  have hRN : R ≤ X := hRS.trans hSN
  have hCN : C ≤ X := hCR.trans hRN
  have hAS : A ≤ S := hAR.trans hRS
  have memS : ∀ x : X, π x ∈ Sb ↔ (x : G) ∈ S := mem_map_mk_iff hAS
  have memR : ∀ x : X, π x ∈ Rb ↔ (x : G) ∈ R := mem_map_mk_iff hAR
  have memC : ∀ x : X, π x ∈ Cb ↔ (x : G) ∈ C := mem_map_mk_iff hAC
  have hone : ∀ x : X, π x = 1 ↔ (x : G) ∈ A := fun x =>
    (QuotientGroup.eq_one_iff x).trans mem_subgroupOf
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hRbcomm : ∀ u ∈ Rb, ∀ w ∈ Rb, u * w = w * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    replace hx : (x : G) ∈ R := mem_subgroupOf.mp hx
    replace hy : (y : G) ∈ R := mem_subgroupOf.mp hy
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)
    have h1 := hcomm _ (inv_mem hy) _ (inv_mem hx)
    have e : (((x * y)⁻¹ * (y * x) : X) : G) =
        (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹⁻¹ * (x : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact h1
  have hRbsq : ∀ u ∈ Rb, u ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hone]
    simpa using hsq _ (mem_subgroupOf.mp hx)
  have hRbel : IsElementaryAbelian 2 Rb :=
    { toIsMulCommutative := ⟨⟨fun u w => Subtype.ext (hRbcomm _ u.2 _ w.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hRbsq _ u.2) }
  have hRbo : CFSG.Open.IsElemAbelian 2 Rb :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 Rb).mp hRbel
  have hRbcard : Nat.card Rb = 2 ^ a := by
    rw [hRb, card_map_mk hRN]
    have h1 := relIndex_mul_card_of_le hAR
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hApos h1
  have hRbrank : CFSG.pRank 2 Rb = a :=
    CFSG.LocalAnalysis.GorensteinLyons.pRank_eq_of_elementary one_lt_two hRbo hRbcard
  have hCbcard : Nat.card Cb ≤ 2 ^ c := by
    rw [hCb, card_map_mk hCN]
    have h1 := relIndex_mul_card_of_le hAC
    have h2 : A.relIndex C * Nat.card A ≤ 2 ^ c * Nat.card A := h1 ▸ hCcard
    exact Nat.le_of_mul_le_mul_right h2 hApos
  have hSb2 : IsPGroup 2 Sb := (hS.of_equiv (subgroupOfEquivOfLe hSN).symm).map π
  have hRbSb : Rb ≤ Sb :=
    map_mono fun x hx => mem_subgroupOf.mpr (hRS (mem_subgroupOf.mp hx))
  have hSbN : Sb ≤ normalizer (Rb : Set (X ⧸ N)) := by
    refine le_trans (map_mono fun s hs => ?_) (le_normalizer_map π)
    refine mem_normalizer_iff.mpr fun y => ?_
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp (hSR (mem_subgroupOf.mp hs)) y
  have hRbn : (Rb.subgroupOf Sb).Normal := (normal_subgroupOf_iff_le_normalizer hRbSb).mpr hSbN
  have hvX : v ∈ X := hSN hvS
  set vb : Sb := ⟨π ⟨v, hvX⟩, (memS _).mpr hvS⟩ with hvb
  have hQuniq : ∀ q : Sb ⧸ Rb.subgroupOf Sb, q ≠ 1 → q ^ 2 = 1 →
      q = (QuotientGroup.mk vb : Sb ⧸ Rb.subgroupOf Sb) := by
    intro q hq1 hq2
    obtain ⟨⟨_, ⟨x, hx, rfl⟩⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hxS : (x : G) ∈ S := mem_subgroupOf.mp hx
    have hxR : (x : G) ∉ R := by
      intro hxR
      apply hq1
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact (memR x).mpr hxR
    have hx2 : (x : G) ^ 2 ∈ R := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow,
        ← map_pow] at hq2
      simpa using (memR _).mp hq2
    have h1 := huniq _ hxS hxR hx2
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)
    show (π ⟨x, _⟩)⁻¹ * π ⟨v, hvX⟩ ∈ Rb
    rw [← map_inv, ← map_mul, memR]
    have h2 := inv_mem h1
    simpa using h2
  have hQrank : CFSG.pRank 2 (Sb ⧸ Rb.subgroupOf Sb) ≤ 1 :=
    pRank_le_one_of_unique_involution _ hQuniq
  have hcent : ∀ xb ∈ Sb, xb ∉ Rb → Rb ⊓ centralizer {xb} ≤ Cb := by
    rintro _ ⟨x, hx, rfl⟩ hxR' eb heb
    obtain ⟨heb1, heb2⟩ := mem_inf.mp heb
    obtain ⟨e, he, rfl⟩ := heb1
    have hxS : (x : G) ∈ S := mem_subgroupOf.mp hx
    have hxR : (x : G) ∉ R := fun h1 => hxR' ((memR x).mpr h1)
    obtain ⟨j, hj1, hj2⟩ := exists_pow_not_mem hS hxS hxR
    have hr : v⁻¹ * (x : G) ^ 2 ^ j ∈ R := huniq _ (pow_mem hxS _) hj1 hj2
    set w : X := ⟨v, hvX⟩ with hw
    set r : X := w⁻¹ * x ^ 2 ^ j with hrdef
    have hrR : π r ∈ Rb := (memR r).mpr (by simpa [hrdef, hw] using hr)
    have hxw : π x ^ 2 ^ j = π w * π r := by
      rw [← map_pow, ← map_mul, hrdef, mul_inv_cancel_left]
    have hc1 : π e * π x = π x * π e := mem_centralizer_singleton_iff.mp heb2
    have hc2 : π e * π x ^ 2 ^ j = π x ^ 2 ^ j * π e := ((Commute.pow_right hc1 _).eq)
    have hc3 : π e * π r = π r * π e := hRbcomm _ ((memR e).mpr (mem_subgroupOf.mp he)) _ hrR
    have hc4 : π e * π w = π w * π e := by
      rw [hxw] at hc2
      have h5 : π e * π w * π r = π w * π e * π r := by
        calc π e * π w * π r = π e * (π w * π r) := by group
          _ = π w * π r * π e := hc2
          _ = π w * (π r * π e) := by group
          _ = π w * (π e * π r) := by rw [hc3]
          _ = π w * π e * π r := by group
      exact mul_right_cancel h5
    rw [memC]
    refine hCv _ (mem_subgroupOf.mp he) ?_
    have h6 : π (e * w * e⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc4]
      group
    simpa [hw] using (hone _).mp h6
  have hCrank : ∀ xb ∈ Sb, xb ∉ Rb → CFSG.pRank 2 ↥(Rb ⊓ centralizer {xb}) ≤ c :=
    fun xb hxb hxbR => CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun B _ =>
      ((Subgroup.card_le_card_group B).trans (card_le_of_le (hcent xb hxb hxbR))).trans
        hCbcard
  have hcrit := CFSG.LocalAnalysis.GorensteinLyons.elementary_strict_rank_strong_closure_criterion
    hSb2 hRbSb hRbel fun xb hxb hxbR => by
      have h1 := hCrank xb hxb hxbR
      rw [hRbrank]
      omega
  obtain ⟨P, hP⟩ := hsyl
  have hsc := hcrit.2.2 ⟨P.mapSurjective (QuotientGroup.mk'_surjective N),
    by rw [Sylow.coe_mapSurjective, hP]⟩
  intro g hg r hr hgr
  have hrX : r ∈ X := hRN hr
  have hgS' : (π ⟨g, hg⟩)⁻¹ * π ⟨r, hrX⟩ * π ⟨g, hg⟩ ∈ Sb := by
    rw [← map_inv, ← map_mul, ← map_mul, memS]
    simpa using hgr
  have key : (π ⟨g, hg⟩)⁻¹ * π ⟨r, hrX⟩ * π ⟨g, hg⟩ ∈ Rb :=
    hsc.2 (π ⟨r, hrX⟩) ((memR _).mpr hr) (π ⟨g, hg⟩) hgS'
  rw [← map_inv, ← map_mul, ← map_mul, memR] at key
  simpa using key

end CFSG.SeitzReduction.RankOne
