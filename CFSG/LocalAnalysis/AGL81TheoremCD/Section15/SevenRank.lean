module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526LN
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KHupGeFive
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
import CFSG.RankThree.OddKernel.RankOneQuotients

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.RankThreeUC.S15.KFactsPair
open Subgroup
open scoped Pointwise

theorem pRank_comap_toStar_le {X : Type} [Group X] [Finite X] {T : Subgroup X} {p : ℕ}
    (hp : p.Prime) (Ys : Subgroup (X ⧸ gnC T)) :
    CFSG.Open.pRank p (Ys.comap (toStar T)) ≤
      CFSG.Open.pRank p (gnC T) + CFSG.Open.pRank p Ys := by
  set Z : Subgroup X := Ys.comap (toStar T) with hZ
  have hC : gnC T ≤ Z := by
    intro x hx
    refine Subgroup.mem_comap.mpr ?_
    rw [show toStar T x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact Ys.one_mem
  let C0 : Subgroup ↥Z := (gnC T).subgroupOf Z
  haveI : C0.Normal := (inferInstance : (gnC T).Normal).subgroupOf Z
  let φ : ↥Z →* ↥Ys :=
    ((toStar T).comp Z.subtype).codRestrict Ys (fun x => x.2)
  have hker : φ.ker = C0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (gnC T) y
    exact ⟨⟨x, hy⟩, Subtype.ext rfl⟩
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (↥Z ⧸ C0)) = CFSG.Open.pRank p Ys := by
    let e : (↥Z ⧸ C0) ≃* ↥Ys :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivRange φ).trans
          ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv))
    calc CFSG.Open.pRank p (⊤ : Subgroup (↥Z ⧸ C0))
        = CFSG.Open.pRank p (⊤ : Subgroup ↥Ys) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
      _ = CFSG.Open.pRank p Ys :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ys).symm
  have hC0rank : CFSG.Open.pRank p C0 = CFSG.Open.pRank p (gnC T) := by
    calc CFSG.Open.pRank p C0
        = CFSG.Open.pRank p (⊤ : Subgroup ↥C0) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup C0
      _ = CFSG.Open.pRank p (⊤ : Subgroup ↥(gnC T)) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
            (Subgroup.subgroupOfEquivOfLe hC)
      _ = CFSG.Open.pRank p (gnC T) :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (gnC T)).symm
  have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_add_pRank_map (G := ↥Z) (p := p) hp C0
    (⊤ : Subgroup ↥Z)
  rw [top_inf_eq, Subgroup.map_top] at h
  have hrangeC : (QuotientGroup.mk' C0).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C0)
  rw [hrangeC, hC0rank, hquot] at h
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Z]
  exact h

theorem pRank_quotient_Y0_le_two {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hfac : GNFactor T T₁ T₂) (hY : (Y0 T T₁ T₂).Normal) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h₁ : CFSG.Open.pRank p (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank p (Subgroup.normalizer (T₂ : Set X)) ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ Y0 T T₁ T₂)) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Y0 T T₁ T₂).Normal := hY
  let Q := X ⧸ Y0 T T₁ T₂
  let π : X →* Q := QuotientGroup.mk' (Y0 T T₁ T₂)
  let A : Subgroup X := Subgroup.centralizer (T₁ : Set X)
  let B : Subgroup X := Subgroup.normalizer (T₂ : Set X)
  let Abar : Subgroup Q := A.map π
  let Bbar : Subgroup Q := B.map π
  have hA : CFSG.Open.pRank p A ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt
      (Subgroup.centralizer_le_normalizer (T₁ : Set X))).trans h₁
  have hB : CFSG.Open.pRank p B ≤ 1 := h₂
  have rank_image_le_one {C : Subgroup X} (hC : CFSG.Open.pRank p C ≤ 1) :
      CFSG.Open.pRank p (C.map π) ≤ 1 := by
    have hCt : CFSG.pRank p ↥C ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact hC
    let ψ : ↥C →* ↥(C.map π) := (π.domRestrict C).codRestrict (C.map π)
      (fun x => Subgroup.mem_map_of_mem π x.2)
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
    have h := CFSG.RankThree.OddKernel.pRank_le_one_of_surjective hp hp2 ψ hψ hCt
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
    exact h
  have hArank : CFSG.Open.pRank p Abar ≤ 1 := rank_image_le_one hA
  have hBrank : CFSG.Open.pRank p Bbar ≤ 1 := rank_image_le_one hB
  have hAB : ∀ x : Q, ∃ a ∈ Abar, ∃ b ∈ Bbar, x = a * b := by
    intro x
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (Y0 T T₁ T₂) x
    obtain ⟨a, ha, y, hy, b, hb, rfl⟩ := hfac x₀
    refine ⟨π a, Subgroup.mem_map_of_mem π ha, π b, Subgroup.mem_map_of_mem π hb, ?_⟩
    have hy1 : π y = 1 := (QuotientGroup.eq_one_iff _).mpr hy
    calc π (a * y * b) = π a * π y * π b := by rw [map_mul, map_mul]
      _ = π a * π b := by rw [hy1, mul_one]
  obtain ⟨P₁, P₂, hP₁, hP₂, ⟨R, hR⟩, hset⟩ := kWiel_holds Q Abar Bbar p hp hAB
  have hr₁ : CFSG.Open.pRank p P₁ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hP₁.le).trans hArank
  have hr₂ : CFSG.Open.pRank p P₂ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hP₂.le).trans hBrank
  have hc₁ := exists_yComponent_dvd_aux_isCyclic hp hp2 hP₁.isPGroup hr₁
  have hc₂ := exists_yComponent_dvd_aux_isCyclic hp hp2 hP₂.isPGroup hr₂
  have hRpg : IsPGroup p (P₁ ⊔ P₂ : Subgroup Q) := by
    rw [← hR]
    exact R.isPGroup'
  have hprod : ∀ w ∈ (P₁ ⊔ P₂ : Subgroup Q), ∃ a ∈ P₁, ∃ b ∈ P₂, w = a * b := by
    intro w hw
    have hw' : w ∈ (P₁ : Set Q) * (P₂ : Set Q) := by
      rw [← hset]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw'
    exact ⟨a, ha, b, hb, rfl⟩
  have h2 := kHupAt_odd hp hp2 Q (P₁ ⊔ P₂) P₁ P₂ hRpg le_sup_left le_sup_right
    hc₁ hc₂ hprod
  rw [← hR, exists_yComponent_dvd_aux_pRank_sylow] at h2
  exact h2

theorem pRank_le_pRank_Y0_add_two {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hfac : GNFactor T T₁ T₂)
    (hY : (Y0 T T₁ T₂).Normal) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h₁ : CFSG.Open.pRank p (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank p (Subgroup.normalizer (T₂ : Set X)) ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤
      CFSG.Open.pRank p (Y0 T T₁ T₂) + 2 := by
  haveI : (Y0 T T₁ T₂).Normal := hY
  have hq := pRank_quotient_Y0_le_two hfac hY hp hp2 h₁ h₂
  have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_add_pRank_map (p := p) hp
    (Y0 T T₁ T₂) (⊤ : Subgroup X)
  rw [top_inf_eq, Subgroup.map_top] at h
  have hrange : (QuotientGroup.mk' (Y0 T T₁ T₂)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  rw [hrange] at h
  omega

theorem pRank_seven_le_one_of_isLThreeOfExp_one {S : Type} [Group S] [Finite S]
    (h : IsLThreeOfExp 1 S) :
    CFSG.Open.pRank 7 (⊤ : Subgroup S) ≤ 1 := by
  have h168 : Nat.card S = 168 := hLN_aux_card_eq h
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E _ hE
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hdvd : 7 ^ k ∣ Nat.card S := hk ▸ Subgroup.card_subgroup_dvd_card E
  rw [h168] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have h49 : 7 ^ 2 ∣ 7 ^ k := Nat.pow_dvd_pow 7 (by omega : 2 ≤ k)
    exact (by norm_num : ¬ 7 ^ 2 ∣ 168) (h49.trans hdvd)
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk1

theorem ystar_normal_of_row1527 {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (h7 : 7 ∈ sigmaSet G M)
    (h27 : Row1527 G M T T₁ T₂) :
    (Ystar (T.subgroupOf M) T₁ T₂).Normal := by
  have hS : IsSimpleGroup ↥(Ystar (T.subgroupOf M) T₁ T₂) := hLN_aux_isSimpleGroup h27
  have hne : Ystar (T.subgroupOf M) T₁ T₂ ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(Ystar (T.subgroupOf M) T₁ T₂) = 1 := by
      rw [hbot]
      simp
    have h168 := hLN_aux_card_eq h27
    omega
  have hex : ∃ Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M)),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls := by
    by_contra h
    push Not at h
    apply hne
    simp [Ystar, h]
  obtain ⟨Ls, hLs⟩ := hex
  have hLsY : Ls = Ystar (T.subgroupOf M) T₁ T₂ := hLN_aux_eq_ystar_of_simple hS hLs
  have huniq : ∀ Is, GNYComponent (T.subgroupOf M) T₁ T₂ Is → Is = Ls := fun Is hIs =>
    (hLN_aux_eq_ystar_of_simple hS hIs).trans hLsY.symm
  have hconj : ∀ g : ↥M ⧸ gnC (T.subgroupOf M),
      ¬ 7 ∣ Nat.card (Subgroup.center ↥(Ls.map (MulAut.conj g).toMonoidHom)) ∧
        7 ∣ Nat.card ↥(Ls.map (MulAut.conj g).toMonoidHom) := by
    intro g
    have h3 : IsLThreeOfExp 1 ↥Ls := by
      rw [hLsY]
      exact h27
    have e : ↥Ls ≃* ↥(Ls.map (MulAut.conj g).toMonoidHom) :=
      Ls.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    obtain ⟨hd, hz⟩ := dvd_and_center_of_isLThreeOfExp_one (isLThreeOfExp_one_of_mulEquiv e h3)
    refine ⟨?_, hd⟩
    rw [hz]
    norm_num
  have hn := ystar_normal ctx.gn ctx.pair (q := 7) (by norm_num) (by norm_num)
    (ctx.rank_N₁ 7 h7) (ctx.rank_N₂ 7 h7) hLs huniq hconj
  rwa [hLsY] at hn

theorem pRank_seven_le_four_of_row1527 {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (h7 : 7 ∈ sigmaSet G M)
    (h27 : Row1527 G M T T₁ T₂) :
    CFSG.Open.pRank 7 (⊤ : Subgroup ↥M) ≤ 4 := by
  have hY : (Y0 (T.subgroupOf M) T₁ T₂).Normal :=
    (ystar_normal_of_row1527 ctx h7 h27).comap (toStar (T.subgroupOf M))
  have hY0 : CFSG.Open.pRank 7 (Y0 (T.subgroupOf M) T₁ T₂) ≤ 2 := by
    change CFSG.Open.pRank 7 ((Ystar (T.subgroupOf M) T₁ T₂).comap
      (toStar (T.subgroupOf M))) ≤ 2
    have h1 := pRank_comap_toStar_le (X := ↥M) (T := T.subgroupOf M) (p := 7) Nat.prime_seven
      (Ystar (T.subgroupOf M) T₁ T₂)
    have hC : CFSG.Open.pRank 7 (gnC (T.subgroupOf M)) ≤ 1 := ctx.rank_C 7 h7
    have hYs : CFSG.Open.pRank 7 (Ystar (T.subgroupOf M) T₁ T₂) ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact pRank_seven_le_one_of_isLThreeOfExp_one h27
    omega
  have h := pRank_le_pRank_Y0_add_two ctx.factor hY Nat.prime_seven (by norm_num)
    (ctx.rank_N₁ 7 h7) (ctx.rank_N₂ 7 h7)
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
