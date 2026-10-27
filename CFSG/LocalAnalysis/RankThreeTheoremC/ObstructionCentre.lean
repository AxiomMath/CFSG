module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.mem_center_of_mem_centralizer {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ¬ IsMulCommutative D) {a : G} (haP : a ∈ (P : Subgroup G))
    (haC : a ∈ centralizer (D : Set G)) (hap : a ^ p = 1) : a ∈ (center D).map D.subtype := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hpow := (hext.pow_eq_one_and_commutator_mem hp hp2).1
  set Z : Subgroup G := (center D).map D.subtype with hZ
  have hZD : Z ≤ D := map_subtype_le _
  have hZc : Nat.card Z = p := hext.card_center_eq hp hp2 hD
  have hZcomm : ∀ z ∈ Z, ∀ d ∈ D, d * z = z * d := fun z hz d hd =>
    mul_comm_of_mem_center_map hz hd
  have hZe : CFSG.IsElementaryAbelian p Z :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Z).2
      ⟨⟨⟨fun a b => Subtype.ext (hZcomm b b.2 a (hZD a.2))⟩⟩, fun z hz => hpow z (hZD hz)⟩
  by_contra haZ
  obtain ⟨x, hxD, hxZ⟩ : ∃ x ∈ D, x ∉ Z := by
    by_contra h
    push Not at h
    exact hD ⟨⟨fun a b => Subtype.ext (hZcomm _ (h b b.2) a a.2)⟩⟩
  have hxp : x ^ p = 1 := hpow x hxD
  have hZx : ∀ z ∈ Z, z * x = x * z := fun z hz => (hZcomm z hz x hxD).symm
  have hEc : Nat.card ↥(Z ⊔ zpowers x) = p ^ 2 := by
    rw [card_sup_zpowers hp Z hxp hxZ hZx, hZc, pow_two]
  have hED : Z ⊔ zpowers x ≤ D := sup_le hZD (zpowers_le.mpr hxD)
  have hxe : CFSG.IsElementaryAbelian p (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hEe : CFSG.IsElementaryAbelian p ↥(Z ⊔ zpowers x) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr (mem_centralizer_iff.mpr hZx))
  have haE : a ∉ Z ⊔ zpowers x := by
    intro haE
    exact haZ ⟨⟨a, hED haE⟩, mem_center_iff.mpr fun g =>
      Subtype.ext (mem_centralizer_iff.mp haC g g.2), rfl⟩
  have hEa : ∀ e ∈ Z ⊔ zpowers x, e * a = a * e := fun e he =>
    mem_centralizer_iff.mp haC e (hED he)
  have hcard : Nat.card ↥((Z ⊔ zpowers x) ⊔ zpowers a) = p ^ 3 := by
    rw [card_sup_zpowers hp _ hap haE hEa, hEc, ← pow_succ]
  have hae : CFSG.IsElementaryAbelian p (zpowers a) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hap
  have hF : CFSG.IsElementaryAbelian p ↥((Z ⊔ zpowers x) ⊔ zpowers a) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun e he => hEa e he))
  have hFle : (Z ⊔ zpowers x) ⊔ zpowers a ≤
      D ⊔ ((P : Subgroup G) ⊓ centralizer (D : Set G)) :=
    sup_le (hED.trans le_sup_left) (zpowers_le.mpr (mem_sup_right ⟨haP, haC⟩))
  have h3 : 3 ≤ CFSG.Open.pRank p (D ⊔ ((P : Subgroup G) ⊓ centralizer (D : Set G))) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨_, hFle,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hF, hcard⟩
  have := hext.product_rank_eq
  omega

theorem ExtremalObstruction.mem_center_of_mem_centralizer_sylow {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ¬ IsMulCommutative D) {w : G} (hwP : w ∈ (P : Subgroup G))
    (hwc : w ∈ centralizer ((P : Subgroup G) : Set G)) (hwp : w ^ p = 1) :
    w ∈ (center D).map D.subtype :=
  hext.mem_center_of_mem_centralizer hp hp2 hD hwP
    (centralizer_le hext.obstruction.2.1 hwc) hwp

theorem ExtremalObstruction.center_le_centralizer {p : ℕ} {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ¬ IsMulCommutative D) :
    (center D).map D.subtype ≤ centralizer ((P : Subgroup G) : Set G) := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hDP : D ≤ P := hext.obstruction.2.1
  have hZc : Nat.card ((center D).map D.subtype) = p := hext.card_center_eq hp hp2 hD
  have hPnt : Nontrivial (P : Subgroup G) := by
    have h1 : 1 < Nat.card ((center D).map D.subtype) := hZc ▸ hp.one_lt
    have h2 : Nat.card ((center D).map D.subtype) ≤ Nat.card (P : Subgroup G) :=
      card_le_of_le ((map_subtype_le _).trans hDP)
    exact Finite.one_lt_card_iff_nontrivial.mp (h1.trans_le h2)
  have hZnt : Nontrivial (center (P : Subgroup G)) := hPp.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := (hPp.to_subgroup (center (P : Subgroup G))).nontrivial_iff_card.1 hZnt
  have hdvd : p ∣ Nat.card (center (P : Subgroup G)) := by
    rw [hcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.1 hn)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center (P : Subgroup G)) p hdvd
  set z : G := (((w : center (P : Subgroup G)) : (P : Subgroup G)) : G) with hz
  have hzP : z ∈ (P : Subgroup G) := (w : (P : Subgroup G)).2
  have hzc : z ∈ centralizer ((P : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun g hg => congrArg Subtype.val (mem_center_iff.1 w.2 ⟨g, hg⟩)
  have hzord : orderOf z = p := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hzZ := hext.mem_center_of_mem_centralizer_sylow hp hp2 hD hzP hzc hzp
  have heq : zpowers z = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_
    rw [hZc, Nat.card_zpowers, hzord]
  rw [← heq]
  exact zpowers_le.mpr hzc

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer ((centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hn' : D.map (MulAut.conj n).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (centralizer (D : Set G)).map (MulAut.conj n).toMonoidHom = centralizer (D : Set G)
  rw [centralizer_map_automorphism, hn']

theorem ExtremalObstruction.mem_center_of_mem_centralizer_of_le_normalizer {p : ℕ}
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime)
    (hp2 : p ≠ 2) (hD : ¬ IsMulCommutative D)
    (hPD : (P : Subgroup G) ≤ normalizer (D : Set G)) {y : G}
    (hyC : y ∈ centralizer (D : Set G)) (hyp : y ^ p = 1) : y ∈ (center D).map D.subtype := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) (normalizer (D : Set G)) :=
    ⟨P.subtype hPD, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPD]⟩
  have hCsyl := hPsyl.inf_of_le_normalizer (centralizer_le_normalizer (D : Set G))
    (normalizer_le_normalizer_centralizer D)
  have hye : CFSG.IsElementaryAbelian p (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
  have hyg : IsPGroup p (zpowers y) := CFSG.IsElementaryAbelian.isPGroup p (zpowers y)
  obtain ⟨Q, hQ⟩ := (hyg.comap_subtype (K := centralizer (D : Set G))).exists_le_sylow
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf p ((Q : Subgroup (centralizer (D : Set G))).map
      (centralizer (D : Set G)).subtype) (centralizer (D : Set G)) := ⟨Q, rfl⟩
  have hyT : y ∈ (Q : Subgroup (centralizer (D : Set G))).map (centralizer (D : Set G)).subtype :=
    ⟨⟨y, hyC⟩, hQ (mem_zpowers y), rfl⟩
  obtain ⟨k, hk, hconj⟩ := hCsyl.exists_mem_conj hTsyl
  have hky : k⁻¹ * y * k ∈ (P : Subgroup G) ⊓ centralizer (D : Set G) := (hconj y).mp hyT
  have hkyZ : k⁻¹ * y * k ∈ (center D).map D.subtype :=
    hext.mem_center_of_mem_centralizer hp hp2 hD hky.1 hky.2 (by
      rw [show k⁻¹ * y * k = k⁻¹ * y * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hyp, mul_one,
        mul_inv_cancel])
  obtain ⟨c, hcZ, hc⟩ := mem_map.mp hkyZ
  have hkc : k * (c : G) = (c : G) * k := (mem_centralizer_iff.mp hk (c : G) c.2).symm
  have hy : y = (c : G) := by
    calc y = k * (k⁻¹ * y * k) * k⁻¹ := by group
      _ = k * (c : G) * k⁻¹ := by rw [← hc]; rfl
      _ = (c : G) := by rw [hkc, mul_inv_cancel_right]
  rw [hy]
  exact mem_map_of_mem _ hcZ

end CFSG.LocalAnalysis.RankThreeTheoremC
