module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoTwelveBound
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoTwelveLift

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal


section CaseI

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {Q : Subgroup G} {z u : G}

theorem centralizer_le_of_caseI_twelve (htri : ExactShapeTrichotomy) (h : Setting G L 12)
    (d : Cyc L Q z) (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 12))
    {S₀ : Finset (Fin 12)} (hS₀ : S₀.card = 3) (hI : CaseIAt e z S₀) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf h d e hx).IsSwap) :
    centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) := by
  classical
  obtain ⟨hx2, -, hx1⟩ := swap_elt_facts h d T e hx hτ
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hex : ExactShape z L 12 := exactShape_of_setting h d T.card
  have hzx : z ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]; exact (mem_centralizer_singleton_iff.1 hx).symm
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hnear : ∀ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b → b ≠ z →
      7 ≤ (fixFin (permOf h d e hb)).card → False := by
    intro b hb hzb hbz h7
    obtain ⟨c, hc⟩ := isConj_iff.1 hzb
    exact near_partner_false h d T e (Or.inl hS₀) (by omega) hI hb hc hbz ⟨by omega, by omega⟩
  have hfus : ¬ IsConj z (z * x) := by
    intro hc
    have hzxC : z * x ∈ centralizer ({z} : Set G) := mul_mem hzC hx
    have hp : permOf h d e hzxC = permOf h d e hx := by
      rw [permOf_mul h d e hzC hx hzxC, permOf_self h d e hzC, one_mul]
    refine hnear (z * x) hzxC hc ?_ ?_
    · intro h'
      exact hx1 (mul_eq_left.1 h')
    · rw [hp, card_fixFin_of_isSwap hτ]
      norm_num
  have hxL : x ∉ L := by
    intro hxL
    have h1 := permOf_of_mem h d e hx hxL
    have h2 := hτ.sign_eq
    rw [h1, (mem_alternatingGroup.1 (e ⟨x, hxL⟩).2)] at h2
    exact absurd h2 (by decide)
  set F : Finset (Fin 12) := fixFin (permOf h d e hx) with hF
  have hFcard : F.card = 10 := card_fixFin_of_isSwap hτ
  obtain ⟨S₁, hS₁F, hS₁⟩ := Finset.exists_subset_card_eq (show 3 ≤ F.card by omega)
  have hI₁ : CaseIAt e z S₁ :=
    caseIAt_transport hex e (hS₀.trans hS₁.symm) (by rw [card_compl_fin]; omega) hI
  have hfix₁ : ∀ i ∈ S₁, permOf h d e hx i = i := fun i hi => mem_fixFin.1 (hS₁F hi)
  have hfixF : ∀ i ∈ F, permOf h d e hx i = i := fun i hi => mem_fixFin.1 hi
  set R₁ : Subgroup G := corr (X := G) e (altSub S₁) with hR₁
  set D : Subgroup G := corr (X := G) e (altSub (F \ S₁)) with hD
  have hDcard7 : (F \ S₁).card = 7 := by rw [Finset.card_sdiff_of_subset hS₁F]; omega
  have hR₁card : Nat.card R₁ = 3 := by
    obtain ⟨eR⟩ := exists_equiv_corr_altSub (X := G) e S₁
    rw [card_eq_of_equiv_alt (by omega) eR, hS₁]
    rfl
  have hDcard : Nat.card D = 2520 := by
    obtain ⟨eD⟩ := exists_equiv_corr_altSub (X := G) e (F \ S₁)
    rw [card_eq_of_equiv_alt (by omega) eD, hDcard7]
    rfl
  obtain ⟨r, hrR, hr1⟩ := exists_ne_one_of_card_ge_three (G := G) e (S := S₁) (by omega)
  have hrord : orderOf r = 3 := by
    have h1 := orderOf_dvd_natCard (⟨r, hrR⟩ : R₁)
    rw [Subgroup.orderOf_mk, hR₁card] at h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hr1
    · exact h2
  have hR₁le : ∀ w ∈ R₁, w ∈ zpowers r := by
    have hle : zpowers r ≤ R₁ := zpowers_le.2 hrR
    have heq : zpowers r = R₁ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hR₁card, Nat.card_zpowers, hrord])
    intro w hw
    rw [heq]; exact hw
  have hrx : r ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_permOf_fix h d e hx hfix₁ hrR).symm
  have hrF : r ∈ corr (X := G) e (altSub F) := corr_mono e (altSub_mono hS₁F) hrR
  have hDx : D ≤ centralizer ({x} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_permOf_fix h d e hx
      (fun i hi => hfixF i (Finset.sdiff_subset hi)) hw).symm
  have hDF : D ≤ corr (X := G) e (altSub F) := corr_mono e (altSub_mono Finset.sdiff_subset)
  have hDr : ∀ w ∈ D, w * r = r * w := by
    have hle := corr_le_centralizer_corr (X := G) e (T₁ := altSub S₁) (T₂ := altSub (F \ S₁))
      (fun g hg g' hg' => comm_of_altSub_disjoint Finset.disjoint_sdiff hg hg')
    intro w hw
    exact (mem_centralizer_iff.1 (hle hw).2 r hrR).symm
  set N : Subgroup ↥(centralizer ({x} : Set G)) := zpowers (selfC x) with hN
  have hmk1 : ∀ (w : G) (hw : w ∈ centralizer ({x} : Set G)), w ∈ L →
      (QuotientGroup.mk ⟨w, hw⟩ : TwoSec x) = 1 → w = 1 := by
    intro w hw hwL h1
    rcases (mem_zpowers_selfC_iff hx2).1 ((QuotientGroup.eq_one_iff _).1 h1) with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hwL) hxL
  set ιD : ↥D →* TwoSec x := (QuotientGroup.mk' N).comp (Subgroup.inclusion hDx) with hιD
  have hιDinj : Function.Injective ιD := by
    rw [injective_iff_map_eq_one]
    intro w hw
    exact Subtype.ext (hmk1 w (hDx w.2) (corr_le e _ w.2) hw)
  set Db : Subgroup (TwoSec x) := ιD.range with hDb
  have hDbcard : Nat.card Db = 2520 :=
    (Nat.card_congr (MonoidHom.ofInjective hιDinj).toEquiv).symm.trans hDcard
  set rb : TwoSec x := QuotientGroup.mk ⟨r, hrx⟩ with hrb
  have hrbA : rb ∈ twoSecComp e x F :=
    ⟨⟨r, hrx⟩, Subgroup.mem_subgroupOf.2 hrF, rfl⟩
  have hDbA : Db ≤ twoSecComp e x F := by
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨w, hDx w.2⟩, Subgroup.mem_subgroupOf.2 (hDF w.2), rfl⟩
  have hDbr : Db ≤ centralizer ({rb} : Set (TwoSec x)) := by
    rintro _ ⟨w, rfl⟩
    rw [mem_centralizer_singleton_iff, hιD, MonoidHom.comp_apply, hrb, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hDr w w.2)
  have hrbord : orderOf rb = 3 := by
    have h1 : rb ^ 3 = 1 := by
      rw [hrb, ← QuotientGroup.mk_pow]
      have : (⟨r, hrx⟩ : ↥(centralizer ({x} : Set G))) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hrord, pow_orderOf_eq_one]
        rfl
      rw [this]
      rfl
    have h2 : rb ≠ 1 := fun h' => hr1 (hmk1 r hrx (corr_le e _ hrR) h')
    exact orderOf_eq_prime h1 h2
  have hkey : ∀ Tb : Subgroup (TwoSec x), IsPGroup 2 Tb →
      Tb ≤ centralizer ({rb} : Set (TwoSec x)) → Nat.card Tb = 2 ^ 6 → False := by
    intro Tb hTb hTbr hTbcard
    obtain ⟨P, hP, hPx, hPr, hPcard⟩ :=
      exists_lift_of_twoSec hx2 hx1 hrx (by rw [hrord]; decide) hTb hTbr
    have hPR : P ≤ centralizer (R₁ : Set G) := by
      intro p hp
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (hR₁le w hw)
      have hpr : p * r = r * p := mem_centralizer_singleton_iff.1 (hPr hp)
      exact ((Commute.zpow_left (show Commute r p from hpr.symm) k)).eq
    have hdvd := card_dvd_of_caseI h d T e (by norm_num) hS₁ hI₁ hx hτ hfix₁ hP hPR hPx
    rw [hPcard, hTbcard] at hdvd
    revert hdvd
    decide
  have hE := exactShape_twoSec h d T e (by norm_num) hx hτ hfus hzx
  rcases htri (TwoSec x) _ _ (12 - 2) (by norm_num) (isKGroupCat_twoSec h hx1)
      (oddCore_twoSec_eq_bot h hxord) hE with h1 | h1 | h1 | ⟨-, h1⟩
  · exact centralizer_le_of_mem_center hx2 hfus hzx h1
  · exfalso
    obtain ⟨Tb, hTb, hTbr, hTbcard⟩ :=
      exists_two_subgroup_of_wreath (k := 3) (by norm_num) h1 hrbA hDbA hDbr
        (by rw [hDbcard]; norm_num)
    exact hkey Tb hTb hTbr hTbcard
  · exfalso
    obtain ⟨b, hb, hzb, hbz, hcard⟩ :=
      exists_partner_of_symOutcome h d T e (by norm_num) hx hτ hfus hzx h1
    exact hnear b hb hzb hbz (by omega)
  · exfalso
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 7 (by rw [hDcard]; norm_num)
    have hcb : orderOf (ιD c) = 7 := by rw [orderOf_injective ιD hιDinj c, hc]
    have hcbr : rb * ιD c = ιD c * rb :=
      (mem_centralizer_singleton_iff.1 (hDbr ⟨c, rfl⟩)).symm
    obtain ⟨Tb, hTb, hTbr, hTbcard⟩ := exists_two_subgroup_of_hnOutcome h1 hrbord hcb hcbr
    exact hkey Tb hTb hTbr hTbcard

theorem false_of_caseI_twelve (htri : ExactShapeTrichotomy) (h : Setting G L 12)
    (d : Cyc L Q z) (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 12))
    {S₀ : Finset (Fin 12)} (hS₀ : S₀.card = 3) (hI : CaseIAt e z S₀) : False :=
  false_of_caseI_of_claim h d T e (by norm_num) (Or.inl hS₀) (by omega) hI
    fun hx hτ => centralizer_le_of_caseI_twelve htri h d T e hS₀ hI hx hτ

end CaseI

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {Q : Subgroup G} {z u : G}

theorem shapeTwo_dichotomy_twelve (htri : ExactShapeTrichotomy)
    (h47 : ShapeTwoCentDoubleAt 12) (h : Setting G L 12) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 12)) :
    CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z 12 H := by
  classical
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (Fin 12), S₀.card = 3 := ⟨{0, 1, 2}, by decide⟩
  have hex : ExactShape z L 12 := exactShape_of_setting h d T.card
  have ht : z ∈ centralizer (corr (X := G) e (altSub S₀) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S₀)
  have hsec := exactShape_section_three hex e hS₀ (by omega) ht
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S₀))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper h.std.kProper)
      (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
  have hO := oddCore_sec_eq_bot (corr (X := G) e (altSub S₀))
  rcases htri _ _ _ (12 - S₀.card) (by omega) hKcat hO hsec with h1 | h1 | h1 | h1
  · exact (false_of_caseI_twelve htri h d T e hS₀ ⟨ht, h1⟩).elim
  · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex e (by norm_num) hS₀ ⟨ht, h1⟩
    exact Or.inr (Or.inr ⟨H, hH⟩)
  · rcases caseII_of_centDoubleAt h47 h d T e (by norm_num) (Or.inl hS₀) (by omega) ⟨ht, h1⟩ with
      h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · omega

theorem false_of_shapeTwo_twelve (htri : ExactShapeTrichotomy)
    (h47 : ShapeTwoCentDoubleAt 12) (h : Setting G L 12) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 12)) : False :=
  false_of_shapeTwo_of_dichotomy htri h d T.card le_rfl T.cent T.outer T.sq e
    (shapeTwo_dichotomy_twelve htri h47 h d T e)

end Main

end CFSG.OddStandard.AltStdSec
