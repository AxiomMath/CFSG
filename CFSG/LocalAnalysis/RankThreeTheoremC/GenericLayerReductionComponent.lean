module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbedding (CatalogSimpleSections)

structure GenericShadow (p : ℕ) {Y : Type} [Group Y] [Finite Y] (S : Sylow p Y) (z : Y)
    (Γ : Subgroup Y) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  core_eq_bot : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  rank_eq : CFSG.Open.pRank p (S : Subgroup Y) = 3
  mem_center : z ∈ Subgroup.center Y
  orderOf_eq : orderOf z = p
  ne_top : Γ ≠ ⊤
  normalizer_le : ∀ D : Subgroup Y, D ≤ (S : Subgroup Y) → 2 ≤ CFSG.Open.pRank p D →
    Subgroup.normalizer (D : Set Y) ≤ Γ

namespace GenericShadow

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {S : Sylow p Y} {z : Y} {Γ : Subgroup Y}

theorem ne_two (h : GenericShadow p S z Γ) : p ≠ 2 := by have := h.five_le; omega

theorem mem_sylow (h : GenericShadow p S z Γ) : z ∈ (S : Subgroup Y) :=
  CFSG.AGLEmbedding.mem_sylow_of_mem_center h.mem_center h.orderOf_eq S

theorem pRank_top_le (h : GenericShadow p S z Γ) : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 :=
  ((CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p h.prime S).symm.trans
    h.rank_eq).le

theorem exists_isComponentOf (h : GenericShadow p S z Γ) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hno
  push Not at hno
  have hlayer : CFSG.layer Y = ⊥ := by
    by_contra hne
    obtain ⟨K, hK⟩ := CFSG.AGLEmbedding.exists_isComponentOf_of_layer_ne_bot hne
    exact hno K hK
  have hchar : centralizer (CFSG.pCore p Y : Set Y) ≤ CFSG.pCore p Y :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y p h.core_eq_bot hlayer
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have hQS : CFSG.pCore p Y ≤ (S : Subgroup Y) := CFSG.pCore_isPGroup.le_sylow_of_normal S
  have hQc : IsCyclic (CFSG.pCore p Y) := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic hp h.ne_two CFSG.pCore_isPGroup hnc
    have h3 := h.normalizer_le _ hQS h2
    rw [normalizer_eq_top] at h3
    exact h.ne_top (top_le_iff.mp h3)
  have h2 := CFSG.AGLEmbedding.pRank_top_le_two_of_isCyclic_selfCentralizing hp h.ne_two
    CFSG.pCore_isPGroup hchar hQc
  have h3 := (CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp S).symm.trans
    h.rank_eq
  omega

theorem center_eq_bot (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : center L = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hpg : IsPGroup p (center L) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf hp h.core_eq_bot hL
  have hdvd : p ∣ Nat.card (center L) := by
    have : Nontrivial (center L) := (nontrivial_iff_ne_bot _).2 hne
    obtain ⟨n, hn, hcard⟩ := hpg.nontrivial_iff_card.1 this
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L
    hL.2.2
  have hcatL : IsCatalogGroup (L ⧸ center L) :=
    h.catalog L (center L) inferInstance hL.2.2.2 hnonab
  have h4 := hK4 p hp h.five_le L hL.2.2 hcatL hpg hdvd
  have hKY : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype
      L.subtype_injective]
    exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top
  have := h.pRank_top_le
  omega

theorem not_mem_of_isComponentOf (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : z ∉ L := by
  intro hzL
  have hz : (⟨z, hzL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h.mem_center g)
  rw [h.center_eq_bot hK4 hL, mem_bot] at hz
  have hz1 : z = 1 := congrArg Subtype.val hz
  have := h.orderOf_eq
  rw [hz1, orderOf_one] at this
  exact h.prime.one_lt.ne this

theorem normalizer_le_sup_zpowers (h : GenericShadow p S z Γ) (A : Subgroup Y) :
    normalizer (A : Set Y) ≤ normalizer ((A ⊔ zpowers z : Subgroup Y) : Set Y) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [Subgroup.map_sup, hn, MonoidHom.map_zpowers]
  congr 2
  exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp h.mem_center n)

theorem two_le_pRank_zpowers_sup (h : GenericShadow p S z Γ) {t : Y} (ht : orderOf t = p)
    (htz : t ∉ zpowers z) :
    2 ≤ CFSG.Open.pRank p (zpowers z ⊔ zpowers t) :=
  CFSG.AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers h.prime h.orderOf_eq
    (ht ▸ pow_orderOf_eq_one t) htz (mem_center_iff.mp h.mem_center t).symm
    (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers t))

theorem le_of_ne_isComponentOf (h : GenericShadow p S z Γ) {L L' : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤) (hne : L' ≠ L) : L ≤ Γ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ⟨htS, htL'⟩, hto, htZ⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot S hL'
  have hzc : zpowers z ≤ centralizer (L' : Set Y) := fun x hx =>
    mem_centralizer_iff.mpr fun l _ => (mem_center_iff.mp (zpowers_le.mpr h.mem_center hx) l)
  have htz : t ∉ zpowers z := fun ht => htZ (hzc ht)
  have h2 := h.two_le_pRank_zpowers_sup hto htz
  have hDS : zpowers z ⊔ zpowers t ≤ (S : Subgroup Y) :=
    sup_le (zpowers_le.mpr h.mem_sylow) (zpowers_le.mpr htS)
  have hLL' : L ≤ centralizer (L' : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne.symm)
  have hDL : zpowers z ⊔ zpowers t ≤ centralizer (L : Set Y) := by
    refine sup_le (fun x hx => mem_centralizer_iff.mpr fun l _ =>
      mem_center_iff.mp (zpowers_le.mpr h.mem_center hx) l) ?_
    exact (zpowers_le.mpr htL').trans (le_centralizer_iff.mp hLL')
  exact (le_centralizer_iff.mp hDL).trans
    ((centralizer_le_normalizer _).trans (h.normalizer_le _ hDS h2))

theorem eq_of_isComponentOf (h : GenericShadow p S z Γ) {L₁ L₂ : Subgroup Y}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) : L₁ = L₂ := by
  by_contra hne
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ Γ := by
    intro L hL
    by_cases h12 : L₂ = L
    · exact h.le_of_ne_isComponentOf hL h₁ (fun h1 => hne (h1.trans h12.symm))
    · exact h.le_of_ne_isComponentOf hL h₂ h12
  have hE : rankThreeLayer (⊤ : Subgroup Y) ≤ Γ := sSup_le fun L hL => hall L hL
  obtain ⟨t₁, ⟨ht₁S, ht₁L⟩, ht₁o, ht₁Z⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot S h₁
  obtain ⟨t₂, ⟨ht₂S, ht₂L⟩, ht₂o, ht₂Z⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot S h₂
  have h12 : L₁ ≤ centralizer (L₂ : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne)
  have ht₂ : t₂ ∉ zpowers t₁ := fun hmem =>
    ht₂Z (h12 ((zpowers_le.mpr ht₁L) hmem))
  have hcomm : Commute t₁ t₂ := (mem_centralizer_iff.mp (h12 ht₁L) t₂ ht₂L).symm
  have h2 : 2 ≤ CFSG.Open.pRank p (zpowers t₁ ⊔ zpowers t₂) :=
    CFSG.AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers hp ht₁o
      (ht₂o ▸ pow_orderOf_eq_one t₂) ht₂ hcomm (mem_sup_left (mem_zpowers t₁))
      (mem_sup_right (mem_zpowers t₂))
  have hL₁E : L₁ ≤ rankThreeLayer (⊤ : Subgroup Y) := le_sSup h₁
  have hL₂E : L₂ ≤ rankThreeLayer (⊤ : Subgroup Y) := le_sSup h₂
  have hle : zpowers t₁ ⊔ zpowers t₂ ≤ (S : Subgroup Y) ⊓ rankThreeLayer (⊤ : Subgroup Y) :=
    sup_le (zpowers_le.mpr ⟨ht₁S, hL₁E ht₁L⟩) (zpowers_le.mpr ⟨ht₂S, hL₂E ht₂L⟩)
  have hN : normalizer (((S : Subgroup Y) ⊓ rankThreeLayer (⊤ : Subgroup Y) : Subgroup Y) :
      Set Y) ≤ Γ :=
    h.normalizer_le _ inf_le_left ((h2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      hle)))
  have : (rankThreeLayer (⊤ : Subgroup Y)).Normal := CFSG.ComponentClassification.Layer.normal Y
  exact CFSG.AGLEmbedding.not_le_of_normalizer_inf_le S hN h.ne_top hE

theorem normal_of_isComponentOf (h : GenericShadow p S z Γ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmap : L.map (MulAut.conj g).toMonoidHom = L :=
    h.eq_of_isComponentOf (IsComponentOf.map_conj hL (mem_top g)) hL
  have : (MulAut.conj g) n ∈ L.map (MulAut.conj g).toMonoidHom := mem_map_of_mem _ hn
  rw [hmap] at this
  simpa using this

theorem not_le_of_isComponentOf (h : GenericShadow p S z Γ)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : ¬ L ≤ Γ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : L.Normal := h.normal_of_isComponentOf hL
  obtain ⟨t, ⟨htS, htL⟩, hto, htZ⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot S hL
  have hzc : zpowers z ≤ centralizer (L : Set Y) := fun x hx =>
    mem_centralizer_iff.mpr fun l _ => (mem_center_iff.mp (zpowers_le.mpr h.mem_center hx) l)
  have htz : t ∉ zpowers z := fun ht => htZ (hzc ht)
  have h2 : 2 ≤ CFSG.Open.pRank p (zpowers z ⊔ zpowers t) := h.two_le_pRank_zpowers_sup hto htz
  have hDS : (S : Subgroup Y) ⊓ L ⊔ zpowers z ≤ (S : Subgroup Y) :=
    sup_le inf_le_left (zpowers_le.mpr h.mem_sylow)
  have htSL : t ∈ (S : Subgroup Y) ⊓ L := ⟨htS, htL⟩
  have hle : zpowers z ⊔ zpowers t ≤ (S : Subgroup Y) ⊓ L ⊔ zpowers z :=
    sup_le le_sup_right (zpowers_le.mpr (mem_sup_left htSL))
  have h2' : 2 ≤ CFSG.Open.pRank p ((S : Subgroup Y) ⊓ L ⊔ zpowers z) :=
    h2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle)
  have hN : normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) ≤ Γ :=
    (h.normalizer_le_sup_zpowers _).trans (h.normalizer_le _ hDS h2')
  exact CFSG.AGLEmbedding.not_le_of_normalizer_inf_le S hN h.ne_top

theorem simple_nonab_catalog (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    IsSimpleGroup ↥L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup ↥L := by
  have hZ := h.center_eq_bot hK4 hL
  let e : L ≃* L ⧸ center L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (L ⧸ center L) := hL.2.2.2
  have hsimple : IsSimpleGroup L := e.isSimpleGroup
  have hnonab : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hL.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  exact ⟨hsimple, hnonab, h.catalog.simple_subgroup L hsimple hnonab⟩

theorem exists_sylow_map_eq_inf (h : GenericShadow p S z Γ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    ∃ T : Sylow p L, (T : Subgroup L).map L.subtype = (S : Subgroup Y) ⊓ L := by
  have : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)

theorem pRank_inf_le_two (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    CFSG.Open.pRank p ((S : Subgroup Y) ⊓ L) ≤ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAU, hA, hAc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
    ((S : Subgroup Y) ⊓ L)
  have hzA : z ∉ A := fun hz => h.not_mem_of_isComponentOf hK4 hL (hAU hz).2
  have hcomm : ∀ e ∈ A, e * z = z * e := fun e _ => mem_center_iff.mp h.mem_center e
  have hzp : z ^ p = 1 := h.orderOf_eq ▸ pow_orderOf_eq_one z
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp A hzp hzA hcomm
  have hAz : A ≤ centralizer ((zpowers z : Subgroup Y) : Set Y) := fun e he =>
    mem_centralizer_iff.mpr fun w hw => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (hcomm e he).symm k |>.symm).eq.symm
  have hE := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hA
    (CFSG.AGLEmbedding.isElemAbelian_zpowers hzp) hAz
  have hle : A ⊔ zpowers z ≤ (S : Subgroup Y) :=
    sup_le (hAU.trans inf_le_left) (zpowers_le.mpr h.mem_sylow)
  have hk := le_pRank_of_elemAbelian_card (p := p) hle hE
    (k := CFSG.Open.pRank p ((S : Subgroup Y) ⊓ L) + 1) (by rw [hcard, hAc, pow_succ])
  have := h.rank_eq
  omega

theorem exists_orderOf_eq_of_one_le_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {H : Subgroup X} (h1 : 1 ≤ CFSG.Open.pRank p H) : ∃ t ∈ H, orderOf t = p := by
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp H
  have hne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEc
    have : p ^ 1 ≤ p ^ CFSG.Open.pRank p H := Nat.pow_le_pow_right hp.pos h1
    have h2 : 1 < p ^ 1 := by simpa using hp.one_lt
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨t, hEH ht, orderOf_eq_prime (hE.2 t ht) ht1'⟩

theorem rankThreeGamma_ne_top (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (T : Sylow p L)
    (hT : (T : Subgroup L).map L.subtype = (S : Subgroup Y) ⊓ L) :
    rankThreeGamma 1 p (T : Subgroup L) ≠ ⊤ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hle : rankThreeGamma 1 p (T : Subgroup L) ≤ Γ.comap L.subtype := by
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQ1, rfl⟩ n hn
    change (n : Y) ∈ Γ
    obtain ⟨q, hqQ, hqo⟩ := exists_orderOf_eq_of_one_le_pRank hp hQ1
    have hQS : Q.map L.subtype ≤ (S : Subgroup Y) ⊓ L :=
      hT ▸ Subgroup.map_mono hQT
    have htq : ((q : L) : Y) ∈ Q.map L.subtype := mem_map_of_mem _ hqQ
    have hto : orderOf ((q : L) : Y) = p := by rw [Subgroup.orderOf_coe]; exact hqo
    have htz : ((q : L) : Y) ∉ zpowers z := by
      intro hmem
      have hz : q ∈ center L := by
        rw [mem_center_iff]
        intro g
        exact Subtype.ext (mem_center_iff.mp (zpowers_le.mpr h.mem_center hmem) g)
      rw [h.center_eq_bot hK4 hL, mem_bot] at hz
      have : ((q : L) : Y) = 1 := congrArg Subtype.val hz
      rw [this, orderOf_one] at hto
      exact hp.one_lt.ne hto
    have h2 := h.two_le_pRank_zpowers_sup hto htz
    have hDS : Q.map L.subtype ⊔ zpowers z ≤ (S : Subgroup Y) :=
      sup_le (hQS.trans inf_le_left) (zpowers_le.mpr h.mem_sylow)
    have h2' : 2 ≤ CFSG.Open.pRank p (Q.map L.subtype ⊔ zpowers z) :=
      h2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
        (sup_le le_sup_right (zpowers_le.mpr (mem_sup_left htq))))
    have hn' : (n : Y) ∈ normalizer ((Q.map L.subtype : Subgroup Y) : Set Y) :=
      Subgroup.le_normalizer_map L.subtype ⟨n, hn, rfl⟩
    exact h.normalizer_le _ hDS h2' (h.normalizer_le_sup_zpowers _ hn')
  intro htop
  rw [htop, top_le_iff] at hle
  apply h.not_le_of_isComponentOf hL
  intro l hl
  have : (⟨l, hl⟩ : L) ∈ Γ.comap L.subtype := hle ▸ mem_top _
  exact this

end GenericShadow

end CFSG.LocalAnalysis.RankThreeTheoremC
