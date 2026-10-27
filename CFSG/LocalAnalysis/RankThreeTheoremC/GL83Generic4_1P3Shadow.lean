module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.AGLEmbedding.CentralizerTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.RankThree.PartOne.Census3 (IsoLie)

structure GenericShadow3 (p : ℕ) {Y : Type} [Group Y] [Finite Y] (S : Sylow p Y) (z : Y)
    (Γ : Subgroup Y) : Prop where
  prime : p.Prime
  eq_three : p = 3
  core_eq_bot : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  rank_eq : CFSG.Open.pRank p (S : Subgroup Y) = 3
  mem_center : z ∈ Subgroup.center Y
  orderOf_eq : orderOf z = p
  ne_top : Γ ≠ ⊤
  normalizer_le : ∀ D : Subgroup Y, D ≤ (S : Subgroup Y) → 2 ≤ CFSG.Open.pRank p D →
    Subgroup.normalizer (D : Set Y) ≤ Γ

namespace GenericShadow3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {S : Sylow p Y} {z : Y} {Γ : Subgroup Y}

theorem ne_two (h : GenericShadow3 p S z Γ) : p ≠ 2 := by
  have := h.eq_three
  omega

theorem mem_sylow (h : GenericShadow3 p S z Γ) : z ∈ (S : Subgroup Y) :=
  CFSG.AGLEmbedding.mem_sylow_of_mem_center h.mem_center h.orderOf_eq S

theorem exists_isComponentOf (h : GenericShadow3 p S z Γ) :
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

theorem normalizer_le_sup_zpowers (h : GenericShadow3 p S z Γ) (A : Subgroup Y) :
    normalizer (A : Set Y) ≤ normalizer ((A ⊔ zpowers z : Subgroup Y) : Set Y) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [Subgroup.map_sup, hn, MonoidHom.map_zpowers]
  congr 2
  exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp h.mem_center n)

theorem two_le_pRank_zpowers_sup (h : GenericShadow3 p S z Γ) {t : Y} (ht : orderOf t = p)
    (htz : t ∉ zpowers z) :
    2 ≤ CFSG.Open.pRank p (zpowers z ⊔ zpowers t) :=
  CFSG.AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers h.prime h.orderOf_eq
    (ht ▸ pow_orderOf_eq_one t) htz (mem_center_iff.mp h.mem_center t).symm
    (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers t))

theorem le_of_ne_isComponentOf (h : GenericShadow3 p S z Γ) {L L' : Subgroup Y}
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

theorem eq_of_isComponentOf (h : GenericShadow3 p S z Γ) {L₁ L₂ : Subgroup Y}
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

theorem normal_of_isComponentOf (h : GenericShadow3 p S z Γ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmap : L.map (MulAut.conj g).toMonoidHom = L :=
    h.eq_of_isComponentOf (IsComponentOf.map_conj hL (mem_top g)) hL
  have : (MulAut.conj g) n ∈ L.map (MulAut.conj g).toMonoidHom := mem_map_of_mem _ hn
  rw [hmap] at this
  simpa using this

theorem not_le_of_isComponentOf (h : GenericShadow3 p S z Γ)
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

theorem center_eq_bot (h : GenericShadow3 p S z Γ) (hK : KFactComponentPCoreThree)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : center L = ⊥ := by
  have hp := h.prime
  have hp3 := h.eq_three
  subst hp3
  have hpg : IsPGroup 3 (center L) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf hp h.core_eq_bot hL
  have hnot : ¬ L ≤ GLBWeakCore 3 (S : Subgroup Y) := by
    intro hle
    apply h.not_le_of_isComponentOf hL
    refine hle.trans (sSup_le ?_)
    rintro N ⟨Q, hQS, hQ2, -, rfl⟩
    exact h.normalizer_le Q hQS hQ2
  have hcore := hK Y h.catalog S L h.rank_eq.ge hL hnot
  refine eq_bot_iff.mpr fun a ha => ?_
  have hmem : a ∈ CFSG.pCore 3 L :=
    le_sSup (show center L ∈ {K : Subgroup L | K.Normal ∧ IsPGroup 3 K} from
      ⟨inferInstance, hpg⟩) ha
  rwa [hcore] at hmem

theorem not_mem_of_isComponentOf (h : GenericShadow3 p S z Γ) (hK : KFactComponentPCoreThree)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : z ∉ L := by
  intro hzL
  have hz : (⟨z, hzL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h.mem_center g)
  rw [h.center_eq_bot hK hL, mem_bot] at hz
  have hz1 : z = 1 := congrArg Subtype.val hz
  have := h.orderOf_eq
  rw [hz1, orderOf_one] at this
  exact h.prime.one_lt.ne this

theorem simple_nonab_catalog (h : GenericShadow3 p S z Γ) (hK : KFactComponentPCoreThree)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    IsSimpleGroup ↥L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup ↥L := by
  have hZ := h.center_eq_bot hK hL
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

theorem exists_sylow_map_eq_inf (h : GenericShadow3 p S z Γ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    ∃ T : Sylow p L, (T : Subgroup L).map L.subtype = (S : Subgroup Y) ⊓ L := by
  have : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)

theorem pRank_inf_le_two (h : GenericShadow3 p S z Γ) (hK : KFactComponentPCoreThree)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    CFSG.Open.pRank p ((S : Subgroup Y) ⊓ L) ≤ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAU, hA, hAc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
    ((S : Subgroup Y) ⊓ L)
  have hzA : z ∉ A := fun hz => h.not_mem_of_isComponentOf hK hL (hAU hz).2
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

theorem rankThreeGamma_ne_top (h : GenericShadow3 p S z Γ) (hK : KFactComponentPCoreThree)
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
      rw [h.center_eq_bot hK hL, mem_bot] at hz
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

theorem isRankTwoSEGroup_of_not_isCyclic_noBM (h : GenericShadow3 p S z Γ)
    (hK : KFactComponentPCoreThree) (hK1 : StronglyEmbeddedRankTwoKFactNoBM) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hBM : NotBM ↥L)
    (hnc : ¬ IsCyclic ↥((S : Subgroup Y) ⊓ L)) : IsRankTwoSEGroup p ↥L := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab, hcat⟩ := h.simple_nonab_catalog hK hL
  obtain ⟨T, hT⟩ := h.exists_sylow_map_eq_inf hL
  have hrank : CFSG.Open.pRank p (T : Subgroup L) = 2 := by
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype
      L.subtype_injective (T : Subgroup L)
    rw [hT] at hmap
    have hle := h.pRank_inf_le_two hK hL
    have hge : 2 ≤ CFSG.Open.pRank p ((S : Subgroup Y) ⊓ L) :=
      two_le_pRank_of_not_isCyclic hp h.ne_two (S.isPGroup'.to_inf_left) hnc
    omega
  exact hK1 L hsimple hnonab hcat hBM p hp h.ne_two T hrank
    (h.rankThreeGamma_ne_top hK hL T hT)

end GenericShadow3

variable {G : Type} [Group G] [Finite G]

theorem exists_genericShadow3 (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) (hp3 : p = 3) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x) :
    ∃ S : Sylow p (GenericReduced p x),
      (S : Subgroup (GenericReduced p x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
          (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) ∧
      GenericShadow3 p S
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩)
        (((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) := by
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hxP, hxL, hsyl, hrk⟩ := hx
  obtain ⟨hxM, hx1, hxp, h3, hCM⟩ := hxL
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  have hOcop : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hOM : O ≤ (C ⊓ M).subgroupOf C := by
    have h1 : GLBPrimeCore p C ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn p C).trans (pPrimeCoreIn_centralizer_le hS hp hM hrk.ge)
    rw [hO, ← glbPrimeCore_subgroupOf p C]
    exact glbPrimeCore_subgroupOf_le_inf h1
  obtain ⟨T, hT⟩ := hsyl
  have hTeq : (T : Subgroup C) = ((P : Subgroup G) ⊓ C).subgroupOf C := by
    rw [Subgroup.subgroupOf, ← hT, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  let Sbar : Sylow p (C ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O)
  have hSbar : (Sbar : Subgroup (C ⧸ O)) =
      (((P : Subgroup G) ⊓ C).subgroupOf C).map (QuotientGroup.mk' O) := by
    rw [Sylow.coe_mapSurjective, hTeq]
  refine ⟨Sbar, hSbar, ?_⟩
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hS.simple hS.nonab hx1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxCo : orderOf (⟨x, hxC⟩ : C) = p := by rw [Subgroup.orderOf_mk]; exact hxo
  refine ⟨hprime, hp3, primeComplementCore_quotient_eq_bot p,
    (catalogSimpleSections_of_isKProper hS.kProper C hCtop).quotient O, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hSbar, ← hTeq, pRank_map_mk_eq_pRank_map_subtype hprime O hOcop, hT, hrk]
  ·
    rw [mem_center_iff]
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.mp c.2))
  · exact orderOf_mk_of_coprime hprime O hOcop hxCo
  ·
    intro htop
    apply hCM
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' O) ((C ⊓ M).subgroupOf C)
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hcomap
    intro g hg
    have hmem : (⟨g, hg⟩ : C) ∈ (C ⊓ M).subgroupOf C := hcomap ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  ·
    intro Dbar hDS hD2
    rw [hSbar] at hDS
    obtain ⟨D, hDT, rfl⟩ : ∃ D ≤ ((P : Subgroup G) ⊓ C).subgroupOf C,
        D.map (QuotientGroup.mk' O) = Dbar := ⟨_, inf_le_right, map_comap_inf_eq _ hDS⟩
    have hTp : IsPGroup p (((P : Subgroup G) ⊓ C).subgroupOf C) :=
      (P.isPGroup'.to_le inf_le_left).comap_subtype
    have hDp : IsPGroup p D := hTp.to_le hDT
    have hrank : 2 ≤ CFSG.Open.pRank p (D.map C.subtype) := by
      rw [← pRank_map_mk_eq_pRank_map_subtype hprime O hOcop]
      exact hD2
    have hDG : D.map C.subtype ≤ (P : Subgroup G) := by
      refine (Subgroup.map_mono hDT).trans ?_
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
      exact inf_le_left
    have hN : normalizer ((D.map C.subtype : Subgroup G) : Set G) ≤ M :=
      normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM (hDp.map C.subtype) (hDG.trans hPM) hrank
    have hNH : normalizer (D : Set C) ≤ (C ⊓ M).subgroupOf C := fun n hn =>
      Subgroup.mem_subgroupOf.mpr
        ⟨n.property, hN (Subgroup.le_normalizer_map C.subtype ⟨n, hn, rfl⟩)⟩
    exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
      ((comap_normalizer_map_le_sup hprime O hOcop hDp).trans (sup_le hOM hNH))

end CFSG.LocalAnalysis.RankThreeTheoremC
