module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Transfer
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionStructure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbedding
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open scoped commutatorElement

theorem exists_orderOf_eq_of_one_le_pRank' {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {H : Subgroup Y} (h1 : 1 ≤ CFSG.Open.pRank p H) :
    ∃ t ∈ H, orderOf t = p := by
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

theorem mem_zpowers_of_ne_one {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {x y : Y}
    (hx : orderOf x = p) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) :
    x ∈ Subgroup.zpowers y := by
  have : Fact p.Prime := ⟨hp⟩
  have hyp : y ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hy
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hyo])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem disjoint_zpowers_of_not_mem {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {x : Y}
    (hx : orderOf x = p) {L : Subgroup Y} (hxL : x ∉ L) : Disjoint L (Subgroup.zpowers x) := by
  rw [Subgroup.disjoint_def]
  intro y hyL hyx
  by_contra hy1
  exact hxL (Subgroup.zpowers_le.mpr hyL (mem_zpowers_of_ne_one hp hx hyx hy1))

theorem card_sup_zpowers_of_normal {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {x : Y}
    (hx : orderOf x = p) {L : Subgroup Y} [L.Normal] (hxL : x ∉ L) :
    Nat.card ↥(L ⊔ Subgroup.zpowers x) = Nat.card L * p := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L (Subgroup.zpowers x)
    (by rw [Subgroup.zpowers_le]; exact Subgroup.normalizer_eq_top L ▸ Subgroup.mem_top x)
    (disjoint_zpowers_of_not_mem hp hx hxL), Nat.card_zpowers, hx]

theorem sup_zpowers_inf_centralizer_eq_bot {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {x : Y} (hx : orderOf x = p) {L : Subgroup Y} [L.Normal]
    (hLC : L ⊓ Subgroup.centralizer (L : Set Y) = ⊥)
    (hxLC : x ∉ L ⊔ Subgroup.centralizer (L : Set Y)) :
    (L ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro y ⟨hyX, hyC⟩
  have hyX' : y ∈ ((Subgroup.zpowers x ⊔ L : Subgroup Y) : Set Y) := by
    rw [sup_comm]
    exact hyX
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (by rw [Subgroup.zpowers_le]; exact Subgroup.normalizer_eq_top L ▸ Subgroup.mem_top x)] at hyX'
  obtain ⟨z, hz, l, hl, hzl⟩ := Set.mem_mul.mp hyX'
  subst hzl
  have hzy : z ∈ L ⊔ Subgroup.centralizer (L : Set Y) := by
    have h1 : z = (z * l) * l⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyC)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl))
  by_cases hz1 : z = 1
  · rw [hz1, one_mul] at hyC ⊢
    have : l ∈ L ⊓ Subgroup.centralizer (L : Set Y) := ⟨hl, hyC⟩
    rw [hLC, Subgroup.mem_bot] at this
    exact this
  · exfalso
    exact hxLC (Subgroup.zpowers_le.mpr hzy (mem_zpowers_of_ne_one hp hx hz hz1))

theorem isCyclic_of_le_cyclic {Y : Type*} [Group Y] {H K : Subgroup Y} (hHK : H ≤ K)
    [IsCyclic K] : IsCyclic H := by
  have : IsCyclic (H.subgroupOf K) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hHK).surjective

theorem card_le_of_isElemAbelian_of_le_cyclic {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : 0 < p) {E K : Subgroup Y} (hE : IsElemAbelian p E) (hEK : E ≤ K) [IsCyclic K] :
    Nat.card E ≤ p := by
  have : IsCyclic E := isCyclic_of_le_cyclic hEK
  exact card_le_of_isCyclic_of_forall_pow_eq_one hp
    (fun c => Subtype.ext (by simpa using hE.2 c c.2))

structure NoncentralReduced (p : ℕ) (X : Type) [Group X] [Finite X] (R : Sylow p X)
    (X₀ B : Subgroup X) (u : X) : Prop where
  red : ReducedNongeneration p X R X₀
  catalog : CatalogSimpleSections X
  BR : B ≤ (R : Subgroup X)
  Be : IsElemAbelian p B
  Bc : Nat.card B = p ^ 3
  omega : ∀ x ∈ (R : Subgroup X), x ^ p = 1 → x ∈ B
  uB : u ∈ B
  uo : orderOf u = p
  uc : u ∈ center X
  uR : u ∉ ⁅(R : Subgroup X), (R : Subgroup X)⁆

namespace NoncentralReduced

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ B : Subgroup X} {u : X}
  (h : NoncentralReduced p X R X₀ B u)

include h

theorem three_le_pRank_B : 3 ≤ CFSG.Open.pRank p B := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  exact le_pRank_of_elemAbelian_card le_rfl h.Be h.Bc

theorem normalizer_le {D : Subgroup X} (hDR : D ≤ (R : Subgroup X))
    (hD2 : 2 ≤ CFSG.Open.pRank p D) : normalizer (D : Set X) ≤ X₀ := by
  classical
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set D₁ : Subgroup X := omegaOneOf p D with hD₁
  have hD₁B : D₁ ≤ B := (closure_le _).2 fun x hx => h.omega x (hDR hx.1) hx.2
  obtain ⟨E, hED, hE, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp D
  have hED₁ : E ≤ D₁ := le_omegaOneOf_of_isElemAbelian hED hE
  have hD₁2 : 2 ≤ CFSG.Open.pRank p D₁ := by
    have := le_pRank_of_elemAbelian_card hED₁ hE hEc
    omega
  have hBC : B ≤ (R : Subgroup X) ⊓ centralizer (D₁ : Set X) := by
    refine le_inf h.BR fun b hb => mem_centralizer_iff.mpr fun x hx => ?_
    exact congrArg Subtype.val (h.Be.1.is_comm.comm ⟨x, hD₁B hx⟩ ⟨b, hb⟩)
  have h3 : 3 ≤ CFSG.Open.pRank p (D₁ ⊔ ((R : Subgroup X) ⊓ centralizer (D₁ : Set X))) :=
    h.three_le_pRank_B.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (hBC.trans le_sup_right))
  have hD₁R : D₁ ≤ (R : Subgroup X) := (omegaOneOf_le p D).trans hDR
  exact (normalizer_le_normalizer_omegaOneOf p D).trans
    ((CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hD₁R hD₁2 h3).trans
      h.red.weakCore_le)

theorem ne_two : p ≠ 2 := h.red.ne_two

theorem uR' : u ∈ (R : Subgroup X) := h.BR h.uB

theorem exists_isComponentOf : ∃ L : Subgroup X, IsComponentOf L ⊤ := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hno
  push Not at hno
  have hlayer : CFSG.layer X = ⊥ := by
    by_contra hne
    obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hne
    exact hno K hK
  have hchar : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p h.red.core_eq_bot hlayer
  have : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hQR : CFSG.pCore p X ≤ (R : Subgroup X) := CFSG.pCore_isPGroup.le_sylow_of_normal R
  have hQc : IsCyclic (CFSG.pCore p X) := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic hp h.ne_two CFSG.pCore_isPGroup hnc
    have h3 := h.normalizer_le hQR h2
    rw [normalizer_eq_top] at h3
    exact h.red.ne_top (top_le_iff.mp h3)
  have h2 := pRank_top_le_two_of_isCyclic_selfCentralizing hp h.ne_two CFSG.pCore_isPGroup
    hchar hQc
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    h.red.three_le_pRank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top)
  omega

theorem normal_of {L : Subgroup X} (hL : IsComponentOf L ⊤) : L.Normal :=
  h.red.normal_of_isComponentOf_of_center h.uc h.uo hL

theorem exists_sylow {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    ∃ T : Sylow p L, (T : Subgroup L).map L.subtype = (R : Subgroup X) ⊓ L := by
  have : Fact p.Prime := ⟨h.red.prime⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)

theorem not_mem_and_center_eq_bot {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    u ∉ L ∧ center L = ⊥ := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  rcases h.red.mem_or_rankOne_of_center h.uc h.uo hL with ⟨huZ, -⟩ | ⟨huL, hZ, -⟩
  · exfalso
    obtain ⟨z, hz, hzu⟩ := huZ
    obtain ⟨T, hT⟩ := h.exists_sylow hL
    have hzu' : (z : X) = u := hzu
    have huL : u ∈ L := hzu' ▸ z.2
    have hzT : z ∈ (T : Subgroup L) := by
      have hmem : u ∈ (R : Subgroup X) ⊓ L := ⟨h.uR', huL⟩
      rw [← hT] at hmem
      obtain ⟨t, htT, htu⟩ := hmem
      have : t = z := Subtype.ext (htu.trans hzu'.symm)
      exact this ▸ htT
    have hcop : Nat.Coprime (T : Subgroup L).index (orderOf z) := by
      have hord : orderOf z = p := by rw [← Subgroup.orderOf_coe, hzu', h.uo]
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 T.not_dvd_index).symm
    have hperf : commutator L = ⊤ := hL.2.2.1
    have key := mem_commutator_of_mem_center_of_perfect hperf hz hzT hcop
    have hmap : u ∈ ((commutator (T : Subgroup L)).map
        ((L.subtype).comp (T : Subgroup L).subtype)) := ⟨_, key, by simp [hzu']⟩
    refine h.uR ?_
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top] at hmap
    have hrange : ((L.subtype).comp (T : Subgroup L).subtype).range =
        (R : Subgroup X) ⊓ L := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hT]
    rw [hrange] at hmap
    exact Subgroup.commutator_mono inf_le_left inf_le_left hmap
  · exact ⟨huL, hZ⟩

theorem normalizer_le_sup_zpowers (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer ((A ⊔ zpowers u : Subgroup X) : Set X) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [Subgroup.map_sup, hn, MonoidHom.map_zpowers]
  congr 2
  exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp h.uc n)

theorem not_le_X₀ {L : Subgroup X} (hL : IsComponentOf L ⊤) (huL : u ∉ L) : ¬ L ≤ X₀ := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : L.Normal := h.normal_of hL
  obtain ⟨t, ⟨htR, htL⟩, hto, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.red.core_eq_bot R hL
  have hD : (R : Subgroup X) ⊓ L ⊔ zpowers u ≤ (R : Subgroup X) :=
    sup_le inf_le_left (zpowers_le.mpr h.uR')
  have htu : u ∉ zpowers t := fun hmem => huL (zpowers_le.mpr htL hmem)
  have h2 : 2 ≤ CFSG.Open.pRank p ((R : Subgroup X) ⊓ L ⊔ zpowers u) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp hto (h.uo ▸ pow_orderOf_eq_one u) htu
      (mem_center_iff.mp h.uc t) (mem_sup_left ⟨htR, htL⟩) (mem_sup_right (mem_zpowers u))
  have hN : normalizer (((R : Subgroup X) ⊓ L : Subgroup X) : Set X) ≤ X₀ :=
    (h.normalizer_le_sup_zpowers _).trans (h.normalizer_le hD h2)
  exact not_le_of_normalizer_inf_le R hN h.red.ne_top

theorem isCyclic_inf_centralizer {L : Subgroup X} (hnle : ¬ L ≤ X₀) :
    IsCyclic ↥((R : Subgroup X) ⊓ centralizer (L : Set X)) := by
  have hp := h.red.prime
  by_contra hnc
  have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (R.isPGroup'.to_inf_left) hnc
  have hN := h.normalizer_le inf_le_left h2
  exact hnle ((le_centralizer_iff.mpr (inf_le_right : (R : Subgroup X) ⊓ centralizer (L : Set X) ≤
    centralizer (L : Set X))).trans ((centralizer_le_normalizer _).trans hN))

theorem simple_nonab_catalog {L : Subgroup X} (hL : IsComponentOf L ⊤) (hZ : center L = ⊥) :
    IsSimpleGroup ↥L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup ↥L := by
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

theorem pRank_le_three : CFSG.Open.pRank p (R : Subgroup X) ≤ 3 := by
  have hp := h.red.prime
  obtain ⟨A, hAR, hA, hAc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
    (R : Subgroup X)
  have hAB : A ≤ B := fun x hx => h.omega x (hAR hx) (hA.2 x hx)
  have hle : p ^ CFSG.Open.pRank p (R : Subgroup X) ≤ p ^ 3 := by
    rw [← hAc, ← h.Bc]
    exact Subgroup.card_le_of_le hAB
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

theorem pRank_inf_le_two {L : Subgroup X} (huL : u ∉ L) :
    CFSG.Open.pRank p ((R : Subgroup X) ⊓ L) ≤ 2 := by
  have : Fact p.Prime := ⟨h.red.prime⟩
  by_cases hpos : 0 < CFSG.Open.pRank p ((R : Subgroup X) ⊓ L)
  · have h1 := pRank_inf_add_one_le (P := (R : Subgroup X)) (C := ⊤) (L := L) le_top h.uR'
      (h.uo ▸ pow_orderOf_eq_one u) (fun c _ => mem_center_iff.mp h.uc c) huL hpos
    have := h.pRank_le_three
    omega
  · omega

theorem eq_sup_zpowers {B₀ : Subgroup X} (hB₀ : B₀ ≤ B) (hc : Nat.card B₀ = p ^ 2)
    (hu : u ∉ B₀) : B₀ ⊔ zpowers u = B := by
  have hp := h.red.prime
  have hle : B₀ ⊔ zpowers u ≤ B := sup_le hB₀ (zpowers_le.mpr h.uB)
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp B₀
    (h.uo ▸ pow_orderOf_eq_one u) hu (fun e _ => mem_center_iff.mp h.uc e)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, hc, h.Bc]
  exact (pow_succ p 2).le

theorem commutator_le_of_sup {B₀ T C : Subgroup X} (hsup : B₀ ⊔ zpowers u = B)
    (hle : ⁅B₀, T⁆ ≤ C) : ⁅B, T⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro b hb t ht
  rw [← hsup] at hb
  have : (zpowers u).Normal := Subgroup.normal_of_le_center (zpowers_le.mpr h.uc)
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  have hzc : ∀ g : X, g * z = z * g := fun g =>
    mem_center_iff.mp ((zpowers_le.mpr h.uc) hz) g
  have hcalc : y * z * t * (y * z)⁻¹ * t⁻¹ = y * t * y⁻¹ * t⁻¹ := by
    calc y * z * t * (y * z)⁻¹ * t⁻¹ = y * (z * t) * z⁻¹ * y⁻¹ * t⁻¹ := by group
      _ = y * (t * z) * z⁻¹ * y⁻¹ * t⁻¹ := by rw [← hzc t]
      _ = y * t * y⁻¹ * t⁻¹ := by group
  show y * z * t * (y * z)⁻¹ * t⁻¹ ∈ C
  rw [hcalc]
  exact hle (Subgroup.commutator_mem_commutator hy ht)

theorem rankThreeGamma_ne_top {L : Subgroup X} (T : Sylow p L)
    (hT : (T : Subgroup L).map L.subtype = (R : Subgroup X) ⊓ L)
    (hN : ∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ L → U ≠ ⊥ →
      L ⊓ normalizer (U : Set X) ≤ X₀) (hnle : ¬ L ≤ X₀) :
    rankThreeGamma 1 p (T : Subgroup L) ≠ ⊤ := by
  have hp := h.red.prime
  have hle : rankThreeGamma 1 p (T : Subgroup L) ≤ X₀.comap L.subtype := by
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQ1, rfl⟩ n hn
    change (n : X) ∈ X₀
    obtain ⟨q, hqQ, hqo⟩ := exists_orderOf_eq_of_one_le_pRank' hp hQ1
    have hQmap : Q.map L.subtype ≤ (R : Subgroup X) ⊓ L := hT ▸ Subgroup.map_mono hQT
    have hQne : Q.map L.subtype ≠ ⊥ := by
      intro hbot
      have hq1 : (q : X) = 1 := by
        have : (q : X) ∈ Q.map L.subtype := Subgroup.mem_map_of_mem _ hqQ
        rw [hbot] at this
        exact Subgroup.mem_bot.mp this
      have hq1' : q = 1 := Subtype.ext hq1
      rw [hq1', orderOf_one] at hqo
      exact hp.one_lt.ne hqo
    have hn' : (n : X) ∈ normalizer ((Q.map L.subtype : Subgroup X) : Set X) :=
      Subgroup.le_normalizer_map L.subtype ⟨n, hn, rfl⟩
    exact hN _ hQmap hQne ⟨n.2, hn'⟩
  intro htop
  rw [htop, top_le_iff] at hle
  apply hnle
  intro l hl
  have : (⟨l, hl⟩ : L) ∈ X₀.comap L.subtype := hle ▸ mem_top _
  exact this

theorem commutator_le_of_noncyclic {L : Subgroup X} (hL : IsComponentOf L ⊤) (huL : u ∉ L)
    (hZ : center L = ⊥) (hnle : ¬ L ≤ X₀) (hnc : ¬ IsCyclic ↥((R : Subgroup X) ⊓ L))
    (hBM : NotBM ↥L) (K1 : StronglyEmbeddedRankTwoKFactNoBM) (KF : SignalizerTwoGroupKFact)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hBT : B ≤ normalizer (T : Set X)) :
    ⁅B, T⁆ ≤ centralizer (L : Set X) := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hLn : L.Normal := h.normal_of hL
  obtain ⟨hsimple, hnonab, hcat⟩ := h.simple_nonab_catalog hL hZ
  have hr2 : 2 ≤ CFSG.Open.pRank p ((R : Subgroup X) ⊓ L) :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (R.isPGroup'.to_inf_left) hnc
  have hr : CFSG.Open.pRank p ((R : Subgroup X) ⊓ L) = 2 := le_antisymm (h.pRank_inf_le_two huL) hr2
  set E : Subgroup X := B ⊓ L with hE
  have hEB : E ≤ B := inf_le_left
  have hEL : E ≤ L := inf_le_right
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => h.Be.2 x (hEB hx)⟩
    have hab : (a : X) * b = b * a :=
      congrArg (fun y : B => (y : X)) (h.Be.1.is_comm.comm ⟨a, hEB a.2⟩ ⟨b, hEB b.2⟩)
    exact Subtype.ext hab
  have hEc : Nat.card E = p ^ 2 := by
    obtain ⟨k, hk⟩ :=
      (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hEe).exists_card_eq
    have hk2 : k ≤ 2 := by
      have := le_pRank_of_elemAbelian_card (P := (R : Subgroup X) ⊓ L)
        (le_inf (hEB.trans h.BR) hEL) hEe hk
      omega
    obtain ⟨A, hAR, hA, hAc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
      ((R : Subgroup X) ⊓ L)
    have hAE : A ≤ E := fun x hx => ⟨h.omega x (hAR hx).1 (hA.2 x hx), (hAR hx).2⟩
    have h2k : p ^ 2 ≤ p ^ k := by
      rw [← hk, ← hr, ← hAc]
      exact Subgroup.card_le_of_le hAE
    have hk2' : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp h2k
    rw [hk, show k = 2 by omega]
  have hEC : E ⊓ centralizer (L : Set X) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x ⟨hxE, hxC⟩
    have hxZ : (⟨x, hEL hxE⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  have huE : u ∉ E := fun hu => huL (hEL hu)
  obtain ⟨hN, -⟩ := h.red.rankOne_principle hL hnc h.uR' huL h.uo
    (Subgroup.center_le_centralizer _ h.uc)
  obtain ⟨Tl, hTl⟩ := h.exists_sylow hL
  have hrank : CFSG.Open.pRank p (Tl : Subgroup L) = 2 := by
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype
      L.subtype_injective (Tl : Subgroup L)
    rw [hTl] at hmap
    omega
  have hΓ := h.rankThreeGamma_ne_top Tl hTl hN hnle
  have hSE : IsRankTwoSEGroup p ↥L := K1 L hsimple hnonab hcat hBM p hp h.ne_two Tl hrank hΓ
  have hcomm := KF X L hLn hsimple hnonab hcat p hp h.ne_two E hEe hEc hEC
    (Or.inl ⟨hSE, hEL⟩) T hT (hEB.trans hBT)
  exact h.commutator_le_of_sup (h.eq_sup_zpowers hEB hEc huE) hcomm

theorem normalizer_le_of_ne_bot {Q : Subgroup X} (hQR : Q ≤ (R : Subgroup X)) (hQ1 : Q ≠ ⊥)
    (huQ : u ∉ Q) : normalizer (Q : Set X) ≤ X₀ := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htQ, -, hto⟩ := exists_mem_centralizer_orderOf_eq (R.isPGroup'.to_le hQR) hQ1
  set Q₁ : Subgroup X := omegaOneOf p Q with hQ₁
  have hQ₁B : Q₁ ≤ B := (closure_le _).2 fun x hx => h.omega x (hQR hx.1) hx.2
  have htQ₁ : t ∈ Q₁ := subset_closure ⟨htQ, hto ▸ pow_orderOf_eq_one t⟩
  have hD : Q₁ ⊔ zpowers u ≤ (R : Subgroup X) :=
    sup_le (hQ₁B.trans h.BR) (zpowers_le.mpr h.uR')
  have htu : u ∉ zpowers t := fun hmem => huQ (zpowers_le.mpr htQ hmem)
  have h2 : 2 ≤ CFSG.Open.pRank p (Q₁ ⊔ zpowers u) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp hto (h.uo ▸ pow_orderOf_eq_one u) htu
      (mem_center_iff.mp h.uc t) (mem_sup_left htQ₁) (mem_sup_right (mem_zpowers u))
  exact (normalizer_le_normalizer_omegaOneOf p Q).trans
    ((h.normalizer_le_sup_zpowers Q₁).trans (h.normalizer_le hD h2))

theorem inf_sup_eq {L C : Subgroup X} [L.Normal] [C.Normal] (hLC : Disjoint L C)
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) :
    (R : Subgroup X) ⊓ (L ⊔ C) = (R : Subgroup X) ⊓ L ⊔ (R : Subgroup X) ⊓ C := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hRtop : CFSG.ABGLocalTools.IsSylowOf p (R : Subgroup X) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, R.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact R.not_dvd_index⟩
  have hsN : CFSG.ABGLocalTools.IsSylowOf p ((R : Subgroup X) ⊓ (L ⊔ C)) (L ⊔ C) :=
    hRtop.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top (L ⊔ C)).ge
  have hsL : CFSG.ABGLocalTools.IsSylowOf p ((R : Subgroup X) ⊓ L) L :=
    hRtop.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top L).ge
  have hsC : CFSG.ABGLocalTools.IsSylowOf p ((R : Subgroup X) ⊓ C) C :=
    hRtop.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top C).ge
  have hCnorm : C ≤ normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcardN : Nat.card ↥(L ⊔ C) = Nat.card L * Nat.card C :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L C hCnorm hLC
  have hle : (R : Subgroup X) ⊓ L ⊔ (R : Subgroup X) ⊓ C ≤ (R : Subgroup X) ⊓ (L ⊔ C) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hdisj : Disjoint ((R : Subgroup X) ⊓ L) ((R : Subgroup X) ⊓ C) :=
    hLC.mono inf_le_right inf_le_right
  have hnorm : (R : Subgroup X) ⊓ C ≤ normalizer (((R : Subgroup X) ⊓ L : Subgroup X) : Set X) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact mem_centralizer_iff.mpr fun l hl => hcomm l hl.2 c hc.2
  have hcardP : Nat.card ↥((R : Subgroup X) ⊓ L ⊔ (R : Subgroup X) ⊓ C) =
      Nat.card ↥((R : Subgroup X) ⊓ L) * Nat.card ↥((R : Subgroup X) ⊓ C) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj
  have hcard : Nat.card ↥((R : Subgroup X) ⊓ (L ⊔ C)) =
      Nat.card ↥((R : Subgroup X) ⊓ L) * Nat.card ↥((R : Subgroup X) ⊓ C) := by
    rw [hsN.card_eq, hsL.card_eq, hsC.card_eq, hcardN,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hcard])).symm

theorem exists_mem_not_mem_sup {L : Subgroup X} [L.Normal]
    (hLC : L ⊓ centralizer (L : Set X) = ⊥) (hcycL : IsCyclic ↥((R : Subgroup X) ⊓ L))
    (hcycC : IsCyclic ↥((R : Subgroup X) ⊓ centralizer (L : Set X))) :
    ∃ x ∈ B, x ∉ L ⊔ centralizer (L : Set X) := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  set C : Subgroup X := centralizer (L : Set X) with hCdef
  have hdisj : Disjoint L C := disjoint_iff.mpr hLC
  have hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := fun l hl c hc => mem_centralizer_iff.mp hc l hl
  have hsup := h.inf_sup_eq hdisj hcomm
  have hBle : B ≤ (B ⊓ L) ⊔ (B ⊓ C) := by
    intro b hb
    have hbLC : b ∈ (R : Subgroup X) ⊓ (L ⊔ C) := ⟨h.BR hb, hcon b hb⟩
    rw [hsup] at hbLC
    have hnorm : (R : Subgroup X) ⊓ L ≤
        normalizer (((R : Subgroup X) ⊓ C : Subgroup X) : Set X) := by
      intro l hl
      refine Subgroup.centralizer_le_normalizer _ ?_
      exact mem_centralizer_iff.mpr fun c hc => (hcomm l hl.2 c hc.2).symm
    have hmem : b ∈ (((R : Subgroup X) ⊓ L ⊔ (R : Subgroup X) ⊓ C : Subgroup X) : Set X) := hbLC
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hmem
    obtain ⟨s, hs, c, hc, hsc⟩ := Set.mem_mul.mp hmem
    have hbp : b ^ p = 1 := h.Be.2 b hb
    rw [← hsc, Commute.mul_pow (show Commute s c from hcomm s hs.2 c hc.2)] at hbp
    have hsC : s ^ p ∈ C := by
      have : s ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hbp
      rw [this]
      exact C.inv_mem (C.pow_mem hc.2 p)
    have hsp : s ^ p = 1 := by
      have : s ^ p ∈ L ⊓ C := ⟨L.pow_mem hs.2 p, hsC⟩
      rw [hLC, Subgroup.mem_bot] at this
      exact this
    have hcp : c ^ p = 1 := by rw [hsp, one_mul] at hbp; exact hbp
    rw [← hsc]
    exact Subgroup.mul_mem_sup ⟨h.omega s hs.1 hsp, hs.2⟩ ⟨h.omega c hc.1 hcp, hc.2⟩
  have hnormBL : B ⊓ C ≤ normalizer ((B ⊓ L : Subgroup X) : Set X) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact mem_centralizer_iff.mpr fun l hl => hcomm l hl.2 c hc.2
  have hcard : Nat.card B ≤ Nat.card ↥(B ⊓ L) * Nat.card ↥(B ⊓ C) := by
    rw [← CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormBL
      (hdisj.mono inf_le_right inf_le_right)]
    exact Subgroup.card_le_of_le hBle
  have hBe : ∀ K : Subgroup X, K ≤ B → IsElemAbelian p K := fun K hKB => by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => h.Be.2 x (hKB hx)⟩
    have hab : (a : X) * b = b * a :=
      congrArg (fun y : B => (y : X)) (h.Be.1.is_comm.comm ⟨a, hKB a.2⟩ ⟨b, hKB b.2⟩)
    exact Subtype.ext hab
  have h1 : Nat.card ↥(B ⊓ L) ≤ p := by
    have := hcycL
    exact card_le_of_isElemAbelian_of_le_cyclic hp.pos (hBe _ inf_le_left)
      (inf_le_inf_right _ h.BR)
  have h2 : Nat.card ↥(B ⊓ C) ≤ p := by
    have := hcycC
    exact card_le_of_isElemAbelian_of_le_cyclic hp.pos (hBe _ inf_le_left)
      (inf_le_inf_right _ h.BR)
  have h3 : p ^ 3 ≤ p * p := by
    rw [← h.Bc]
    exact hcard.trans (Nat.mul_le_mul h1 h2)
  have h4 : p * p < p ^ 3 := by
    have := hp.one_lt
    calc p * p = p ^ 2 := (sq p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
  omega

theorem isSylowOf_top : CFSG.ABGLocalTools.IsSylowOf p (R : Subgroup X) ⊤ := by
  have : Fact p.Prime := ⟨h.red.prime⟩
  exact CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, R.isPGroup', by
    rw [Subgroup.relIndex_top_right]
    exact R.not_dvd_index⟩

theorem isElemAbelian_of_le {K : Subgroup X} (hKB : K ≤ B) : IsElemAbelian p K := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => h.Be.2 x (hKB hx)⟩
  have hab : (a : X) * b = b * a :=
    congrArg (fun y : B => (y : X)) (h.Be.1.is_comm.comm ⟨a, hKB a.2⟩ ⟨b, hKB b.2⟩)
  exact Subtype.ext hab

theorem isSylowOf_inf_sup_zpowers {L : Subgroup X} [L.Normal] {x : X}
    (hxR : x ∈ (R : Subgroup X)) (hxo : orderOf x = p) (hxL : x ∉ L) :
    CFSG.ABGLocalTools.IsSylowOf p ((R : Subgroup X) ⊓ (L ⊔ zpowers x)) (L ⊔ zpowers x) := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hsL : CFSG.ABGLocalTools.IsSylowOf p ((R : Subgroup X) ⊓ L) L :=
    h.isSylowOf_top.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top L).ge
  have hLE : zpowers x ≤ normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have heq : (R : Subgroup X) ⊓ (L ⊔ zpowers x) = (R : Subgroup X) ⊓ L ⊔ zpowers x := by
    apply le_antisymm
    · rintro y ⟨hyR, hyX⟩
      have hyX' : y ∈ ((zpowers x ⊔ L : Subgroup X) : Set X) := by
        rw [sup_comm]
        exact hyX
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE] at hyX'
      obtain ⟨z, hz, l, hl, hzl⟩ := Set.mem_mul.mp hyX'
      have hzR : z ∈ (R : Subgroup X) := (zpowers_le.mpr hxR) hz
      have hlR : l ∈ (R : Subgroup X) := by
        have : l = z⁻¹ * y := by rw [← hzl]; group
        rw [this]
        exact (R : Subgroup X).mul_mem ((R : Subgroup X).inv_mem hzR) hyR
      rw [← hzl, sup_comm]
      exact Subgroup.mul_mem_sup hz (Subgroup.mem_inf.mpr ⟨hlR, hl⟩)
    · exact sup_le (inf_le_inf_left _ le_sup_left)
        (zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxR, mem_sup_right (mem_zpowers x)⟩))
  have hnorm : zpowers x ≤ normalizer (((R : Subgroup X) ⊓ L : Subgroup X) : Set X) :=
    (le_inf (zpowers_le.mpr (Subgroup.le_normalizer hxR)) hLE).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hdisj : Disjoint ((R : Subgroup X) ⊓ L) (zpowers x) :=
    disjoint_zpowers_of_not_mem hp hxo (fun hx => hxL (Subgroup.mem_inf.mp hx).2)
  have hcard : Nat.card ↥((R : Subgroup X) ⊓ (L ⊔ zpowers x)) =
      Nat.card ↥((R : Subgroup X) ⊓ L) * p := by
    rw [heq, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      Nat.card_zpowers, hxo]
  refine CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right ?_
  rw [hcard, hsL.card_eq, card_sup_zpowers_of_normal hp hxo hxL,
    Nat.factorization_mul Nat.card_pos.ne' hp.ne_zero, Finsupp.add_apply, hp.factorization_self,
    pow_add, pow_one]

theorem commutator_le_of_cyclic {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (hZ : center L = ⊥) (hnle : ¬ L ≤ X₀) (hcyc : IsCyclic ↥((R : Subgroup X) ⊓ L))
    (K2 : StronglyEmbeddedCyclicOuterKFact) (KF : SignalizerTwoGroupKFact)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hBT : B ≤ normalizer (T : Set X)) :
    ⁅B, T⁆ ≤ centralizer (L : Set X) := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hLn : L.Normal := h.normal_of hL
  obtain ⟨hsimple, hnonab, hcat⟩ := h.simple_nonab_catalog hL hZ
  set C : Subgroup X := centralizer (L : Set X) with hCdef
  have hLC : L ⊓ C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro y ⟨hyL, hyC⟩
    have hyZ : (⟨y, hyL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp hyC g g.2)
    rw [hZ, mem_bot] at hyZ
    exact congrArg Subtype.val hyZ
  have hCcyc : IsCyclic ↥((R : Subgroup X) ⊓ C) := h.isCyclic_inf_centralizer hnle
  have huC : u ∈ C := Subgroup.center_le_centralizer _ h.uc
  obtain ⟨t₀, ⟨ht₀R, ht₀L⟩, ht₀o, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.red.core_eq_bot R hL
  have ht₀B : t₀ ∈ B := h.omega t₀ ht₀R (ht₀o ▸ pow_orderOf_eq_one t₀)
  obtain ⟨x, hxB, hxLC⟩ := h.exists_mem_not_mem_sup hLC hcyc hCcyc
  have hxL : x ∉ L := fun hx => hxLC (Subgroup.mem_sup_left hx)
  have hxp : x ^ p = 1 := h.Be.2 x hxB
  have hxo : orderOf x = p := orderOf_eq_prime hxp (fun hx1 => hxL (hx1 ▸ L.one_mem))
  have hxR : x ∈ (R : Subgroup X) := h.BR hxB
  set X₂ : Subgroup X := L ⊔ zpowers x with hX₂
  have hLX₂ : L ≤ X₂ := le_sup_left
  have hX₂C : X₂ ⊓ C = ⊥ := sup_zpowers_inf_centralizer_eq_bot hp hxo hLC hxLC
  have huX₂ : u ∉ X₂ := by
    intro hu
    have : u ∈ X₂ ⊓ C := ⟨hu, huC⟩
    rw [hX₂C, mem_bot] at this
    have h1 := h.uo
    rw [this, orderOf_one] at h1
    exact hp.one_lt.ne h1
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : Sylow p ↥X₂,
      (P₂ : Subgroup ↥X₂).map X₂.subtype = (R : Subgroup X) ⊓ X₂ :=
    h.isSylowOf_inf_sup_zpowers (L := L) hxR hxo hxL
  set D : Subgroup X := zpowers t₀ ⊔ zpowers x with hD
  have hDB : D ≤ B := sup_le (zpowers_le.mpr ht₀B) (zpowers_le.mpr hxB)
  have hDX₂ : D ≤ X₂ := sup_le ((zpowers_le.mpr ht₀L).trans hLX₂) (le_sup_right)
  have hxt₀ : x ∉ zpowers t₀ := fun hx => hxL ((zpowers_le.mpr ht₀L) hx)
  have hDc : Nat.card D = p ^ 2 := by
    have := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers t₀) hxp hxt₀
      (fun e he => congrArg Subtype.val
        (h.Be.1.is_comm.comm ⟨e, (zpowers_le.mpr ht₀B) he⟩ ⟨x, hxB⟩))
    rw [Nat.card_zpowers, ht₀o] at this
    rw [hD, this, sq]
  have hDe : IsElemAbelian p D := h.isElemAbelian_of_le hDB
  have huD : u ∉ D := fun hu => huX₂ (hDX₂ hu)
  have hDC : D ⊓ C = ⊥ := le_bot_iff.mp (hX₂C ▸ inf_le_inf_right _ hDX₂)
  have e : ↥(L.subgroupOf X₂) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX₂
  have : IsSimpleGroup ↥(L.subgroupOf X₂) := e.isSimpleGroup
  have hnonab' : ∃ a b : ↥(L.subgroupOf X₂), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat' : IsCatalogGroup ↥(L.subgroupOf X₂) := IsCatalogGroup.of_mulEquiv e hcat
  have hcent : Subgroup.centralizer ((L.subgroupOf X₂ : Subgroup ↥X₂) : Set ↥X₂) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyC : (y : X) ∈ C := by
      rw [hCdef]
      refine mem_centralizer_iff.mpr fun l hl => ?_
      have := mem_centralizer_iff.mp hy ⟨l, hLX₂ hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
      exact congrArg Subtype.val this
    have : (y : X) ∈ X₂ ⊓ C := ⟨y.2, hyC⟩
    rw [hX₂C, mem_bot] at this
    exact Subtype.ext this
  have hcycP : IsCyclic ↥((P₂ : Subgroup ↥X₂) ⊓ L.subgroupOf X₂) := by
    have := hcyc
    let f : ↥((P₂ : Subgroup ↥X₂) ⊓ L.subgroupOf X₂) →* ↥((R : Subgroup X) ⊓ L) :=
      (((X₂.subtype).comp (Subgroup.subtype _)).codRestrict ((R : Subgroup X) ⊓ L) (fun y => by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have hy1 : (y : ↥X₂) ∈ (P₂ : Subgroup ↥X₂) := y.2.1
          have : ((y : ↥X₂) : X) ∈ (P₂ : Subgroup ↥X₂).map X₂.subtype := ⟨_, hy1, rfl⟩
          rw [hP₂] at this
          exact (Subgroup.mem_inf.mp this).1
        · exact y.2.2))
    refine isCyclic_of_injective f (fun a b hab => ?_)
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥((R : Subgroup X) ⊓ L) => (z : X)) hab))
  have hrk : 2 ≤ CFSG.Open.pRank p (P₂ : Subgroup ↥X₂) := by
    have h1 : 2 ≤ CFSG.Open.pRank p D := le_pRank_of_elemAbelian_card le_rfl hDe hDc
    have h2 : CFSG.Open.pRank p D ≤ CFSG.Open.pRank p ((R : Subgroup X) ⊓ X₂) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf (hDB.trans h.BR) hDX₂)
    have h3 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp X₂.subtype
      X₂.subtype_injective (P₂ : Subgroup ↥X₂)
    rw [hP₂] at h3
    omega
  have hΓ : rankThreeGamma 1 p (P₂ : Subgroup ↥X₂) ≠ ⊤ := by
    have hle : rankThreeGamma 1 p (P₂ : Subgroup ↥X₂) ≤ X₀.comap X₂.subtype := by
      refine sSup_le ?_
      rintro N ⟨Q, hQT, hQ1, rfl⟩ n hn
      change (n : X) ∈ X₀
      obtain ⟨q, hqQ, hqo⟩ := exists_orderOf_eq_of_one_le_pRank' hp hQ1
      have hQmap : Q.map X₂.subtype ≤ (R : Subgroup X) ⊓ X₂ := by
        rw [← hP₂]
        exact Subgroup.map_mono hQT
      have hQne : Q.map X₂.subtype ≠ ⊥ := by
        intro hbot
        have hq1 : (q : X) = 1 := by
          have : (q : X) ∈ Q.map X₂.subtype := Subgroup.mem_map_of_mem _ hqQ
          rw [hbot] at this
          exact Subgroup.mem_bot.mp this
        have hq1' : q = 1 := Subtype.ext hq1
        rw [hq1', orderOf_one] at hqo
        exact hp.one_lt.ne hqo
      have huQ : u ∉ Q.map X₂.subtype := fun hu => huX₂ (hQmap hu).2
      have hn' : (n : X) ∈ normalizer ((Q.map X₂.subtype : Subgroup X) : Set X) :=
        Subgroup.le_normalizer_map X₂.subtype ⟨n, hn, rfl⟩
      exact h.normalizer_le_of_ne_bot (hQmap.trans inf_le_left) hQne huQ hn'
    intro htop
    rw [htop, top_le_iff] at hle
    apply hnle
    intro l hl
    have : (⟨l, hLX₂ hl⟩ : ↥X₂) ∈ X₀.comap X₂.subtype := hle ▸ mem_top _
    exact this
  have hiso := K2 ↥X₂ (L.subgroupOf X₂) inferInstance inferInstance hnonab' hcat' hcent p hp
    h.ne_two P₂ hcycP hrk hΓ
  have hiso' : (p = 3 ∧ IsoLie ↥L (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)) ∨
      (p = 5 ∧ IsoLie ↥L (.suzuki 2)) := by
    rcases hiso with ⟨h3, hl⟩ | ⟨h5, hl⟩
    · exact Or.inl ⟨h3, isoLie_of_mulEquiv e hl⟩
    · exact Or.inr ⟨h5, isoLie_of_mulEquiv e hl⟩
  have hcomm := KF X L hLn hsimple hnonab hcat p hp h.ne_two D hDe hDc hDC
    (Or.inr hiso') T hT (hDB.trans hBT)
  exact h.commutator_le_of_sup (h.eq_sup_zpowers hDB hDc huD) hcomm

theorem commutator_eq_bot (hBM : ∀ L : Subgroup X, IsComponentOf L ⊤ → center L = ⊥ → NotBM ↥L)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (KF : SignalizerTwoGroupKFact) {T : Subgroup X} (hT : IsPGroup 2 T)
    (hBT : B ≤ normalizer (T : Set X)) : ⁅B, T⁆ = ⊥ := by
  have hp := h.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL⟩ := h.exists_isComponentOf
  obtain ⟨huL, hZ⟩ := h.not_mem_and_center_eq_bot hL
  have hLn := h.normal_of hL
  have hnle := h.not_le_X₀ hL huL
  have hle : ⁅B, T⁆ ≤ centralizer (L : Set X) := by
    by_cases hcyc : IsCyclic ↥((R : Subgroup X) ⊓ L)
    · exact h.commutator_le_of_cyclic hL hZ hnle hcyc K2 KF hT hBT
    · exact h.commutator_le_of_noncyclic hL huL hZ hnle hcyc (hBM L hL hZ) K1 KF hT hBT
  exact commutator_eq_bot_of_le_centralizer h.ne_two h.red.core_eq_bot hL hLn hZ
    (fun L' hL' => h.red.eq_of_isComponentOf_of_center h.uc h.uo hL' hL)
    (h.red.isCyclic_pCore_of_component hL) (fun b hb => h.Be.2 b hb) hT hBT hle

end NoncentralReduced

end CFSG.LocalAnalysis.RankThreeTheoremC
