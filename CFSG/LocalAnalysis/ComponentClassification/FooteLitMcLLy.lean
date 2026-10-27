module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadicBase

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn map_centralizer_subtype)
open scoped commutatorElement

theorem centralizer_conj_eq {Y : Type*} [Group Y] (r c : Y) :
    (centralizer ({r} : Set Y)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * r * c⁻¹} : Set Y) := by
  ext x
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc c * y * c⁻¹ * (c * r * c⁻¹) = c * (y * r) * c⁻¹ := by group
      _ = c * (r * y) * c⁻¹ := by rw [hy]
      _ = c * r * c⁻¹ * (c * y * c⁻¹) := by group
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, by group⟩
    calc c⁻¹ * x * c * r = c⁻¹ * (x * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * x) * c := by rw [hx]
      _ = r * (c⁻¹ * x * c) := by group

theorem isQuasisimple_centralizer_conj {Y : Type*} [Group Y] {r : Y}
    (h : Open.IsQuasisimple ↥(centralizer ({r} : Set Y))) (c : Y) :
    Open.IsQuasisimple ↥(centralizer ({c * r * c⁻¹} : Set Y)) := by
  have e := ((centralizer ({r} : Set Y)).equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr (centralizer_conj_eq r c))
  exact ClassicalInvolution.isQuasisimple_of_mulEquiv e h

theorem isQuasisimple_centralizer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {x : X} (h : Open.IsQuasisimple ↥(centralizer ({e x} : Set Y))) :
    Open.IsQuasisimple ↥(centralizer ({x} : Set X)) := by
  have hmap : (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
    ext y
    simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  have e' := ((centralizer ({x} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)
  exact ClassicalInvolution.isQuasisimple_of_mulEquiv e'.symm h

theorem isQuasisimple_centralizer_of_mulEquiv_all {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ y : Y, orderOf y = 2 → Open.IsQuasisimple ↥(centralizer ({y} : Set Y))) (x : X)
    (hx : orderOf x = 2) : Open.IsQuasisimple ↥(centralizer ({x} : Set X)) :=
  isQuasisimple_centralizer_of_mulEquiv e (h _ (by rw [MulEquiv.orderOf_eq]; exact hx))

theorem isQuasisimple_centralizer_of_sylow_cover {M : Type} [Group M] (H : Subgroup M) [Finite H]
    (S : Subgroup M) (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {r : M}
    (hr : r ∈ H) (hSr : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * r * c⁻¹) {K : Subgroup M}
    (hK : centralizerIn H r = K) (hq : Open.IsQuasisimple K) (y : H) (hy : orderOf y = 2) :
    Open.IsQuasisimple ↥(centralizer ({y} : Set H)) := by
  have hr' : Open.IsQuasisimple ↥(centralizer ({(⟨r, hr⟩ : H)} : Set H)) :=
    ClassicalInvolution.isQuasisimple_of_mulEquiv (HSFLit.centralizerEquivIn H hr hK).symm hq
  obtain ⟨c, hc, hyc⟩ := ClassicalInvolution.cover_of_sylow H S hS hidx r hSr y y.2
    (by rw [Subgroup.orderOf_coe]; exact hy)
  have e : y = ⟨c, hc⟩ * ⟨r, hr⟩ * (⟨c, hc⟩ : H)⁻¹ := Subtype.ext (by simp [hyc])
  rw [e]
  exact isQuasisimple_centralizer_conj hr' _

theorem isQuasisimple_centralizer_McL :
    ∀ y : Blueprint.NativeSporadic.McL, orderOf y = 2 →
      Open.IsQuasisimple ↥(centralizer ({y} : Set Blueprint.NativeSporadic.McL)) := by
  refine isQuasisimple_centralizer_of_mulEquiv_all (Y := ↥ClassicalInvolution.McLProof.P) ?e ?_
  case e => exact ClassicalInvolution.McLProof.mclEquivP
  have hP := ClassicalInvolution.McLProof.card_P
  have hS2 : IsPGroup 2 ClassicalInvolution.McLProof.S :=
    IsPGroup.of_card (n := 7) (by rw [ClassicalInvolution.McLProof.card_S]; norm_num)
  exact isQuasisimple_centralizer_of_sylow_cover _ _ hS2
    (ClassicalInvolution.McLProof.S_index_odd hP) ClassicalInvolution.McLProof.pa_mem
    ClassicalInvolution.McLProof.cover_S (ClassicalInvolution.McLProof.centralizerIn_P hP)
    ClassicalInvolution.McLProof.K_quasisimple.1

theorem isQuasisimple_centralizer_Ly :
    ∀ y : Blueprint.NativeSporadic.Ly, orderOf y = 2 →
      Open.IsQuasisimple ↥(centralizer ({y} : Set Blueprint.NativeSporadic.Ly)) := by
  refine isQuasisimple_centralizer_of_mulEquiv_all (Y := ↥CFSG.Sporadic.Ly.J) ?e ?_
  case e => exact CFSG.Sporadic.Ly.lyEquivJ
  intro y hy
  obtain ⟨hCK, hq, -, -⟩ := ClassicalInvolution.LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := ClassicalInvolution.LyProof.S_sylow
  obtain ⟨-, hcover⟩ := ClassicalInvolution.LyProof.S_facts
  have hz : Open.IsQuasisimple
      ↥(centralizer ({ClassicalInvolution.LyProof.zJ} : Set CFSG.Sporadic.Ly.J)) := by
    rw [hCK]
    exact hq
  have hSz : ∀ s ∈ ClassicalInvolution.LyProof.SJ, orderOf s = 2 →
      ∃ c ∈ (⊤ : Subgroup CFSG.Sporadic.Ly.J), s = c * ClassicalInvolution.LyProof.zJ * c⁻¹ := by
    intro s hs hord
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hord, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    obtain ⟨c, hc⟩ := hcover s hs hss hs1
    exact ⟨c, mem_top c, hc⟩
  obtain ⟨c, -, hc⟩ := ClassicalInvolution.cover_of_sylow ⊤ ClassicalInvolution.LyProof.SJ hSp
    hidx ClassicalInvolution.LyProof.zJ hSz y (mem_top _) hy
  rw [hc]
  exact isQuasisimple_centralizer_conj hz c

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_isQuasisimple_centralizer (h : FooteSec4 G L) {M : Subgroup G}
    (hM : IsFooteM L M)
    (hq : ∀ t : G, orderOf t = 2 → Open.IsQuasisimple ↥(centralizer ({t} : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
  obtain ⟨W, hW, hWE⟩ := exists_isKleinFour_le hE2 (by omega)
  obtain ⟨t, htW, ht1, -⟩ := exists_ne_of_isKleinFour hW 1
  have ht : orderOf t = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hW htW) ht1
  have htE := hWE htW
  obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM ht (hEC htE)
  obtain ⟨-, hBt, hBpc⟩ := hBmax.1
  set B := footeF L t with hBdef
  set X := centralizer ({t} : Set G) with hXdef
  set J := B.subgroupOf X with hJdef
  have hXq := hq t ht
  have hcomp : CFSG.IsComponent (⊤ : Subgroup X) := by
    refine ⟨?_, Subgroup.IsSubnormal.top⟩
    have hq' : CFSG.IsQuasisimple X :=
      ⟨⟨hXq.1⟩, hXq.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
        X hXq⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := X)).symm hq'
  have hBperf : ⁅B, B⁆ = B := GSThmB.commutator_eq_self_of_isPComponent hBt hBpc
  obtain ⟨-, -, hJsn, -, -⟩ := hBpc
  have hEX : E ≤ X := fun x hx => mem_centralizer_singleton_iff.mpr
    (commute_of_sq_eq_one hE2 hx htE)
  have hrank := h.hrank2 B hBF
  rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hJsn with htop | hcen
  ·
    have hXB : X ≤ B := fun x hx => by
      have h1 : (⟨x, hx⟩ : X) ∈ J := htop (mem_top _)
      exact h1
    have hEB := hEX.trans hXB
    have hel : Open.IsElemAbelian 2 (E.subgroupOf B) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
      · exact commute_of_sq_eq_one hE2 a.2 b.2
      · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE2 _ ha
    have hcard : Nat.card (E.subgroupOf B) = 2 ^ 3 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hEB).symm.toEquiv, hE8]
      norm_num
    have h3 := SectionRank.le_pRank one_lt_two (le_top : E.subgroupOf B ≤ ⊤) hel hcard
    rw [← SectionRank.pRank_eq_open_pRank_top] at h3
    omega
  ·
    have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
      intro a ha b hb
      have h1 : ⁅(⟨a, hBt ha⟩ : X), (⟨b, hBt hb⟩ : X)⁆ ∈ ⁅(⊤ : Subgroup X), J⁆ :=
        commutator_mem_commutator (mem_top _) (show (⟨b, hBt hb⟩ : X) ∈ J from hb)
      rw [hcen, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact congrArg Subtype.val h1
    have hB1 : B = ⊥ := by
      rw [← hBperf, eq_bot_iff, commutator_le]
      intro a ha b hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)]
      exact one_mem _
    have h0 : CFSG.pRank 2 ↥B = 0 := by
      rw [hB1, SectionRank.pRank_eq_open_pRank_top]
      refine Nat.eq_zero_of_le_zero (SectionRank.pRank_le one_lt_two fun F _ _ => ?_)
      rw [pow_zero]
      exact (Subgroup.card_le_card_group F).trans Subgroup.card_bot.le
    omega

theorem not_mulEquiv_McL (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    (e : G ≃* Blueprint.NativeSporadic.McL) : False :=
  false_of_isQuasisimple_centralizer h hM
    (isQuasisimple_centralizer_of_mulEquiv_all (Y := Blueprint.NativeSporadic.McL) e
      isQuasisimple_centralizer_McL)

theorem not_mulEquiv_Ly (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    (e : G ≃* Blueprint.NativeSporadic.Ly) : False :=
  false_of_isQuasisimple_centralizer h hM
    (isQuasisimple_centralizer_of_mulEquiv_all (Y := Blueprint.NativeSporadic.Ly) e
      isQuasisimple_centralizer_Ly)

end CFSG.ComponentClassification.FooteLit
