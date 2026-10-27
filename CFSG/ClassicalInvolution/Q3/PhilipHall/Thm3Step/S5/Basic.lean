module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S6
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

variable {G : Type} [Group G] [Finite G]

structure S5Hyp (Φ : Set (Subgroup G)) (K : Subgroup G) (Q : Subgroup G) : Prop where
  odd : classicalInvolutionOddCore G = ⊥
  typeR : TypeRHyp Φ
  gen : omegaGen Φ = ⊤
  mem : K ∈ Φ
  viol : ¬ AEmpty Φ K
  normal : Q.Normal
  pgrp : IsPGroup 2 Q
  ne_bot : Q ≠ ⊥
  maxQ : ∀ P : Subgroup G, P.Normal → IsPGroup 2 P → P ≤ Q
  zout : ∀ J ∈ Φ, ∀ z, IsUniqueInvolution J z → z ∉ Q

abbrev barFam (Φ : Set (Subgroup G)) (Q : Subgroup G) [Q.Normal] : Set (Subgroup (G ⧸ Q)) :=
  quotFamily Φ Q

variable {Φ : Set (Subgroup G)} {K Q : Subgroup G}

theorem S5Hyp.inf_eq_bot (h : S5Hyp Φ K Q) {J : Subgroup G} (hJ : J ∈ Φ) : J ⊓ Q = ⊥ := by
  by_contra hne
  obtain ⟨z, hz⟩ := (h.typeR.hyp.omega1 J hJ).1
  exact h.zout J hJ z hz (Subgroup.mem_inf.mp
    (TL4.mem_of_isPGroup_of_ne_bot hz inf_le_left (h.pgrp.to_le inf_le_right) hne)).2

theorem S5Hyp.le_centralizer (h : S5Hyp Φ K Q) {J : Subgroup G} (hJ : J ∈ Φ) :
    J ≤ Subgroup.centralizer (Q : Set G) := by
  obtain ⟨z, hz⟩ := (h.typeR.hyp.omega1 J hJ).1
  exact S6.Hyp.le_centralizer_of_not_mem { toTypeRHyp := h.typeR, odd := h.odd } hJ hz h.normal
    (h.zout J hJ z hz)

theorem S5Hyp.le_center (h : S5Hyp Φ K Q) : Q ≤ Subgroup.center G := by
  have hle : omegaGen Φ ≤ Subgroup.centralizer (Q : Set G) :=
    iSup₂_le fun J hJ => h.le_centralizer hJ
  rw [h.gen] at hle
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) q hq).symm

theorem S5Hyp.iSup_RSet_eq_top (h : S5Hyp Φ K Q) : ⨆ T ∈ RSet Φ, T = ⊤ := by
  rw [eq_top_iff, ← h.gen]
  refine iSup₂_le fun J hJ => ?_
  rw [← S6.Hyp.gen { toTypeRHyp := h.typeR, odd := h.odd } hJ, Subgroup.closure_le]
  rintro x ⟨hxJ, hx2⟩
  obtain ⟨T, hT, -, hxT⟩ := exists_mem_RSet_ge hJ hx2 (Subgroup.zpowers_le.mpr hxJ)
  exact (le_iSup₂_of_le T hT le_rfl : T ≤ ⨆ T ∈ RSet Φ, T) (hxT (Subgroup.mem_zpowers x))

theorem S5Hyp.inf_eq_bot_of_le (h : S5Hyp Φ K Q) {J T : Subgroup G} (hJ : J ∈ Φ) (hTJ : T ≤ J) :
    T ⊓ Q = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right Q hTJ).trans (h.inf_eq_bot hJ).le)

theorem S5Hyp.inf_eq_bot_RSet (h : S5Hyp Φ K Q) {T : Subgroup G} (hT : T ∈ RSet Φ) :
    T ⊓ Q = ⊥ := by
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT
  exact h.inf_eq_bot_of_le hJ hTJ.1

theorem S5Hyp.oddCore_quot (h : S5Hyp Φ K Q) [Q.Normal] :
    classicalInvolutionOddCore (G ⧸ Q) = ⊥ :=
  TwistQ.oddFree h.le_center h.pgrp h.odd

theorem S5Hyp.noNormalTwo_quot (h : S5Hyp Φ K Q) [Q.Normal] : NoNormalTwo (G ⧸ Q) := by
  intro P hP hP2
  have hc : (P.comap (QuotientGroup.mk' Q)).Normal := hP.comap _
  have hc2 : IsPGroup 2 (P.comap (QuotientGroup.mk' Q)) :=
    hP2.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact h.pgrp)
  have hle := h.maxQ _ hc hc2
  rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) P]
  exact (Subgroup.map_mono hle).trans
    (le_of_eq ((Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' Q).ge))

theorem S5Hyp.card_quot_lt (h : S5Hyp Φ K Q) [Q.Normal] : Nat.card (G ⧸ Q) < Nat.card G :=
  TwistQ.card_lt h.ne_bot

theorem S5Hyp.q8 (h : S5Hyp Φ K Q) :
    ∀ L ∈ Φ, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
  intro L hL
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := L) IsPGroup.of_bot bot_le
  exact ⟨P, hP, h.typeR.sylow L hL P hP⟩

theorem S5Hyp.centQuotGen (h : S5Hyp Φ K Q) [Q.Normal] : CentQuotGen Φ Q :=
  TL4.ExitTwo.centQuotGen h.typeR.hyp h.q8 h.le_center fun _ hJ => h.inf_eq_bot hJ

theorem S5Hyp.typeR_quot (h : S5Hyp Φ K Q) [Q.Normal] : TypeRHyp (barFam Φ Q) where
  hyp := h.centQuotGen.hyp'
  twoGroup := TL4.ExitTwo.two_quot_cent h.typeR.twoGroup fun _ hJ => h.inf_eq_bot hJ
  sylow := by
    intro L hL P hP
    obtain ⟨P₀, hP₀, ⟨e⟩⟩ := TL4.ExitTwo.q8_quot_cent h.q8 (fun _ hJ => h.inf_eq_bot hJ) L hL
    exact TL4.ExitTwo.nonempty_equiv_of_isSylow2In hP hP₀ e

theorem S5Hyp.isUniqueInvolution_map (h : S5Hyp Φ K Q) [Q.Normal] {J : Subgroup G} (hJ : J ∈ Φ)
    {z : G} (hz : IsUniqueInvolution J z) :
    IsUniqueInvolution (J.map (QuotientGroup.mk' Q)) (QuotientGroup.mk' Q z) :=
  AscQuot.isUniqueInvolution_map_mk (h.inf_eq_bot hJ) hz

theorem S5Hyp.mk_inj (h : S5Hyp Φ K Q) [Q.Normal] {J : Subgroup G} (hJ : J ∈ Φ) {a b : G}
    (ha : a ∈ J) (hb : b ∈ J) (hab : QuotientGroup.mk' Q a = QuotientGroup.mk' Q b) : a = b :=
  TwistQ.mk_inj (h.inf_eq_bot hJ) ha hb hab

theorem S5Hyp.oddCoreOf_map (h : S5Hyp Φ K Q) [Q.Normal] {J : Subgroup G} (hJ : J ∈ Φ) :
    oddCoreOf (J.map (QuotientGroup.mk' Q)) = (oddCoreOf J).map (QuotientGroup.mk' Q) :=
  oddCoreOf_map_mk_of_odd (by rw [inf_comm, h.inf_eq_bot hJ, Subgroup.card_bot]; exact odd_one)

theorem S5Hyp.eq_of_map_eq (h : S5Hyp Φ K Q) [Q.Normal] {J J' : Subgroup G} (hJ : J ∈ Φ)
    (hJ' : J' ∈ Φ) (he : J.map (QuotientGroup.mk' Q) = J'.map (QuotientGroup.mk' Q)) : J = J' :=
  h.centQuotGen.eq_of_map J hJ J' hJ' he

theorem S5Hyp.natCard_map_sylow (h : S5Hyp Φ K Q) [Q.Normal] {J T : Subgroup G} (hJ : J ∈ Φ)
    (hT : IsSylow2In T J) : Nat.card ↥(T.map (QuotientGroup.mk' Q)) = 8 := by
  rw [← Nat.card_congr (AscQuot.quotRestrictEquiv (h.inf_eq_bot_of_le hJ hT.1)).toEquiv]
  obtain ⟨e⟩ := h.typeR.sylow J hJ T hT
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem S5Hyp.map_eq_of_le (h : S5Hyp Φ K Q) [Q.Normal] {J J' T : Subgroup G} (hJ : J ∈ Φ)
    (hJ' : J' ∈ Φ) (hT : IsSylow2In T J)
    (hle : T.map (QuotientGroup.mk' Q) ≤ J'.map (QuotientGroup.mk' Q)) :
    J.map (QuotientGroup.mk' Q) = J'.map (QuotientGroup.mk' Q) :=
  Sec6Gen.eq_of_le_of_le h.typeR_quot.hyp (map_mem_quotFamily hJ) (map_mem_quotFamily hJ')
    (hT.2.1.map _) (by rw [h.natCard_map_sylow hJ hT]; omega) (Subgroup.map_mono hT.1) hle

theorem S5Hyp.mem_normalizer_map_iff (h : S5Hyp Φ K Q) [Q.Normal] {J : Subgroup G} (hJ : J ∈ Φ)
    {g : G} :
    QuotientGroup.mk' Q g ∈
        Subgroup.normalizer ((J.map (QuotientGroup.mk' Q) : Subgroup (G ⧸ Q)) : Set (G ⧸ Q)) ↔
      g ∈ Subgroup.normalizer (J : Set G) :=
  ⟨fun hg => h.centQuotGen.normalizer_of_map J hJ g hg, mk_mem_normalizer_map⟩

theorem S5Hyp.eq_of_map_le_RSet (h : S5Hyp Φ K Q) [Q.Normal] {T T' : Subgroup G}
    (hT : T ∈ RSet Φ) (hT' : T' ∈ RSet Φ)
    (hle : T.map (QuotientGroup.mk' Q) ≤ T'.map (QuotientGroup.mk' Q)) : T = T' := by
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT
  obtain ⟨J', hJ', hT'J'⟩ := exists_isSylow2In_of_mem_RSet hT'
  have hJJ' : J = J' := h.eq_of_map_eq hJ hJ'
    (h.map_eq_of_le hJ hJ' hTJ (hle.trans (Subgroup.map_mono hT'J'.1)))
  subst hJJ'
  have hTT' : T ≤ T' := by
    intro t ht
    obtain ⟨t', ht', htt'⟩ := hle (Subgroup.mem_map_of_mem _ ht)
    rw [← h.mk_inj hJ (hT'J'.1 ht') (hTJ.1 ht) htt']
    exact ht'
  exact Subgroup.eq_of_le_of_card_ge hTT' (le_of_eq (hT'J'.natCard_eq hTJ))

theorem S5Hyp.eq_of_le_sup_RSet (h : S5Hyp Φ K Q) {T T' : Subgroup G} (hT : T ∈ RSet Φ)
    (hT' : T' ∈ RSet Φ) (hle : T ≤ T' ⊔ Q) : T = T' := by
  haveI := h.normal
  refine h.eq_of_map_le_RSet hT hT' ?_
  rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk']
  exact hle

theorem S5Hyp.conjSub_mem_RSet (h : S5Hyp Φ K Q) {T : Subgroup G} (hT : T ∈ RSet Φ) (g : G) :
    conjSub g T ∈ RSet Φ := by
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT
  exact mem_RSet_of_isSylow2In (h.typeR.hyp.conjInvariant g J hJ)
    (Hall196.isSylow2In_map_hom (MulAut.conj g).toMonoidHom hTJ)

theorem tightInO2_iff_mem_pCore {Y : Type} [Group Y] {z : Y} : TightInO2 z ↔ z ∈ pCore 2 Y :=
  ⟨fun ⟨P, hP, hP2, hz⟩ => (le_sSup ⟨hP, hP2⟩ : P ≤ pCore 2 Y) hz,
    fun hz => ⟨pCore 2 Y, pCore_normal, pCore_isPGroup, hz⟩⟩

section Step

theorem s5Hyp_of_ctx {m : ℕ} {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    {K : Subgroup Y} (hc : Ctx m Y Φ K) (htw : TwinOrbits Φ K)
    (hno : ∀ z : Y, IsUniqueInvolution K z → ¬ TightInO2 z) (hQ : ¬ NoNormalTwo Y) :
    S5Hyp Φ K (pCore 2 Y) where
  odd := hc.odd
  typeR := hc.hyp
  gen := hc.gen
  mem := hc.mem
  viol := hc.notEmpty
  normal := pCore_normal
  pgrp := pCore_isPGroup
  ne_bot := by
    intro hbot
    apply hQ
    intro P hP hP2
    rw [eq_bot_iff, ← hbot]
    exact le_sSup ⟨hP, hP2⟩
  maxQ := fun P hP hP2 => le_sSup ⟨hP, hP2⟩
  zout := by
    intro J hJ u hu huQ
    obtain ⟨g, M, ⟨-, w, hwK, hwM⟩, rfl⟩ := htw J hJ
    have hu' : u = g * w * g⁻¹ := hu.eq (hwM.conj g)
    refine hno w hwK (tightInO2_iff_mem_pCore.mpr ?_)
    have h1 := (pCore_normal (p := 2) (G := Y)).conj_mem u huQ g⁻¹
    have h2 : g⁻¹ * u * g⁻¹⁻¹ = w := by
      rw [hu']
      group
    rwa [h2] at h1

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
