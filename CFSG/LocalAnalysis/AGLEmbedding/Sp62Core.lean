module

public import CFSG.LocalAnalysis.AGLEmbedding.G28MSide
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4DataAux
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Key

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_perfect_of_isPGroup {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {B : Subgroup Y} (hB : IsPGroup p B) (hBB : ⁅B, B⁆ = B) : B = ⊥ := by
  rcases Subgroup.bot_or_nontrivial B with hbot | hnt
  · exact hbot
  · have : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hBB
    exact absurd hB.isNilpotent (Group.IsPerfect.not_isNilpotent B)

omit [Finite G] in
theorem le_pCoreOf_of_barM_eq_bot {M V : Subgroup G} (hVM : V ≤ M) (hbot : barM M V = ⊥) :
    V ≤ pCoreOf 2 M := by
  intro v hv
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hVM hv⟩ ∈ barM M V :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact coe_mem_pCoreOf_two_of_mk_eq_one _ hmem

theorem not_dvd_card_center_of_normal {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {Lb : Subgroup Y} [Lb.Normal] (hO : CFSG.pCore p Y = ⊥) :
    ¬ p ∣ Nat.card (Subgroup.center Lb) := by
  intro hdvd
  set Zb := (Subgroup.center Lb).map Lb.subtype with hZb
  have hZn : Zb.Normal := inferInstance
  have hcomm : IsMulCommutative Zb := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, -, rfl⟩
    have e : (a : Y) * b = b * a := by
      have := congrArg (Subtype.val : Lb → Y) (Subgroup.mem_center_iff.mp ha b).symm
      simpa using this
    exact Subtype.ext e
  have hc : Nat.card Zb = Nat.card (Subgroup.center Lb) :=
    Subgroup.card_map_of_injective Lb.subtype_injective
  obtain ⟨Q⟩ : Nonempty (Sylow p Zb) := inferInstance
  have hle := Sylow.map_le_pCore hZn inferInstance p Q
  rw [hO] at hle
  apply Q.ne_bot_of_dvd_card (hc ▸ hdvd)
  rw [eq_bot_iff]
  intro x hx
  have : (x : Y) ∈ (⊥ : Subgroup Y) := hle ⟨x, hx, rfl⟩
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))

end Generic

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Sp62Facts

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V : Subgroup G}

theorem D1Sp62Data.pCore_eq_bot (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hO
  obtain ⟨hVV, hVK, hVN, -⟩ := h.piece
  have hVM : V ≤ M := hVK.trans inf_le_right
  have hVY : V ≤ pCorePreimage 3 M :=
    (h.dichotomy _ (h3.pCorePreimage_le_inf h84 hD2)
      (inf_le_right.trans (le_normalizer_pCorePreimage 3 M))).resolve_left
      (h3.pCorePreimage_not_le hO)
  have hVO : barM M V ≤ CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    rintro _ ⟨⟨v, hvM⟩, hv, rfl⟩
    obtain ⟨m, hm, hmv⟩ := hVY (Subgroup.mem_subgroupOf.mp hv)
    have : m = ⟨v, hvM⟩ := Subtype.ext hmv
    subst this
    exact hm
  have hbot : barM M V = ⊥ :=
    eq_bot_of_perfect_of_isPGroup (CFSG.pCore_isPGroup.to_le hVO) (barM_perfect hVM hVV)
  exact hVN ((le_pCoreOf_of_barM_eq_bot hVM hbot).trans h3.twoCore_M_le_glbPrimeCore)

theorem D1Sp62Data.R_le_Pi (h : D1Sp62Data P M H R V) (hB3 : StmtBlockThree) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : R ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L :=
  le_inf h.surv.ph3.le_inf (h.surv.le_blockClosure rfl hL (hB3 h.surv.ph3 hL))

theorem D1Sp62Data.card_sylow (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∀ Q : Sylow 3 (blockParabolic M (pCoreOf 2 H) L),
      Nat.card (Q : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3 ^ 4 := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set PL := blockParabolic M (pCoreOf 2 H) L with hPL
  intro Q
  have hXM : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ M := inf_le_right.trans hL.le
  have hXH : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H := fun x hx =>
    (hKeq ▸ ⟨hL.le hx.2, hx.1⟩ : x ∈ H ⊓ M).1
  have hPLH : Nat.card PL ∣ Nat.card H :=
    (card_barM_dvd hXM).trans (Subgroup.card_dvd_of_le hXH)
  have hRPL : barM M R ≤ PL := h.barM_le h84 h86 hD2 hB3 hb hL (h.R_le_Pi hB3 hL)
  have hcR : Nat.card (barM M R) = 3 ^ 4 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) h3.le_M h3.isPGroup_R, h.card_R]
  have h81 : 3 ^ 4 ∣ Nat.card PL := hcR ▸ Subgroup.card_dvd_of_le hRPL
  have hge : 3 ^ 4 ∣ Nat.card (Q : Subgroup PL) := Q.pow_dvd_card_of_pow_dvd_card h81
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hQH : 3 ^ n ∣ Nat.card H := hn ▸ (Subgroup.card_subgroup_dvd_card _).trans hPLH
  have hRH : CFSG.ABGLocalTools.IsSylowOf 3 R H := h3.isSylow
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hRH
  obtain ⟨hRle, -, hidx⟩ := hRH
  have hmul := Subgroup.relIndex_mul_relIndex ⊥ R H bot_le hRle
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, h.card_R] at hmul
  rw [← hmul] at hQH
  have hc : Nat.Coprime (3 ^ n) (R.relIndex H) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx)
  have hle : 3 ^ n ∣ 3 ^ 4 := hc.dvd_of_dvd_mul_right hQH
  rw [hn] at hge ⊢
  exact Nat.dvd_antisymm hle hge

end Sp62Facts

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Sp62Index

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V : Subgroup G}

theorem D1Sp62Data.blockParabolic_eq (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    blockParabolic M (pCoreOf 2 H) L = barM M ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) :=
  le_antisymm (blockParabolic_le_barM h.surv.ph3.inf_eq_inf_normalizer_twoCore hL.le le_rfl)
    (h.barM_le h84 h86 hD2 hB3 hb hL le_rfl)

theorem D1Sp62Data.relIndex_le (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (barM M V ⊔ barM M (((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) ⊓ GLBPrimeCore 3 H)).relIndex
      (blockParabolic M (pCoreOf 2 H) L) ≤ 2 := by
  obtain ⟨-, -, -, -, hidx, -⟩ := h.piece
  set Pi := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hPi
  set N := GLBPrimeCore 3 H with hN
  have hVPi := h.le_Pi hB3 hL
  have hPiK : Pi ≤ H ⊓ M := inf_le_left
  have hPiH : Pi ≤ H := hPiK.trans inf_le_left
  have hPiM : Pi ≤ M := hPiK.trans inf_le_right
  rw [barM_sup_eq hVPi hPiH hPiM, h.blockParabolic_eq h84 h86 hD2 hB3 hb hL]
  have hd : (barM M (Pi ⊓ (V ⊔ N))).relIndex (barM M Pi) ∣ (V ⊔ N).relIndex Pi := by
    have h1 := relIndex_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
      (Subgroup.comap_mono (inf_le_left : Pi ⊓ (V ⊔ N) ≤ Pi) :
        (Pi ⊓ (V ⊔ N)).subgroupOf M ≤ Pi.subgroupOf M)
    have h2 : ((Pi ⊓ (V ⊔ N)).subgroupOf M).relIndex (Pi.subgroupOf M) =
        (V ⊔ N).relIndex Pi := by
      rw [Subgroup.relIndex_subgroupOf hPiM, Subgroup.inf_relIndex_left]
    rw [← h2]
    exact h1
  have hne1 : (V ⊔ N).relIndex Pi ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hne2 : (V ⊔ N).relIndex (H ⊓ M) ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  calc _ ≤ (V ⊔ N).relIndex Pi := Nat.le_of_dvd (Nat.pos_of_ne_zero hne1) hd
    _ ≤ (V ⊔ N).relIndex (H ⊓ M) := Subgroup.relIndex_le_of_le_right hPiK hne2
    _ ≤ 2 := hidx

end Sp62Index

end CFSG.AGLEmbedding
