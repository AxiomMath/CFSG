module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5W1618p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

local notation "StSL" => Assembly.LowTwoRank.StatedSL

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem rankOneAt_plus_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F)) :
    RankOneAt (S.plus K) (autOn S.Tv (S.WK K) ⊓ S.plus K) := by
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hNH := S.HK_le_normalizer_plus_F4 h1222 h517 hF hK hT
  have hTvHK : IsSylowTwoOf (autOn S.Tv (S.WK K)) (autOn (S.HK K) (S.WK K)) :=
    Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hK.1) hHKW
  have hQsyl : IsSylowTwoOf (autOn S.Tv (S.WK K) ⊓ S.plus K) (S.plus K) :=
    A4.isSylowTwoOf_inf_normal hTvHK (A4.autOn_mono hKHK) hNH
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  have hsimp : IsSimpleGroup ↥(S.plus K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo hF4.ge) e
  have h60 : Nat.card ↥(S.plus K) = 60 := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
    norm_num
  obtain ⟨e₅⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := ↥(S.plus K)) h60
  have hR5 : IsRankOneSylow ↥(S.plus K) :=
    CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType (.linear 2 le_rfl e₅)
  have hp2 : CFSG.Open.pCore 2 ↥(S.plus K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 ↥(S.plus K)) with h | h
    · exact h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥(S.plus K)) :=
        CFSG.LieType.BorelTits.pCore_isPGroup 2
      rw [h] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
      rw [Subgroup.card_top, h60] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have hq : oTwoQuot ↥(S.plus K) ≃* ↥(S.plus K) :=
    (QuotientGroup.quotientMulEquivOfEq hp2).trans QuotientGroup.quotientBot
  exact F1.rankOneAt_of_isRankOneSylow hQsyl (hR5.of_mulEquiv hq.symm)

theorem exists_minParabolic_of_sl2_four_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F)) :
    ∃ K₀ M : Subgroup G, K₀ ≤ K ∧ K₀ ∈ lFamily S.Tv ∧
      S.Tv ≤ Subgroup.normalizer (K₀ : Set G) ∧ autOn K₀ (S.WK K) = S.plus K ∧
      MinParabolic (K₀ ⊔ S.Tv) S.Tv M := by
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hK hT
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hKHK.trans hHKW
  have hTW : S.Tv ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (S.Tv_le_HK K).trans hHKW
  have hNH := S.HK_le_normalizer_plus_F4 h1222 h517 hF hK hT
  have hKp : ⁅K, K⁆ = K := perfect_of_mem_cComp hK.2.1

  have hTsyl : IsSylowTwoOf S.Tv (K ⊔ S.Tv) := by
    have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
    refine ⟨le_sup_right, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
    have hrel := Subgroup.relIndex_mul_relIndex S.Tv (K ⊔ S.Tv) _ le_sup_right
      (sup_le hK.1 S.Tv_le_Gv)
    have h' : 2 ∣ S.Tv.relIndex (K ⊔ S.Tv) := h2
    have h3 : 2 ∣ S.Tv.relIndex (Subgroup.centralizer ({S.v12} : Set G)) :=
      hrel ▸ dvd_mul_of_dvd_left h' _
    exact h3

  have hker : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
    have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) K := by
      refine A3.subnormal_of_normal inf_le_left ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro k hk
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, mem_normalizer_centralizer_of_mem_normalizer (hKW hk)⟩
    have hlt : K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) < K := by
      refine lt_of_le_of_ne inf_le_left fun h => (qs_perfect_ne_bot hq).2 ?_
      rw [show S.plus K = autOn K (S.WK K) from rfl, autOn_eq_bot_iff hKW]
      intro k hk
      rw [← h] at hk
      exact hk.2
    have hle := le_solvRad_of_subnormal_lt hK.2.1 hsub hlt
    have := solvRad_isSolvable K
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hQ : autOn K (S.WK K) ∈ cComp (autOn K (S.WK K)) := mem_cComp_self_of_isQuasisimple hq

  have hTvN : autOn S.Tv (S.WK K) ≤
      Subgroup.normalizer ((S.plus K : Subgroup (MulAut ↥(S.WK K))) : Set (MulAut ↥(S.WK K))) :=
    (A4.autOn_mono (S.Tv_le_HK K)).trans hNH
  have hR1 := S.rankOneAt_plus_F4 h1222 h517 hF hK hT hF4 e
  have hsup : autOn (K ⊔ S.Tv) (S.WK K) = S.plus K ⊔ autOn S.Tv (S.WK K) := autOn_sup hKW hTW
  have hM := isUniqueMaxOver_borelOf_sup hR1 hTvN
  have hnn := not_le_normalizer_of_rankOneAt hR1
  rw [← hsup] at hM hnn
  obtain ⟨K₀, hmin, hmp⟩ := exists_minParabolic_member hKp hKW hTW hT hTsyl hker hQ hM hnn
  exact ⟨K₀, _, hmin.1.1, hmin.1.2.1, hmin.1.2.2.1, hmin.1.2.2.2, hmp⟩

end Setting

end CFSG.Quasithin.H13.A5
