module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddNat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Timmesfeld.Orders
  CFSG.Timmesfeld.ClassicalOrders
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem exists_natural_of_odd_F4 (hIrr : IrrPlusBaseNonempty) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5_F4) (h3228 : Stmt3_2_2_eight) (h513 : Stmt5_1_3_F4) (h5114 : Stmt5_1_14_first_F4)
    (hn : Odd n) :
    ∃ V₀ : Subgroup G, IsCh5Module T L V₀ ∧ IsNatModCh5 L V₀ n ∧ V₀ ≤ T ∧
      T ≤ Subgroup.normalizer (V₀ : Set G) ∧ IsTISetUnder V₀ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hn1 : 1 ≤ n := by obtain ⟨j, rfl⟩ := hn; omega
  have hL0 : conjClosure L T = L := hh.conjClosure_eq
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.2

  obtain ⟨I, hI⟩ := hIrr G T L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maximal hh.faithful
    hh.isQuasisimple hh.T_le_normalizer
  obtain ⟨-, -, h323I⟩ := h323 G T L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maximal
    hh.faithful hh.isQuasisimple
  rw [hL0] at h323I
  obtain ⟨V₀, hV₀, -, hfsu⟩ := h323I I hI
  obtain ⟨hV₀R, hV₀ne, hLV₀, hV₀L, -, hV₀irr, -⟩ := hV₀
  have hne₀ : ¬ L ≤ Subgroup.centralizer (V₀ : Set G) := by
    intro hc
    apply hV₀ne
    rw [← hV₀L]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (Subgroup.le_centralizer_iff.mp hc)

  have hVR : conjClosure V₀ T ≤ reducedAggregate (L ⊔ T) :=
    Hyp5_1_14.conjClosure_le_reducedAggregate hV₀R
  have hLV : L ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    le_normalizer_conjClosure_of_le hh.T_le_normalizer hLV₀
  have hneV : ¬ L ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV := hh.card_autOn_L hLV hVR hneV

  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL0.symm
  have hcase : V₀ = conjClosure V₀ T ∧ IsTISetUnder V₀ M := by
    rcases hcases with ⟨h1, h1'⟩ | ⟨h1, -, -, -, hTI⟩ | ⟨-, hlist, -⟩
    · refine ⟨h1, fun g hg hgV => absurd ?_ hgV⟩
      rw [h1, h1']
      exact le_normalizer_conjClosure _ _ (hh.normal hg)
    · exact ⟨h1, fun g hg hgV => hTI g (hh.normal hg) hgV⟩
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact card_SL3_ne_L2_odd hF hn1 ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · exact card_statedSp_ne_L2_odd hF hn ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_alt 6 (by norm_num)] at h1
        exact L2_odd_ne_360 hn1 (h1.symm.trans (by norm_num [Nat.factorial]))
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_SL4_two] at h1
        exact L2_odd_ne_20160 hn h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_SL5_two] at h1
        exact L2_odd_ne_9999360 hn h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [L34Orders.card_alt 7 (by norm_num)] at h1
        exact L2_odd_ne_2520 hn1 (h1.symm.trans (by norm_num [Nat.factorial]))
  obtain ⟨hVeq, hTI⟩ := hcase

  obtain ⟨hVLT, hred, -⟩ := h3228 G T L V₀ hfsu
  rw [hL0, ← hVeq] at hVLT hred
  have hmod : IsCh5Module T L V₀ := ⟨hVLT, hred, fun hb => hV₀ne (by rw [← hV₀L]; exact hb)⟩
  have hV₀T : V₀ ≤ T := by
    obtain ⟨-, -, hRO, -⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.reducedAggregate_props (L ⊔ T)
    exact hV₀R.trans (hRO.trans (pCoreOf_le_of_isSylowTwoOf (hh.isSylowTwoOf le_sup_right)))
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T

  have hCV : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := hh.inf_centralizer_eq_bot hV₀R hTV₀ hZL
  have hirr : ∀ J : Subgroup G, J ≤ V₀ → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = V₀ := by
    intro J hJ hLJ
    have := hV₀irr J (by rw [hCV]; exact bot_le) hJ hLJ
    rwa [hCV] at this
  refine ⟨V₀, hmod, ?_, hV₀T, hTV₀, hTI⟩

  rcases h513 G T M L V₀ n hh hmod with ⟨W₁, W₂, hW₁, hW₂, h12, h12s, hN1, hN2⟩ | ⟨rfl, -⟩ |
      hnat | ⟨m, hm, -⟩ | ⟨-, ⟨e⟩, -⟩
  ·
    exfalso
    have hW₁V : W₁ = V₀ := (hirr W₁ (h12s ▸ le_sup_left) hW₁).resolve_left hN1.ne_bot
    have hW₂V : W₂ = V₀ := (hirr W₂ (h12s ▸ le_sup_right) hW₂).resolve_left hN2.ne_bot
    rw [hW₁V, hW₂V, inf_idem] at h12
    exact hV₀ne h12
  · exact absurd hn (by decide)
  ·
    have hsub : (Subgroup.centralizer (L : Set G)).subgroupOf V₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ V₀ ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
      rw [hCV, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    rw [hV₀L] at hnat
    obtain ⟨hLV', hc, hb⟩ := hnat
    rw [hsub] at hb
    exact ⟨hLV', hc, hb⟩
  · exact absurd hn (by rw [hm, Nat.not_odd_iff_even]; exact even_two_mul m)
  ·
    exfalso
    have hcard₀ := hh.card_autOn_L hLV₀ hV₀R hne₀
    have : Finite ↥(autOn (L ⊔ T) V₀) := Finite.of_equiv _ e.toEquiv.symm
    have hle := Subgroup.card_le_of_le (A4.autOn_mono (V := V₀) (le_sup_left : L ≤ L ⊔ T))
    rw [hcard₀, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hle
    have hn3 : 3 ≤ n := by
      obtain ⟨j, rfl⟩ := hn
      have := hh.two_le
      omega
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 h63
    norm_num [Nat.factorial] at hle
    omega

end Hyp5_1_14

end CFSG.Quasithin.H13
