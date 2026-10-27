module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8T
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Set

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S1248

namespace S1248

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V U : Subgroup G} {z : G}

open CFSG.Quasithin.Vol2.Ch11.SecA (quotPCore_subgroupOf_equiv pRank_subgroupOf_eq
  map_oPrimeResidualOf_top)

theorem Facts.comp_type_core_F4
    (hF : Facts G T L V U z) (hinv : InvolFact1248_F4) (h68 : E6.E68Stmt)
    (hlist : Lemma115_3_List) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hKF : KnownFacts15122Types) (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact)
    (hKG3 : HatA67Fact1248) {W : Subgroup G} (hW : W = U ∨ (W ≤ U ∧ W.relIndex U = 2))
    {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (W : Set G)) (hX3 : Nat.card X = 3)
    (hXW : X ⊓ Subgroup.centralizer (W : Set G) = ⊥) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer (W : Set G))) :
    IsSimpleGroup ↥K ∧ ∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1 := by
  classical
  have hyp := hF.setting.cx.hyp
  have := hyp.simple
  have hΓ := hF.mem_gamma_F4 hinv hW
  have hV : CFSG.Open.IsElemAbelian 2 V := hF.cx.isElemAbelian
  have hV2 : IsPGroup 2 V := hyp.sylow.1.to_le hF.cx.le_T
  have hWV : W ≤ V := hΓ.1
  obtain ⟨-, hcase⟩ := h68 G T (Subgroup.normalizer (L : Set G)) V W K hV hF.e61 hΓ hK

  have hKMV : K ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.centralizer (V : Set G) := by
    intro k hk
    have : k ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨hk.2, hK.1 hk.1⟩
    rw [hF.inf_centralizer_eq_F4 hinv hW] at this
    exact this.2
  have hautI : Nat.card (autI hV (K ⊓ Subgroup.normalizer (L : Set G))) = 1 := by
    have h0 : autOn (K ⊓ Subgroup.normalizer (L : Set G)) V = ⊥ :=
      C1Pack5.autOn_eq_bot_of_le_centralizer hKMV
    have h1 : Nat.card (autI hV (K ⊓ Subgroup.normalizer (L : Set G))) =
        Nat.card (autOn (K ⊓ Subgroup.normalizer (L : Set G)) V) := rfl
    rw [h1, h0, Subgroup.card_bot]

  have hmW : E3.mQuot V W ≤ 2 := by
    have h1 := E3.relIndex_eq_two_pow hV2 W
    have h2 : W.relIndex V ≤ 4 := by
      rcases hW with rfl | ⟨h, h2⟩
      · rw [hF.setting.hyper]; norm_num
      · rw [← Subgroup.relIndex_mul_relIndex W U V h hF.setting.le, h2, hF.setting.hyper]
    rw [h1] at h2
    by_contra hlt
    push Not at hlt
    have : 2 ^ 3 ≤ 2 ^ E3.mQuot V W := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hSQ : SQTKGroup ↥(Subgroup.normalizer (W : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian
      (pCoreOf_normalizer_ne_bot (hV2.to_le hWV) hΓ.2.1)
  have hKc := mem_cComp_normalizer_of_isComponentIn hK
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hKW : K ≤ Subgroup.centralizer (W : Set G) := hK.1
  have h115 := hF.lemma115Hyp_F4 hinv hW
  have hcases := (Lemma115_3_List.component_cases hlist hyp.simple hyp.nonabelian
    (qtkeCore_of_cat hyp.nonabelian hyp.qtke) h115 hK).2.2.2

  have hexcl : ∀ {S : Type} [Group S] [Finite S], (↥K ≃* S) → A318Exclusion S → False :=
    fun e hS => by
      have := hS.simple
      exact false_of_exclusion hF318 h36 h38 hSQ hKc hKW hKq e.isSimpleGroup e hS hXN hX3 hXW
  rcases hcase with ⟨n, hmod, hZ, -, -, hcard, -, -, -⟩ | ⟨n, hn1, hmod, hmq, -, hab⟩ |
      ⟨hpsl4, -⟩ | ⟨hmod4, -⟩ | ⟨hmod5, -⟩
  ·
    rw [hautI] at hcard
    have hn : n = 1 := by
      have h2 : 2 ^ n = 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) (show 2 ^ n = 2 ^ 1 by rw [h2, pow_one])
    subst hn
    have hpsl : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K)
        .PSL 3 2 1 := by
      rcases hmod with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · omega
      · exact h
      · omega
    have hZ1 := hKG1 G K z hKq hpsl hZ hcases
    have hs := isSimpleGroup_of_center_eq_bot hKq hZ1
    have eK : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm
    have h32 : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 3 2 1 :=
      IsPSL.of_mulEquiv eK.symm hpsl
    refine ⟨hs, 7, ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩,
      Vol2Native.statedClassicalModel_psl_two_seven_of_three_two h32⟩
  ·
    have hn : n = 1 := by
      rcases hab with ⟨-, ⟨h2n, -⟩ | ⟨h1, -⟩⟩ | ⟨-, -, -, -, hcyc⟩
      · omega
      · exact h1
      · by_contra hne
        have := (hcyc (by omega)).2
        rw [hautI] at this
        have h2 : 2 ^ n = 2 := by omega
        exact hne (Nat.pow_right_injective (le_refl 2) (show 2 ^ n = 2 ^ 1 by rw [h2, pow_one]))
    subst hn
    rcases hmod with ⟨h, -⟩ | ⟨-, he⟩
    · omega
    · obtain ⟨e⟩ := he
      exact (hexcl e hKF.alt6).elim
  ·
    exact (hexcl (MulEquiv.refl ↥K) (hKF.l42 ↥K hpsl4)).elim
  ·
    rcases hmod4 with he | ⟨hZ3, h6⟩ | ⟨hZ3, h7⟩
    · obtain ⟨e⟩ := he
      exact (hexcl e hKF.alt7).elim
    · obtain ⟨hr, hn⟩ := hKG3 ↥K hKq hZ3 (Or.inl h6)
      exact (false_of_hat hF318 h36 h38 hSQ hKc hKW hKq hZ3 hr (fun s q => (hn s q).1)
        (fun s q => (hn s q).2) hXN hX3 hXW).elim
    · obtain ⟨hr, hn⟩ := hKG3 ↥K hKq hZ3 (Or.inr h7)
      exact (false_of_hat hF318 h36 h38 hSQ hKc hKW hKq hZ3 hr (fun s q => (hn s q).1)
        (fun s q => (hn s q).2) hXN hX3 hXW).elim
  ·
    rcases hmod5 with ⟨p, hp, hpsl⟩ | h33 | he
    · have hLie : LieModel ↥K .PSL 2 p 1 := Or.inl ⟨by decide, hpsl⟩
      exact ⟨CFSG.Timmesfeld.isSimpleGroup_of_lieModel hLie, p, hp, hpsl⟩
    · exact (hexcl (MulEquiv.refl ↥K) (hKG2 ↥K h33)).elim
    · exact (hexcl (MulEquiv.refl ↥K) (hKF.m11 ↥K he)).elim

theorem Facts.comp_basic_F4 (hF : Facts G T L V U z) (hinv : InvolFact1248_F4) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer (U : Set G))) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) ∧ V ⊓ Subgroup.centralizer (K : Set G) = U := by
  have h115 := hF.lemma115Hyp_F4 hinv (Or.inl rfl)
  have hKM : ¬ K ≤ Subgroup.normalizer (L : Set G) := (h115.component_action hK).2.2.1
  refine ⟨hKM, ?_⟩
  set W := V ⊓ Subgroup.centralizer (K : Set G) with hW
  have hUW : U ≤ W := fun u hu => ⟨hF.setting.le hu, Subgroup.mem_centralizer_iff.2 fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hK.1 hk) u hu).symm⟩
  have hWV : W ≤ V := inf_le_left
  have hWne : W ≠ V := by
    intro h
    apply hKM
    rw [← hF.normalizer_V_eq]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff, ← h]
    exact inf_le_right
  have hmul := Subgroup.relIndex_mul_relIndex U W V hUW hWV
  rw [hF.setting.hyper] at hmul
  have hWV2 : W.relIndex V ≠ 1 := fun h1 => hWne (le_antisymm hWV (Subgroup.relIndex_eq_one.1 h1))
  have hUW1 : U.relIndex W = 1 := by
    have h0 : W.relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases Nat.lt_or_ge (W.relIndex V) 2 with h | h
    · omega
    · nlinarith [Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite : U.relIndex W ≠ 0)]
  exact (le_antisymm (Subgroup.relIndex_eq_one.1 hUW1) hUW)

end S1248

open S1248

theorem comp1248Type_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hpre : Pre1242_F4) (hinv : InvolFact1248_F4) (hX : HypX1248_F4) (h68 : E6.E68Stmt)
    (hlist : Lemma115_3_List) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hKF : KnownFacts15122Types) (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact)
    (hKG3 : HatA67Fact1248) (hKG4 : L2pThreeFact1248) : Comp1248Type_F4 := by
  intro G _ _ T L V U hS K hK
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hF⟩ := S1248.exists_facts_F4 h331 h1222 h323 h3228 hpre hS
  have hyp := hS.cx.hyp
  have hev : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
  have hΓ := hF.mem_gamma_F4 hinv (Or.inl rfl)
  have hU2 : IsPGroup 2 U := (hyp.sylow.1.to_le hF.cx.le_T).to_le hS.le

  obtain ⟨X, hXN, hX3, hXW⟩ : ∃ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) ∧
      Nat.card X = 3 ∧ X ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
    rcases hX G T L V U hS with ⟨X, hXle, hX3, hXU, -⟩ | ⟨Y, hYle, hY27, -, hYU⟩
    · refine ⟨X, hXle.trans inf_le_right, hX3, ?_⟩
      have hd : Nat.card ↥(X ⊓ Subgroup.centralizer (U : Set G)) ∣ 3 :=
        hX3 ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact Subgroup.card_eq_one.1 h1
      · exfalso
        apply hXU
        have heq : X ⊓ Subgroup.centralizer (U : Set G) = X :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hX3])
        rw [← heq]
        exact inf_le_right
    · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 (by rw [hY27]; norm_num)
      refine ⟨Subgroup.zpowers (y : G), (Subgroup.zpowers_le.2 y.2).trans
        (hYle.trans inf_le_right), by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy], ?_⟩
      refine le_bot_iff.1 ?_
      calc Subgroup.zpowers (y : G) ⊓ Subgroup.centralizer (U : Set G) ≤
          Y ⊓ Subgroup.centralizer (U : Set G) := inf_le_inf_right _ (Subgroup.zpowers_le.2 y.2)
        _ = ⊥ := hYU
  obtain ⟨hKs, hKp⟩ := hF.comp_type_core_F4 hinv h68 hlist hF318 h36 h38 hKF hKG1 hKG2 hKG3
    (Or.inl rfl) hXN hX3 hXW hK
  obtain ⟨hKM, hCV⟩ := hF.comp_basic_F4 hinv hK
  refine ⟨?_, hKs, hKp, hKM, hCV⟩
  rintro ⟨Y, hYle, hY27, hY3, hYU⟩
  obtain ⟨p, hp, hpsl⟩ := hKp
  exact false_of_Y hev hU2 hΓ.2.1 (hYle.trans inf_le_right) hY27 hY3 hYU hK.1
    (hKG4 ↥K p hp hpsl).1

end CFSG.Quasithin.H13
