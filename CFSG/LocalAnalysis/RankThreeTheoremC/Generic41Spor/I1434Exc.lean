module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Defs
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcPlaneSzTits
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc

open CFSG.Open (IsElemAbelian)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open Polynomial


@[expose] def RankNotThree (X : Type) [Group X] : Prop :=
  (∀ E : Subgroup X, IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 3) ∨
    ∃ (E : Subgroup X) (k : ℕ), 4 ≤ k ∧ IsElemAbelian 5 E ∧ Nat.card E = 5 ^ k

theorem rankNotThree_of_rankLE2 {X : Type} [Group X] (h : RankLE2 5 X) : RankNotThree X :=
  Or.inl fun E hE hc => by
    have := h E hE
    rw [hc] at this
    norm_num at this

theorem rankNotThree_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : RankNotThree X) : RankNotThree Y := by
  rcases h with h | ⟨E, k, hk, hE, hc⟩
  · refine Or.inl fun E hE hc => h (E.map e.symm.toMonoidHom)
      (CFSG.SectionRank.isElemAbelian_map hE _) ?_
    rw [Subgroup.card_map_of_injective e.symm.injective, hc]
  · refine Or.inr ⟨E.map e.toMonoidHom, k, hk, CFSG.SectionRank.isElemAbelian_map hE _, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hc]

theorem pRank_ne_three_of_rankNotThree {X : Type} [Group X] [Finite X] (h : RankNotThree X)
    (Q : Sylow 5 X) : CFSG.Open.pRank 5 (Q : Subgroup X) ≠ 3 := by
  intro hQ
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases h with h | ⟨E, k, hk, hE, hc⟩
  · obtain ⟨E, -, hE, hc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) (Q : Subgroup X)
    rw [hQ] at hc
    exact h E hE hc
  · have hEp : IsPGroup 5 E := IsPGroup.of_card hc
    obtain ⟨P, hP⟩ := hEp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
    have hgQ : ((g • P : Sylow 5 X) : Subgroup X) =
        (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hle : E.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) := by
      rw [← hg, hgQ]
      exact Subgroup.map_mono hP
    have hk3 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) hle
      (CFSG.SectionRank.isElemAbelian_map hE _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc])
    omega

theorem orderOf_five_cases {q : ℕ} (hq : ¬ 5 ∣ q) :
    orderOf (q : ZMod 5) = 1 ∨ orderOf (q : ZMod 5) = 2 ∨ orderOf (q : ZMod 5) = 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hq0 : (q : ZMod 5) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q 5).1 h)
  have h4 : orderOf (q : ZMod 5) ∣ 4 := ZMod.orderOf_dvd_card_sub_one hq0
  obtain ⟨e, he⟩ : ∃ e, orderOf (q : ZMod 5) = e := ⟨_, rfl⟩
  rw [he] at h4 ⊢
  have hle : e ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases e
  all_goals first
    | exact absurd h4 (by decide)
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)

theorem not_five_dvd_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ5 : ℓ ≠ 5) : ¬ 5 ∣ ℓ ^ f := fun h =>
  hℓ5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hℓ).1 (Nat.prime_five.dvd_of_dvd_pow h)).symm

theorem not_five_dvd_CFSG.Open.ordG2_three_pow {f : ℕ} (hf : Odd f) : ¬ 5 ∣ CFSG.Open.ordG2 (3 ^ f) := by
  obtain ⟨a, rfl⟩ := hf
  have h2 : (3 ^ (2 * a + 1)) ^ 2 % 5 = 4 := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add, pow_mul, Nat.mul_mod,
      Nat.pow_mod]
    norm_num
  generalize 3 ^ (2 * a + 1) = q at h2
  have h6 : q ^ 6 % 5 = 4 := by
    rw [show q ^ 6 = (q ^ 2) ^ 3 by ring, Nat.pow_mod, h2]
  have hq6 : 1 ≤ q ^ 6 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · norm_num at h2
    · exact Nat.one_le_pow _ _ hq
  have hq2 : 1 ≤ q ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · norm_num at h2
    · exact Nat.one_le_pow _ _ hq
  have e1 : (q ^ 6 - 1) % 5 = 3 := by omega
  have e2 : (q ^ 2 - 1) % 5 = 3 := by omega
  intro h
  have h0 : CFSG.Open.ordG2 q % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  unfold CFSG.Open.ordG2 at h0
  rw [Nat.mul_mod, Nat.mul_mod (q ^ 6), h6, e1, e2] at h0
  norm_num at h0

theorem not_five_cube_dvd_CFSG.Open.ordF4_two : ¬ 5 ^ 3 ∣ CFSG.Open.ordF4 2 := by
  unfold CFSG.Open.ordF4
  norm_num

theorem card_derivedCentralQuotient_dvd {M : Type} [Group M] {H A : Subgroup M} (hHA : H ≤ A) :
    Nat.card (DerivedCentralQuotient H) ∣ Nat.card A := by
  have h1 : Nat.card (DerivedCentralQuotient H) ∣ Nat.card ↥⁅H, H⁆ :=
    Subgroup.card_quotient_dvd_card _
  have hle : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  exact h1.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_dvd_of_le hHA))

section Families



theorem exists_mulEquiv_adjointGroup {X : Type} [Group X] {τ : Tag} {q : ℕ}
    (h : UntwistedChevalleyModel X τ q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (X ≃* ↥(adjointGroup τ F)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hZ : Subgroup.center ↥(adjointGroup τ F) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem rankNotThree_G2 (F : Type) [Field F] [Finite F] (hF : ¬ 5 ∣ Nat.card F) :
    RankNotThree ↥(adjointGroup .G2 F) :=
  rankNotThree_of_rankLE2 (rankLE2_adjointGroup_G2 F Nat.prime_five le_rfl hF)

theorem rankNotThree_F4 (F : Type) [Field F] [Finite F] (hF : ¬ 5 ∣ Nat.card F) :
    RankNotThree ↥(adjointGroup .F4 F) := by
  rcases orderOf_five_cases hF with he | he | he
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_one F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 4, le_rfl, hE, hc⟩
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_two F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 4, le_rfl, hE, hc⟩
  · refine rankNotThree_of_rankLE2 (rankLE2_adjointGroup_F4 F Nat.prime_five (by norm_num) hF ?_)
    intro h
    have := (dvd_pow_sub_one_iff_orderOf Nat.card_pos he).1 h
    omega

theorem rankNotThree_E6 (F : Type) [Field F] [Finite F] (hF : ¬ 5 ∣ Nat.card F) :
    RankNotThree ↥(adjointGroup .E6 F) := by
  rcases orderOf_five_cases hF with he | he | he
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_one F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 6, by norm_num, hE, hc⟩
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_two F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 4, le_rfl, hE, hc⟩
  · exact rankNotThree_of_rankLE2 (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_E6_of_degCount_eq_two
      F Nat.prime_five (by rw [he]; decide))

theorem rankNotThree_E7 (F : Type) [Field F] [Finite F] (hF : ¬ 5 ∣ Nat.card F) :
    RankNotThree ↥(adjointGroup .E7 F) := by
  rcases orderOf_five_cases hF with he | he | he
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_one F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 7, by norm_num, hE, hc⟩
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_two F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 7, by norm_num, hE, hc⟩
  · exact rankNotThree_of_rankLE2 (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_E7_of_degCount_eq_two
      F Nat.prime_five (by rw [he]; decide))

theorem rankNotThree_E8 (F : Type) [Field F] [Finite F] (hF : ¬ 5 ∣ Nat.card F) :
    RankNotThree ↥(adjointGroup .E8 F) := by
  rcases orderOf_five_cases hF with he | he | he
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_one F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 8, by norm_num, hE, hc⟩
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_two F Nat.prime_five (by norm_num) he
    exact Or.inr ⟨E, 8, by norm_num, hE, hc⟩
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_four F Nat.prime_five he
    exact Or.inr ⟨E, 4, le_rfl, hE, hc⟩

theorem rankNotThree_twistedE6 {X : Type} [Group X] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hℓ5 : ℓ ≠ 5) (h : TwistedChevalleyModel X .E6 (ℓ ^ f)) : RankNotThree X := by
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hℓ hf h
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, (RingEquiv.ofBijective σ hbij) c = c ^ (ℓ ^ f) := hσ
  have e' : ↥(twistedE6RootGroup F (RingEquiv.ofBijective σ hbij)) ≃* X := e
  refine rankNotThree_of_mulEquiv e' ?_
  rcases orderOf_five_cases (not_five_dvd_pow (f := f) hℓ hℓ5) with he | he | he
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_one hℓ hf F hF _ hσ' Nat.prime_five
      (by norm_num) he
    exact Or.inr ⟨E, 4, le_rfl, hE, hc⟩
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_two hℓ hf F hF _ hσ' Nat.prime_five
      (by norm_num) he
    exact Or.inr ⟨E, 6, by norm_num, hE, hc⟩
  · exact rankNotThree_of_rankLE2
      ((sylowTorus_twistedE6_four hℓ hf F hF _ hσ' Nat.prime_five he).rankLE2 Nat.prime_five le_rfl)

theorem rankNotThree_trialityD4 {X : Type} [Group X] [Finite X] {ℓ f : ℕ}
    (hmc : ChevalleyExceptionalModel X .trialityD4 ℓ f) (hℓ5 : ℓ ≠ 5) : RankNotThree X := by
  have hℓ : ℓ.Prime := hmc.1.1
  have hf : 1 ≤ f := hmc.1.2.1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h : TwistedChevalleyModel X .D4 (ℓ ^ f) := hmc.2
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hℓ hf h
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, (RingEquiv.ofBijective σ hbij) c = c ^ (ℓ ^ f) := hσ
  have e' : ↥(graphFixedRootGroup TwistTag.D4 F (RingEquiv.ofBijective σ hbij).toRingHom) ≃* X := e
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  refine rankNotThree_of_rankLE2 (RankLE2.of_mulEquiv e' ?_)
  by_cases hdvd : 5 ∣ Nat.card (graphFixedRootGroup TwistTag.D4 F (RingEquiv.ofBijective σ hbij).toRingHom)
  · have hdvd' : 5 ∣ Nat.card X := by rwa [← Nat.card_congr e'.toEquiv]
    obtain ⟨m, hm, hd⟩ := ((CFSG.RankThree.Chevalley.exact_E_type_and_triality_cross_prime_factor_exhaustion
      Nat.prime_five (by norm_num) hℓ5 hmc).1 hdvd').2.2.2.2 rfl
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    by_cases h12 : m = 12
    · subst h12
      have h24 : (ℓ ^ f) ^ 2 ≤ (ℓ ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
      have h1 : ((5 : ℕ) : ℤ) ∣ (((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        simpa only [CFSG.RankThree.Chevalley.exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X,
          eval_one, Nat.cast_pow, Nat.cast_ofNat] using hd
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_pRank_le_one Nat.prime_five
        (CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve hℓ hf F hF _ hσ' Nat.prime_five le_rfl
          (Int.natCast_dvd_natCast.1 h1))
    · have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_sylowShape Nat.prime_five
        (CFSG.RankThree.PartOne.K128.sylowShape_D4 hf F hF _ hσ' hm' Nat.prime_five le_rfl
          (CFSG.RankThree.PartOne.K128.dvd_phiNat_of_dvd_cycloVal hq1 hm' hd))
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_not_dvd Nat.prime_five hdvd

theorem rankNotThree_suzuki {X : Type} [Group X] [Finite X] {ℓ f : ℕ} (h : SuzukiModel X ℓ f) :
    RankNotThree X := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : X ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  exact rankNotThree_of_rankLE2 (rankLE2_of_oddSylow_cyclic Nat.prime_five (by norm_num)
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic a ha hF' e'))

theorem rankNotThree_reeG2 {X : Type} [Group X] [Finite X] {ℓ f : ℕ}
    (h : ReeTitsModel X .twistedG2 ℓ f) : RankNotThree X := by
  obtain ⟨⟨-, -, -, rfl, hodd, -⟩, a, -, F, _, _, hF, ⟨e⟩⟩ := h
  have hdvd : Nat.card X ∣ CFSG.Open.ordG2 (3 ^ f) := by
    rw [Nat.card_congr e.toEquiv, ← hF,
      ← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
    exact card_derivedCentralQuotient_dvd inf_le_left
  refine Or.inl fun E _ hc => not_five_dvd_CFSG.Open.ordG2_three_pow hodd ?_
  exact (dvd_pow_self 5 (by norm_num : 3 ≠ 0)).trans
    (hc ▸ (Subgroup.card_subgroup_dvd_card E).trans hdvd)

theorem rankNotThree_reeF4 {X : Type} [Group X] [Finite X] {ℓ f : ℕ}
    (h : ReeTitsModel X .twistedF4 ℓ f) : RankNotThree X := by
  have hℓ2 : ℓ = 2 := h.1.2.2.2.1
  subst hℓ2
  exact Or.inl fun E hE hc =>
    CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five h Nat.prime_five le_rfl hE.2 hc

theorem rankNotThree_tits {X : Type} [Group X] [Finite X] {ℓ f : ℕ}
    (h : ReeTitsModel X .Tits ℓ f) : RankNotThree X := by
  obtain ⟨⟨-, -, -, rfl, rfl⟩, a, -, F, _, _, hF, ⟨e⟩⟩ := h
  have hdvd : Nat.card X ∣ CFSG.Open.ordF4 2 := by
    rw [Nat.card_congr e.toEquiv, show (2 : ℕ) = 2 ^ 1 from rfl, ← hF,
      ← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    exact card_derivedCentralQuotient_dvd inf_le_left
  exact Or.inl fun E _ hc => not_five_cube_dvd_CFSG.Open.ordF4_two
    (hc ▸ (Subgroup.card_subgroup_dvd_card E).trans hdvd)

theorem i1434ExcCase_holds : I1434ExcCase := by
  intro K _ _ t ℓ f ht hmodel hℓ5 Q _
  refine pRank_ne_three_of_rankNotThree ?_ Q
  have hℓ : ℓ.Prime := hmodel.admissible.1
  have hf : 1 ≤ f := hmodel.admissible.2.1
  have h5 : ¬ 5 ∣ ℓ ^ f := not_five_dvd_pow hℓ hℓ5
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup hm
    exact rankNotThree_of_mulEquiv e.symm (rankNotThree_G2 F (hF ▸ h5))
  · obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup hm
    exact rankNotThree_of_mulEquiv e.symm (rankNotThree_F4 F (hF ▸ h5))
  · obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup hm
    exact rankNotThree_of_mulEquiv e.symm (rankNotThree_E6 F (hF ▸ h5))
  · obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup hm
    exact rankNotThree_of_mulEquiv e.symm (rankNotThree_E7 F (hF ▸ h5))
  · obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup hm
    exact rankNotThree_of_mulEquiv e.symm (rankNotThree_E8 F (hF ▸ h5))
  · obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact rankNotThree_twistedE6 hℓ hf hℓ5 hm
  · exact rankNotThree_trialityD4
      (hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])) hℓ5
  · rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hm⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact rankNotThree_suzuki hm
  · obtain ⟨-, hm⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
    exact rankNotThree_reeG2 hm
  · obtain ⟨-, hm⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
    exact rankNotThree_reeF4 hm
  · obtain ⟨-, hm⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
    exact rankNotThree_tits hm

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc
