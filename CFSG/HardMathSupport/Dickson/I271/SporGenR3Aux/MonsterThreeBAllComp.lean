module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LargeExtraspecialCases
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeNoComp
public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBIrr

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL tbL_conj QQ_le_tbL card_QQ
  not_three_pow_21_dvd factorization_tbL isAct_b₁ isAct_b₂)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (SylFact)
open CFSG.HardMathSupport.MathTwE6.M3BIrr (irrCheck tbL_dichotomy)
open CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll
open CFSG.HardMathSupport.Solomon.LocalBalance (glaPPrimeCoreOf_le_of_isSubnormal)

theorem prime_dvd_monsterOrder {r : ℕ} (hr : r.Prime) (h : r ∣ CFSG.Open.monsterOrder) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 29 ∨
      r = 31 ∨ r = 41 ∨ r = 47 ∨ r = 59 ∨ r = 71 := by
  have key : ∀ q e : ℕ, q.Prime → r ∣ q ^ e → r = q := fun q e hq hd =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hd)
  have key1 : ∀ q : ℕ, q.Prime → r ∣ q → r = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 hd
  unfold CFSG.Open.monsterOrder at h
  simp only [Nat.Prime.dvd_mul hr, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (key 2 46 Nat.prime_two h)
  · exact Or.inr (Or.inl (key 3 20 Nat.prime_three h))
  · exact Or.inr (Or.inr (Or.inl (key 5 9 (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key 7 6 (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 11 2 (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 13 3 (by norm_num) h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 17 (by norm_num) h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 19 (by norm_num) h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 23 (by norm_num) h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 29 (by norm_num) h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (key1 31 (by norm_num) h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (key1 41 (by norm_num) h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl (key1 47 (by norm_num) h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl (key1 59 (by norm_num) h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (key1 71 (by norm_num) h))))))))))))))

theorem not_pow_ten_dvd_monsterOrder {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    ¬ r ^ 10 ∣ CFSG.Open.monsterOrder := by
  intro hdvd
  have h : r ∣ CFSG.Open.monsterOrder := (dvd_pow_self r (by norm_num)).trans hdvd
  rcases prime_dvd_monsterOrder hr h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | omega
  | (unfold CFSG.Open.monsterOrder at hdvd; norm_num at hdvd)

theorem trivial_of_normal_coprime_of_core_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} (h : GLAPPrimeCoreOf p X = ⊥) :
    ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      Nat.Coprime p (Nat.card N) → N = ⊥ := by
  intro N hNX hXN hcop
  have hn : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have hcop' : Nat.Coprime p (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ GLAPPrimeCore p ↥X := le_sSup ⟨hn, hcop'⟩
  have hN : N ≤ GLAPPrimeCoreOf p X :=
    calc N = (N.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hNX).symm
      _ ≤ GLAPPrimeCoreOf p X := Subgroup.map_mono hle
  rw [h] at hN
  exact le_bot_iff.1 hN

theorem isComponentOf_of_glaPComponent_of_core {G : Type*} [Group G] {p : ℕ} {X L : Subgroup G}
    (hX : GLAPPrimeCoreOf p X = ⊥) (hL : GLAPComponent p X L) : IsComponentOf L X := by
  have hcore : GLAPPrimeCore p ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hX
  refine ⟨hL.1, hL.2.1, ?_⟩
  have hq := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    ((Subgroup.subgroupOfEquivOfLe hL.1).symm.trans
      (Subgroup.equivMapOfInjective (L.subgroupOf X) _ hinj)) hq

theorem dvd_card_of_isComponentOf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X K : Subgroup G} (hX : GLAPPrimeCoreOf p X = ⊥) (hK : IsComponentOf K X) :
    p ∣ Nat.card K := by
  by_contra hnd
  have hcop : Nat.Coprime p (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have htop : (⊤ : Subgroup K) ≤ GLAPPrimeCore p ↥K :=
    le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have hKcore : K ≤ GLAPPrimeCoreOf p K :=
    calc K = (⊤ : Subgroup K).map K.subtype := by rw [Subgroup.map_top, Subgroup.range_subtype]
      _ ≤ GLAPPrimeCoreOf p K := Subgroup.map_mono htop
  have hbot : K ≤ ⊥ := by
    have := hKcore.trans (glaPPrimeCoreOf_le_of_isSubnormal p hK.2.1)
    rwa [hX] at this
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  haveI : Nontrivial K := (QuotientGroup.mk_surjective (s := Subgroup.center K)).nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : K)
  exact hx (Subtype.ext (Subgroup.mem_bot.1 (hbot x.2)))

noncomputable abbrev M3X : Subgroup Gmat := Subgroup.centralizer ({tbw} : Set Gmat)

@[expose] def M3Beta1 (J : Subgroup Gmat) : Prop :=
  IsComponentOf J M3X ∧ 3 ∣ Nat.card J ∧ QQ ≤ Subgroup.normalizer (J : Set Gmat) ∧
    QQ ⊓ (J ⊔ (M3X ⊓ Subgroup.centralizer (J : Set Gmat))) ≤ Subgroup.zpowers tbw ∧
    ¬ 3 ^ 9 ∣ Nat.card ↥(J ⊔ (M3X ⊓ Subgroup.centralizer (J : Set Gmat)))

@[expose] def M3Beta2a (J : Subgroup Gmat) : Prop :=
  IsComponentOf J M3X ∧ QQ ≤ J ∧ (∀ K : Subgroup Gmat, IsComponentOf K M3X → K = J) ∧
    M3X ≤ Subgroup.normalizer (J : Set Gmat) ∧
    M3X ⊓ Subgroup.centralizer (J : Set Gmat) = Subgroup.zpowers tbw ∧
    Nat.card (Subgroup.center J) = 3 ∧ 3 ^ 20 ∣ Nat.card M3X ∧ ¬ 3 ^ 21 ∣ Nat.card M3X

theorem centralizer_zpowers_eq' {G : Type*} [Group G] (w : G) :
    Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) =
      Subgroup.centralizer ({w} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h _ (Subgroup.mem_zpowers _)
  · intro h g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (show Commute w x from h w rfl) n).eq

theorem conj_mem_zpowers' {G : Type*} [Group G] {b w : G} (h : b⁻¹ * w * b ∈ Subgroup.zpowers w) :
    ∀ g ∈ Subgroup.zpowers w, b⁻¹ * g * b ∈ Subgroup.zpowers w := by
  rintro _ ⟨k, rfl⟩
  have e : b⁻¹ * w ^ k * b = (b⁻¹ * w * b) ^ k := by
    have := conj_zpow (a := b⁻¹) (b := w) (i := k)
    rw [inv_inv] at this
    exact this.symm
  simp only
  rw [e]
  exact zpow_mem h k

section Setup

theorem tbL_le_normalizer_zpowers' :
    tbL ≤ Subgroup.normalizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  intro b hb
  refine mem_normalizer_of_conj ?_
  refine conj_mem_of_mem_closure (S := {tbb₁, tbb₂} ∪ Set.range tbq) ?_ hb
  rintro b' ((rfl | rfl) | ⟨j, rfl⟩)
  · refine conj_mem_zpowers' ?_
    have h2 : tbb₁⁻¹ * tbw * tbb₁ = tbw ^ 2 := isAct_b₁.2
    rw [h2]
    exact pow_mem (Subgroup.mem_zpowers _) _
  · refine conj_mem_zpowers' ?_
    have h2 : tbb₂⁻¹ * tbw * tbb₂ = tbw ^ 1 := isAct_b₂.2
    rw [h2]
    exact pow_mem (Subgroup.mem_zpowers _) _
  · refine conj_mem_zpowers' ?_
    have hc := tbCommData.commute_of_mem (Subgroup.subset_closure ⟨j, rfl⟩)
      (Subgroup.mem_zpowers tbw)
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.mem_zpowers _

theorem m3Setup (hsyl : SylFact) (hirr : irrCheck () = true) :
    Setup Gmat 3 tbw QQ tbL M3X 12 20 9 (10 : ℕ).factorial := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have hcardG : Nat.card Gmat = CFSG.Open.monsterOrder :=
    CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have hLQ : tbL ≤ Subgroup.normalizer (QQ : Set Gmat) := fun b hb =>
    mem_normalizer_of_conj (tbL_conj b hb)
  have hrel : (Subgroup.zpowers tbw).relIndex QQ = 3 ^ 12 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers tbw) (K := QQ)
    rw [inf_of_le_left (Subgroup.zpowers_le.2 tbCommData.mem_z), Nat.card_zpowers,
      tbCommData.orderOf_z, card_QQ] at h
    omega
  refine
    { prime := Nat.prime_three
      order_w := ThreeBNF.orderOf_tbw
      hLQ := hLQ
      hLX := ?_
      hQX := ?_
      hwQ := tbCommData.mem_z
      hwX := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx
      hCQ := step0_QQ hsyl
      hdich := fun N hN hnorm => tbL_dichotomy hirr N hN hnorm
      hrel := hrel
      hk := by norm_num
      hm := Nat.factorial_dvd_factorial (by norm_num)
      hr := fun r hr h5 => by
        rw [hcardG]
        exact not_pow_ten_dvd_monsterOrder hr h5
      hb := by norm_num
      hG := by
        rw [hcardG]
        exact not_three_pow_21_dvd }
  · intro b hb
    have h := CFSG.HardMathSupport.MathTwE6.mem_normalizer_centralizer
      (tbL_le_normalizer_zpowers' hb)
    rwa [centralizer_zpowers_eq'] at h
  · intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 ThreeBNF.tbw_mem_centralizer q hq

theorem pow_twenty_dvd_card_M3X (hsyl : SylFact) : 3 ^ 20 ∣ Nat.card M3X := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have h1 : 3 ^ 20 ∣ Nat.card tbL := by
    have := Nat.ordProj_dvd (Nat.card tbL) 3
    rwa [factorization_tbL hsyl] at this
  exact pow_dvd_card_centralizer Nat.prime_three ThreeBNF.orderOf_tbw
    tbL_le_normalizer_zpowers' h1

theorem m3_component_cases (hsyl : SylFact) (hirr : irrCheck () = true)
    (hM3 : OPrimeCoreTrivialAt 3 Gmat) {J : Subgroup Gmat} (hJ : IsComponentOf J M3X) :
    M3Beta1 J ∨ M3Beta2a J := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have S := m3Setup hsyl hirr
  have hX : GLAPPrimeCoreOf 3 M3X = ⊥ := hM3 tbw ThreeBNF.orderOf_tbw
  have hpd : ∀ K : Subgroup Gmat, IsComponentOf K M3X → 3 ∣ Nat.card K := fun K hK =>
    dvd_card_of_isComponentOf Nat.prime_three hX hK
  obtain ⟨hQN, hcase⟩ := component_cases S hJ (hpd J hJ)
  rcases hcase with ⟨hQw, hdvd⟩ | hQJ
  · left
    refine ⟨hJ, hpd J hJ, hQN, hQw, fun h9 => S.hG ?_⟩
    have := (mul_dvd_mul_left (3 ^ 12) h9).trans hdvd
    rwa [← pow_add] at this
  · right
    obtain ⟨huniq, hXN, hCeq, hZ⟩ :=
      beta2a_structure S hJ hQJ hpd (trivial_of_normal_coprime_of_core_eq_bot hX)
    refine ⟨hJ, hQJ, huniq, hXN, hCeq, hZ, pow_twenty_dvd_card_M3X hsyl, fun h => ?_⟩
    exact not_three_pow_21_dvd ((h.trans (Subgroup.card_subgroup_dvd_card M3X)).trans
      (CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder.symm ▸ dvd_rfl))

theorem m3ResBNoComp_of_not_residual (hsyl : SylFact) (hirr : irrCheck () = true)
    (hM3 : OPrimeCoreTrivialAt 3 Gmat) (hR : ¬ ((∃ J, M3Beta1 J) ∨ (∃ J, M3Beta2a
        J))) : M3ResBNoComp := fun J hJ => by
  have hX : GLAPPrimeCoreOf 3 M3X = ⊥ := hM3 tbw ThreeBNF.orderOf_tbw
  rcases m3_component_cases hsyl hirr hM3 (isComponentOf_of_glaPComponent_of_core hX hJ) with
    h | h
  · exact hR (Or.inl ⟨J, h⟩)
  · exact hR (Or.inr ⟨J, h⟩)

end Setup

end CFSG.HardMathSupport.Dickson.I271
