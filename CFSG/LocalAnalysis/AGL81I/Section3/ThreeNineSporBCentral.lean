module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporConstrained
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBurnside
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentRes
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveNoCompK
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65
public import CFSG.Mathlib.GroupTheory.ExtraspecialCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetCatalog
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier
import CFSG.RankThree.Native.FiveLocalPCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
import CFSG.Monster.Griess.ModFive.Lattice

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

noncomputable section

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Pinned CFSG.RankThree.Native
  CFSG.RankThree.Native.FiveLocal CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.Sec6.I1431
  CFSG.Quasithin.B113KDet
open scoped commutatorElement

private instance fact_prime_thirty_one : Fact (Nat.Prime 31) := ⟨by norm_num⟩

private theorem orderOf_mul_of_thirteen_five {G : Type*} [Group G] {a b : G}
    (h : a * b = b * a) (ha : orderOf a = 13) (hb : orderOf b = 5) :
    orderOf (a * b) = 65 := by
  have hcomm : Commute a b := h
  have hcop : (orderOf a).Coprime (orderOf b) := by
    rw [ha, hb]
    norm_num
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha, hb]

private theorem three_pow_three_not_dvd (r s : ℕ) (hr : r ≤ 5) :
    ¬ 3 ^ 3 ∣ 5 ^ s * ∏ i : Fin r, (5 ^ r - 5 ^ (i : ℕ)) := by
  have hcop : Nat.Coprime (3 ^ 3) (5 ^ s) := by
    have h35 : Nat.Coprime 3 5 := by norm_num
    exact (h35.pow_left 3).pow_right s
  intro hd
  have h3 := hcop.dvd_of_dvd_mul_left hd
  interval_cases r <;> norm_num [Fin.prod_univ_succ] at h3

private theorem factorization_two_monsterBabyOrder :
    CFSG.Open.monsterBabyOrder.factorization 2 = 41 := by
  have h : CFSG.Open.monsterBabyOrder = 2 ^ 41 * 1889375872099856765625 := by
    unfold CFSG.Open.monsterBabyOrder
    norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem factorization_five_monsterBabyOrder :
    CFSG.Open.monsterBabyOrder.factorization 5 = 6 := by
  have h : CFSG.Open.monsterBabyOrder = 5 ^ 6 * 265906014798491276235365154816 := by
    unfold CFSG.Open.monsterBabyOrder
    norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem factorization_two_target :
    (2 ^ 41 * 3 ^ 4 * 5 ^ 6).factorization 2 = 41 := by
  rw [show 2 ^ 41 * 3 ^ 4 * 5 ^ 6 = 2 ^ 41 * (3 ^ 4 * 5 ^ 6) by ring,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem factorization_three_target :
    (2 ^ 41 * 3 ^ 4 * 5 ^ 6).factorization 3 = 4 := by
  rw [show 2 ^ 41 * 3 ^ 4 * 5 ^ 6 = 3 ^ 4 * (2 ^ 41 * 5 ^ 6) by ring,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem factorization_five_target :
    (2 ^ 41 * 3 ^ 4 * 5 ^ 6).factorization 5 = 6 := by
  rw [show 2 ^ 41 * 3 ^ 4 * 5 ^ 6 = 5 ^ 6 * (2 ^ 41 * 3 ^ 4) by ring,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem orderOf_five_zmod_thirty_one : orderOf (5 : ZMod 31) = 3 := by
  have h3 : ((5 : ZMod 31) ^ 3) = 1 := by decide +kernel
  have h1 : (5 : ZMod 31) ≠ 1 := by decide +kernel
  exact orderOf_eq_prime (p := 3) h3 h1

private theorem Q_inf_centralizer_eq {G : Type*} [Group G] [Finite G]
    {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z) :
    Q q ⊓ Subgroup.centralizer (Q q : Set G) = Subgroup.zpowers z := by
  have h1 : (Subgroup.center ↥(Q q)).map (Q q).subtype =
      Q q ⊓ Subgroup.centralizer (Q q : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, Subgroup.mem_centralizer_iff.2 fun y hy => by
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hy⟩)⟩
    · rintro ⟨hg, hgc⟩
      exact ⟨⟨g, hg⟩, Subgroup.mem_center_iff.2 fun y => by
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 hgc (y : G) y.2, rfl⟩
  exact h1.symm.trans hR.ZQ_eq

private theorem commutator_Q_le_zpowers {G : Type*} [Group G]
    {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z) :
    ⁅Q q, Q q⁆ ≤ Subgroup.zpowers z := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h : ⁅a, b⁆ = bcomm a⁻¹ b⁻¹ := by
    rw [commutatorElement_def, bcomm]
    group
  rw [h]
  exact hR.bcomm_mem (Subgroup.inv_mem _ ha) (Subgroup.inv_mem _ hb)

private theorem prime_dvd_of_dvd_five_pow_sub_one {r k : ℕ} (hr : r.Prime) (hk1 : 1 ≤ k)
    (hk5 : k < 5) (hdvd : r ∣ 5 ^ k - 1) :
    r = 2 ∨ r = 3 ∨ r = 13 ∨ r = 31 := by
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · have h4 : r ∣ 2 ^ 2 := by
      norm_num at hdvd ⊢
      exact hdvd
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h4))
  · have h24 : r ∣ 2 ^ 3 * 3 := by
      norm_num at hdvd ⊢
      exact hdvd
    rcases hr.dvd_mul.1 h24 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3))
  · have h124 : r ∣ 2 ^ 2 * 31 := by
      norm_num at hdvd ⊢
      exact hdvd
    rcases hr.dvd_mul.1 h124 with h2 | h31
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h31)))
  · have h624 : r ∣ 2 ^ 4 * (3 * 13) := by
      norm_num at hdvd ⊢
      exact hdvd
    rcases hr.dvd_mul.1 h624 with h2 | hrest
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · rcases hr.dvd_mul.1 hrest with h3 | h13
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h13)))

section CertBase

private abbrev CB : Subgroup NativeSporadic.B :=
  Subgroup.centralizer ({zFive} : Set NativeSporadic.B)

private abbrev OB : Subgroup NativeSporadic.B := (CFSG.pCore 5 ↥CB).map CB.subtype

private theorem CB_le_normalizer_OB :
    CB ≤ Subgroup.normalizer (OB : Set NativeSporadic.B) := by
  refine Subgroup.le_normalizer_iff.2 ?_
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hpc : (⟨g, hg⟩ : ↥CB) * y * (⟨g, hg⟩ : ↥CB)⁻¹ ∈ CFSG.pCore 5 ↥CB :=
    Subgroup.Normal.conj_mem (CFSG.pCore_normal (p := 5) (G := ↥CB)) y hy ⟨g, hg⟩
  refine Subgroup.mem_map.2 ⟨_, hpc, ?_⟩
  rfl

private theorem CB_le_normalizer_Q (hO : OB = Q qFive) :
    CB ≤ Subgroup.normalizer (Q qFive : Set NativeSporadic.B) := hO ▸ CB_le_normalizer_OB

end CertBase

section CertSix

private theorem P_le_CB : P xFive qFive ≤ CB := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.2
    (bFiveRel.mem_H0.1 (bFiveRel.P_le_H0 hg)).2

private theorem not_order_thirty_one_mem_centralizer_Q {u : NativeSporadic.B}
    (hu : orderOf u = 31) (huz : u * zFive = zFive * u)
    (huN : u ∈ Subgroup.normalizer (Q qFive : Set NativeSporadic.B)) :
    u ∈ Subgroup.centralizer (Q qFive : Set NativeSporadic.B) := by
  have hpr : orderOf (5 : ZMod 31) = 3 := orderOf_five_zmod_thirty_one
  have hQQ : ⁅Q qFive, Q qFive⁆ ≤ Subgroup.zpowers zFive :=
    commutator_Q_le_zpowers bFiveRel
  have hZ : Q qFive ⊓ Subgroup.centralizer (Q qFive : Set NativeSporadic.B) =
      Subgroup.zpowers zFive := Q_inf_centralizer_eq bFiveRel
  have hQ6 : Nat.card (Q qFive) ∣ 5 ^ 6 := by
    rw [bFiveRel.card_Q]
    norm_num
  exact CFSG.Extraspecial.mem_centralizer_of_orderOf_eq_three
    (p := 5) (r := 31) (G := NativeSporadic.B) (Q := Q qFive) (z := zFive) (u := u)
    bFiveRel.orderOf_z hQQ hZ hQ6 hpr hu huN huz

private theorem card_centralizer_eq_CB_of_mem_zpowers {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.B) {z : L}
    (hcard : Nat.card (Subgroup.centralizer ({(e z : NativeSporadic.B)} :
      Set NativeSporadic.B)) = Nat.card (Subgroup.centralizer ({z} : Set L)))
    (hs : orderOf (e z) = 5)
    (hconj : ∃ c : NativeSporadic.B, c * (e z) * c⁻¹ ∈ Subgroup.zpowers zFive) :
    Nat.card (Subgroup.centralizer ({z} : Set L)) = Nat.card CB := by
  let s : NativeSporadic.B := e z
  obtain ⟨c, hc⟩ := hconj
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hconj5 : orderOf (c * s * c⁻¹) = 5 := by
    rw [← MulAut.conj_apply c s, MulEquiv.orderOf_eq]
    exact hs
  obtain ⟨k, hkpow, hk5⟩ : ∃ k : ℕ, zFive ^ j = zFive ^ k ∧ k < 5 := by
    refine ⟨(j % 5).toNat, ?_, ?_⟩
    · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num)),
        zpow_eq_zpow_emod j (by rw [zpow_natCast]; exact bFiveRel.z_pow_five)]
      rfl
    · have h0 := Int.emod_nonneg j (by norm_num : (5 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 5)
      omega
  have hk0 : k ≠ 0 := by
    intro h0
    have h1 : zFive ^ j = 1 := by rw [hkpow, h0, pow_zero]
    have h2 : c * s * c⁻¹ = 1 := by rw [← hj, h1]
    rw [h2, orderOf_one] at hconj5
    norm_num at hconj5
  have h5k : ¬ 5 ∣ k := by
    intro hd
    have hle : 5 ≤ k := Nat.le_of_dvd (by omega) hd
    omega
  have hcentk : Subgroup.centralizer ({zFive ^ k} : Set NativeSporadic.B) =
      Subgroup.centralizer ({zFive} : Set NativeSporadic.B) :=
    CFSG.HardMathSupport.Dickson.I271.TabMFive.centralizer_pow_eq_of_five
      bFiveRel.orderOf_z h5k
  have hcard2 : Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.B)) =
      Nat.card CB := by
    rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj c s,
      ← hj, hkpow, hcentk]
  rw [← hcard]
  exact hcard2

end CertSix

section CertCardB

private theorem factorization_two_le (hCB : Nat.card CB ∣ Nat.card NativeSporadic.B) :
    (Nat.card CB).factorization 2 ≤ 41 := by
  have hle : (Nat.card CB).factorization 2 ≤
      (Nat.card NativeSporadic.B).factorization 2 :=
    (Nat.factorization_le_iff_dvd (d := Nat.card CB) (n := Nat.card NativeSporadic.B)
      Nat.card_pos.ne' Nat.card_pos.ne').mpr hCB 2
  rw [CFSG.Monster.Existence.card_nativeB, factorization_two_monsterBabyOrder] at hle
  exact hle

private theorem factorization_five_le (hCB : Nat.card CB ∣ Nat.card NativeSporadic.B) :
    (Nat.card CB).factorization 5 ≤ 6 := by
  have hle : (Nat.card CB).factorization 5 ≤
      (Nat.card NativeSporadic.B).factorization 5 :=
    (Nat.factorization_le_iff_dvd (d := Nat.card CB) (n := Nat.card NativeSporadic.B)
      Nat.card_pos.ne' Nat.card_pos.ne').mpr hCB 5
  rw [CFSG.Monster.Existence.card_nativeB, factorization_five_monsterBabyOrder] at hle
  exact hle

end CertCardB

section CertCatalog

private theorem isKGroup_B_of_isKGroupCat {L : Type} [Group L]
    (hK : CFSG.SectionRank.IsKGroupCat L) (e : L ≃* NativeSporadic.Carrier .B) :
    CFSG.Open.IsKGroup NativeSporadic.B := by
  have hbr : CFSG.Quasithin.B113KDet.CatalogBridge :=
    CFSG.Quasithin.B113KDet.catalogBridge_holds
  have hK' : CFSG.SectionRank.IsKGroupCat NativeSporadic.B :=
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv hK e.symm
  unfold CFSG.Open.IsKGroup
  unfold CFSG.SectionRank.IsKGroupCat at hK'
  intro K L' _ _ hs _
  exact hbr _ (hK' K (L'.subgroupOf K) hs)

end CertCatalog

section CertCore

private theorem centralizer_pCore_le (hB : CFSG.Open.IsKGroup NativeSporadic.B) :
    Subgroup.centralizer (CFSG.pCore 5 ↥CB : Set ↥CB) ≤ CFSG.pCore 5 ↥CB := by
  refine centralizer_pCore_le_pCore_of_noComp Nat.prime_five
    gLAPPrimeCoreOf_centralizer_zFive_eq_bot ?_
  intro J hJ
  exact tabBFiveBNoComp_of_kGroup
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    hB J hJ

private theorem pCore_eq_Q_aux (hB : CFSG.Open.IsKGroup NativeSporadic.B) : OB = Q qFive := by
  have h5 : (Nat.card NativeSporadic.B).factorization 5 = 6 := by
    rw [CFSG.Monster.Existence.card_nativeB, factorization_five_monsterBabyOrder]
  have hDade : OB = Q qFive ∨ OB = Subgroup.zpowers zFive :=
    bFiveRel.pCore_centralizer_eq_Q_or_zpowers h5
  rcases hDade with h | h
  · exact h
  · exfalso
    have h56 : 5 ^ 6 ∣ Nat.card CB := bFiveRel.card_P ▸ Subgroup.card_dvd_of_le P_le_CB
    have hfull : Subgroup.centralizer (CFSG.pCore 5 ↥CB : Set ↥CB) = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨c, hc⟩ -
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      apply Subtype.ext
      have hyO : (y : NativeSporadic.B) ∈ OB := Subgroup.mem_map_of_mem CB.subtype hy
      rw [h] at hyO
      have hzc : c * zFive = zFive * c := by
        simpa only [CB, Subgroup.mem_centralizer_singleton_iff] using hc
      have hcz : zFive * c = c * zFive := hzc.symm
      have hle : Subgroup.zpowers zFive ≤
          Subgroup.centralizer ({c} : Set NativeSporadic.B) :=
        Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hcz)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hyO)
    have hpceq : CFSG.pCore 5 ↥CB = ⊤ := le_antisymm le_top (hfull ▸ centralizer_pCore_le hB)
    have hcard : Nat.card CB = 5 := by
      calc Nat.card CB = Nat.card (CFSG.pCore 5 ↥CB) := by rw [hpceq, Subgroup.card_top]
        _ = Nat.card OB := (Subgroup.card_map_of_injective CB.subtype_injective).symm
        _ = Nat.card (Subgroup.zpowers zFive) := by rw [h]
        _ = 5 := by rw [Nat.card_zpowers, bFiveRel.orderOf_z]
    have hle : 5 ^ 6 ≤ Nat.card CB := Nat.le_of_dvd Nat.card_pos h56
    rw [hcard] at hle
    norm_num at hle

private theorem exists_prime_element_not_mem_centralizer_Q
    (hB : CFSG.Open.IsKGroup NativeSporadic.B) (hO : OB = Q qFive) {r : ℕ}
    (hr : r.Prime) (hrdvd : r ∣ Nat.card CB) (hr5 : r ≠ 5) :
    ∃ u : NativeSporadic.B, orderOf u = r ∧ u * zFive = zFive * u ∧
      u ∈ Subgroup.normalizer (Q qFive : Set NativeSporadic.B) ∧
      u ∉ Subgroup.centralizer (Q qFive : Set NativeSporadic.B) := by
  have hF : Fintype ↥CB := Fintype.ofFinite _
  have hcard : Nat.card ↥CB = @Fintype.card ↥CB hF := @Nat.card_eq_fintype_card ↥CB hF
  have hdvd : r ∣ @Fintype.card ↥CB hF := by
    rw [← hcard]
    exact hrdvd
  obtain ⟨v, hv⟩ := @exists_prime_orderOf_dvd_card ↥CB inferInstance hF r ⟨hr⟩ hdvd
  refine ⟨(v : NativeSporadic.B), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hv]
  · have h := v.2
    simpa only [CB, Subgroup.mem_centralizer_singleton_iff] using h
  · exact CB_le_normalizer_Q hO v.2
  · intro huQ
    have hvcent : v ∈ Subgroup.centralizer (CFSG.pCore 5 ↥CB : Set ↥CB) := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have hyQ : (y : NativeSporadic.B) ∈ Q qFive := by
        rw [← hO]
        exact Subgroup.mem_map_of_mem CB.subtype hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 huQ (y : NativeSporadic.B) hyQ)
    have hmem : v ∈ CFSG.pCore 5 ↥CB := centralizer_pCore_le hB hvcent
    have hpcdvd : r ∣ Nat.card (CFSG.pCore 5 ↥CB) := by
      have := Subgroup.orderOf_dvd_natCard (CFSG.pCore 5 ↥CB) hmem
      rwa [hv] at this
    have hQcard : Nat.card (CFSG.pCore 5 ↥CB) = 5 ^ 5 := by
      rw [← Subgroup.card_map_of_injective CB.subtype_injective]
      change Nat.card OB = 5 ^ 5
      rw [hO, bFiveRel.card_Q]
    have hr5' : r = 5 := by
      have h : r ∣ 5 ^ 5 := hQcard ▸ hpcdvd
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 (hr.dvd_of_dvd_pow h)
    exact hr5 hr5'

private theorem factorization_three_le (hB : CFSG.Open.IsKGroup NativeSporadic.B)
    (hO : OB = Q qFive) : (Nat.card CB).factorization 3 ≤ 2 := by
  have hC : Subgroup.centralizer (CFSG.pCore 5 ↥CB : Set ↥CB) ≤ CFSG.pCore 5 ↥CB :=
    centralizer_pCore_le hB
  obtain ⟨r, s, hr, hdvd⟩ := exists_card_dvd_of_centralizer_pCore_le (p := 5) hC
  have hQ5 : Nat.card (CFSG.pCore 5 ↥CB) = 5 ^ 5 := by
    rw [← Subgroup.card_map_of_injective CB.subtype_injective]
    change Nat.card OB = 5 ^ 5
    rw [hO, bFiveRel.card_Q]
  have hr5 : r ≤ 5 := by
    have h5r : 5 ^ r ≤ 5 ^ 5 := hQ5 ▸ hr
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 h5r
  by_contra hcon
  have h3dvd : 3 ^ 3 ∣ Nat.card CB :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').2 (by omega)
  have h3prod : 3 ^ 3 ∣ 5 ^ s * ∏ i : Fin r, (5 ^ r - 5 ^ (i : ℕ)) :=
    h3dvd.trans hdvd
  exact three_pow_three_not_dvd r s hr5 h3prod

end CertCore

private theorem prime_dvd_card_centralizer (hB : CFSG.Open.IsKGroup NativeSporadic.B)
    (hO : OB = Q qFive) {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ Nat.card CB) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  by_cases hr5 : r = 5
  · exact Or.inr (Or.inr hr5)
  · obtain ⟨u, hu_r, huz, huN, huCQ⟩ :=
      exists_prime_element_not_mem_centralizer_Q hB hO hr hrdvd hr5
    have hz_ne_one : zFive ≠ 1 := by
      intro h1
      have h5 := bFiveRel.orderOf_z
      rw [h1, orderOf_one] at h5
      norm_num at h5
    obtain ⟨k, hk1, hk5, hkdvd⟩ :=
      exists_dvd_pow_sub_one_of_not_mem_centralizer (G := NativeSporadic.B)
        (p := 5) (r := r) (m := 5) (R := Q qFive) Nat.prime_five hr hr5
        (by rw [bFiveRel.card_Q]) (w := u) (z := zFive)
        hu_r huN bFiveRel.z_mem hz_ne_one huz huCQ
    rcases prime_dvd_of_dvd_five_pow_sub_one hr hk1 hk5 hkdvd with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exfalso
      have h65 : orderOf (u * zFive) = 65 :=
        orderOf_mul_of_thirteen_five (G := NativeSporadic.B) (a := u) (b := zFive)
          huz (by rw [hu_r, h]) bFiveRel.orderOf_z
      exact noOrder65_B (u * zFive) h65
    · exfalso
      exact huCQ (not_order_thirty_one_mem_centralizer_Q (by rw [hu_r, h]) huz huN)

private theorem factorization_eq_zero_of_prime_not_two_three_five
    (hB : CFSG.Open.IsKGroup NativeSporadic.B) (hO : OB = Q qFive) {p : ℕ}
    (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) :
    (Nat.card CB).factorization p = 0 ∧ (2 ^ 41 * 3 ^ 4 * 5 ^ 6).factorization p = 0 := by
  constructor
  · apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    rcases prime_dvd_card_centralizer hB hO hp hd with h | h | h
    · exact h2 h
    · exact h3 h
    · exact h5 h
  · apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have h' : p ∣ 2 := hp.dvd_of_dvd_pow h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
      · have h' : p ∣ 3 := hp.dvd_of_dvd_pow h
        exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h')
    · have h' : p ∣ 5 := hp.dvd_of_dvd_pow h
      exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h')

private theorem card_centralizer_dvd_aux (hB : CFSG.Open.IsKGroup NativeSporadic.B)
    (hO : OB = Q qFive) : Nat.card CB ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6 := by
  have hCB : Nat.card CB ∣ Nat.card NativeSporadic.B := Subgroup.card_subgroup_dvd_card CB
  have h2le := factorization_two_le hCB
  have h5le := factorization_five_le hCB
  have h3le := factorization_three_le hB hO
  refine (Nat.factorization_le_iff_dvd (d := Nat.card CB)
    (n := 2 ^ 41 * 3 ^ 4 * 5 ^ 6) Nat.card_pos.ne' (by norm_num)).mp ?_
  intro p
  by_cases hp : p.Prime
  · by_cases h2 : p = 2
    · subst h2
      rw [factorization_two_target]
      exact h2le
    · by_cases h3 : p = 3
      · subst h3
        rw [factorization_three_target]
        omega
      · by_cases h5 : p = 5
        · subst h5
          rw [factorization_five_target]
          exact h5le
        · obtain ⟨h1, h0⟩ :=
            factorization_eq_zero_of_prime_not_two_three_five hB hO hp h2 h3 h5
          rw [h1, h0]
  · rw [Nat.factorization_eq_zero_of_not_prime (Nat.card CB) hp,
      Nat.factorization_eq_zero_of_not_prime (2 ^ 41 * 3 ^ 4 * 5 ^ 6) hp]

theorem card_centralizer_dvd_B_of_five_central {L : Type} [Group L] [Finite L]
    (hK : CFSG.SectionRank.IsKGroupCat L) (e : L ≃* NativeSporadic.Carrier .B) {z : L}
    (hz : orderOf z = 5) (h56 : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6 := by
  have hB : CFSG.Open.IsKGroup NativeSporadic.B := isKGroup_B_of_isKGroupCat hK e
  have hO : OB = Q qFive := pCore_eq_Q_aux hB
  have hBdvd : Nat.card CB ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6 := card_centralizer_dvd_aux hB hO
  have hs : orderOf (e z) = 5 := by
    rw [MulEquiv.orderOf_eq, hz]
  have hcard : Nat.card (Subgroup.centralizer ({(e z : NativeSporadic.B)} :
      Set NativeSporadic.B)) = Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    change Nat.card (Subgroup.centralizer ({(e z : NativeSporadic.Carrier .B)} :
      Set (NativeSporadic.Carrier .B))) = _
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_mulEquiv_apply
      (e : L ≃* NativeSporadic.B) z
  have h56' : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({(e z : NativeSporadic.B)} :
      Set NativeSporadic.B)) := by
    rw [hcard]
    exact h56
  have hconj := exists_conj_mem_zpowers_zFive hs h56'
  have hfin := card_centralizer_eq_CB_of_mem_zpowers e hcard hs hconj
  rw [hfin]
  exact hBdvd

end

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
