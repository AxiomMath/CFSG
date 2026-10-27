module

public import CFSG.Quasithin.H13.L32A727c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A728
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk6

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem l1_not_le_two_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {X : Subgroup G} (hX : IsPGroup 2 ↥X) (hle : l1 T L V ≤ X) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := (M76.relIndex_l1_T_F4 S h1222 h1332 h1334).1
  have hle' : l1 T L V ≤ pCoreOf 2 (l1 T L V) :=
    le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (hX.to_le hle)
  rw [Subgroup.relIndex_eq_one.mpr hle'] at h3
  norm_num at h3

theorem false_of_B1a_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4) (h79 : Lemma14_7_9_F4)
    (h714 : Thm14_7_14_F4) {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal)
    (hK : IsPGroup 3 ↥K) (hexp : ∀ x ∈ K, x ^ 3 = 1)
    (hKM : ¬ pre H K ≤ Subgroup.normalizer (L : Set G)) (hHe : H = pre H K ⊔ (l1 T L V ⊔ T))
    (hlt : pCoreOf 2 (oTwoUpper (pre H K)) <
      oTwoUpper (pre H K) ⊓ Subgroup.normalizer (L : Set G)) : False := by
  obtain ⟨hYY, hYH, hHY, hY3⟩ := hyp79 hKn hexp
  have hKY := modO2Image_oTwoUpper_pre hK
  obtain ⟨-, h⟩ := h79 G T L V H S _ 3 Nat.prime_three hYY hYH hHY hY3 hlt
  rcases h with hYl | ⟨hP, hz, -⟩
  · exact hKM (pre_le_M_of_le_l1_F4 S h1332 (by rw [← hKY, hYl]))
  · have hLK : modO2Image H (l1 T L V) ≤ K := by
      rw [← hKY]
      exact modO2Image_mono' ((le_sup_left.trans hz.le).trans (o2z_le _))
    have hle := oTwoUpper_top_le S hKn hHe hLK
    have hge : K ≤ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hKY]
      exact modO2Image_oTwoUpper_le hYH
    have h1 := isPOnePlusTwo_modO2Image hYH hHY hP
    rw [hKY, ← le_antisymm hle hge] at h1
    exact h714 G T L V H S h1

theorem false_of_B1b_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4)
    (ih : ∀ H₀ : Subgroup G, H₀ < H → Setting147 G T L V H₀ → Concl T L V H₀)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal) (hK : IsPGroup 3 ↥K)
    (hKP : K ≤ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hcent : ∀ x ∈ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H), (∀ y ∈ K, x * y = y * x) →
      orderOf x = 3 → x ∈ K)
    (hKne : K ≠ ⊥)
    (hle : oTwoUpper (pre H K) ⊓ Subgroup.normalizer (L : Set G) ≤
      pCoreOf 2 (oTwoUpper (pre H K)))
    (hLP : modO2Image H (l1 T L V) ≤ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := oTwoUpper (pre H K) with hY
  set L1s := modO2Image H (l1 T L V) with hL1s
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hLM := l1T_le_M_F4 S.hyp h1332
  have hP3 : IsPGroup 3 ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := CFSG.pCore_isPGroup
  have hL3 : IsPGroup 3 ↥L1s := hP3.to_le hLP

  have hLne : L1s ≠ ⊥ := by
    intro h
    refine l1_not_le_two_F4 S h1222 h1332 h1334 (pCoreOf_isPGroup 2 H) fun x hx => ?_
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hl1H hx⟩ ∈ L1s :=
      ⟨⟨x, hl1H hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← mem_pCoreOf_iff] at hx'
    exact hx'
  have hL3card : Nat.card ↥L1s = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp
      (L32A.card_dvd_three_of_isPGroup_F4 S h1222 h1332 h1334 hL3) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hLne
    · exact h

  have hLK : ¬ L1s ≤ K := by
    intro h
    have h2 : l1 T L V ≤ Y :=
      (A4.oTwoUpper_oTwoUpper (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G))).symm.le.trans
        (oTwoUpper_mono (le_pre_of_le hl1H h))
    exact l1_not_le_two_F4 S h1222 h1332 h1334 (pCoreOf_isPGroup 2 Y)
      ((le_inf h2 (le_sup_left.trans hLM)).trans hle)
  have hLKinf : L1s ⊓ K = ⊥ := by
    have hd : Nat.card ↥(L1s ⊓ K) ∣ 3 := hL3card ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      apply hLK
      have e := Subgroup.eq_of_le_of_card_ge (inf_le_left : L1s ⊓ K ≤ L1s) (by rw [h, hL3card])
      rw [← e]
      exact inf_le_right

  set P1 := K ⊓ Subgroup.centralizer (L1s : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hP1
  have hP1ne : P1 ≠ ⊥ := by
    set J := K ⊔ L1s with hJ
    have hJ3 : IsPGroup 3 ↥J := hP3.to_le (sup_le hKP hLP)
    have : Group.IsNilpotent ↥J := hJ3.isNilpotent
    have : (K.subgroupOf J).Normal := hKn.subgroupOf J
    have hKJ : K.subgroupOf J ≠ ⊥ := by
      intro h
      exact hKne ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le le_sup_left)
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hKJ)
    intro hP
    have hzK : ((z : ↥J) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
    have hzC : ((z : ↥J) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
        Subgroup.centralizer (L1s : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hc := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp z.2).2
        ⟨l, Subgroup.mem_sup_right hl⟩
      exact congrArg Subtype.val hc
    have hz : ((z : ↥J) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ P1 := ⟨hzK, hzC⟩
    rw [hP, Subgroup.mem_bot] at hz
    exact hz1 (Subtype.ext (Subtype.ext hz))

  have hP1lt : P1 < K := by
    refine lt_of_le_of_ne inf_le_left fun h => hLK fun l hl => ?_
    by_cases hl1 : l = 1
    · rw [hl1]
      exact K.one_mem
    have hord : orderOf l = 3 := by
      have hd : orderOf l ∣ 3 := hL3card ▸ Subgroup.orderOf_dvd_natCard L1s hl
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hl1
      · exact h1
    refine hcent l (hLP hl) (fun y hy => ?_) hord
    have hyC := (show y ∈ P1 from h ▸ hy).2
    exact Subgroup.mem_centralizer_iff.mp hyC l hl

  have hTL1 : modO2Image H T ≤ Subgroup.normalizer (L1s : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_le_normalizer' (Setting147.T_le_N_l1_F4 S h1332)
  have hKN : ∀ x : ↥H ⧸ CFSG.pCore 2 ↥H, x ∈ Subgroup.normalizer (K : Set _) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by
        have := hKn.conj_mem _ hk x⁻¹
        convert this using 1
        group⟩
  have hL1N : L1s ≤ Subgroup.normalizer (L1s : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    Subgroup.le_normalizer
  have hLT : L1s ⊔ modO2Image H T ≤ Subgroup.normalizer (P1 : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hKN l, mem_normalizer_centralizer (hL1N hl)⟩)
      fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hKN t, mem_normalizer_centralizer (hTL1 ht)⟩

  set H1 := pre H P1 ⊔ (l1 T L V ⊔ T) with hH1
  have hH1H : H1 ≤ H := sup_le (pre_le P1) (sup_le hl1H hTH)
  have hP1n : H1 ≤ Subgroup.normalizer (pre H P1 : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    intro g hg
    have hgH : g ∈ H := sup_le hl1H hTH hg
    have hgs : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hgH⟩ ∈ L1s ⊔ modO2Image H T := by
      rw [← modO2Image_sup hl1H hTH]
      exact ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hN := Subgroup.mem_normalizer_iff.mp (hLT hgs)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxH := pre_le P1 hx
      have h1 := (hN _).mp ((mem_pre ⟨x, hxH⟩).mp hx)
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      exact (mem_pre (⟨g, hgH⟩ * ⟨x, hxH⟩ * ⟨g, hgH⟩⁻¹)).mpr h1
    · intro hx
      have hxH : x ∈ H := by
        have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (H.inv_mem hgH) (pre_le P1 hx)) hgH
      have h1 := (mem_pre (⟨g, hgH⟩ * ⟨x, hxH⟩ * ⟨g, hgH⟩⁻¹)).mp hx
      rw [map_mul, map_mul, map_inv] at h1
      exact (mem_pre ⟨x, hxH⟩).mpr ((hN _).mpr h1)
  have hP13 : IsPGroup 3 ↥P1 := hK.to_le inf_le_left
  have hH1lt : H1 < H := by
    refine lt_of_le_of_ne hH1H fun h => ?_

    have hA3 : IsPGroup 3 ↥(P1 ⊔ L1s) := hP3.to_le (sup_le (inf_le_left.trans hKP) hLP)
    have hTop : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ (P1 ⊔ L1s) ⊔ modO2Image H T := by
      have e := congrArg (modO2Image H) h
      rw [modO2Image_self, modO2Image_sup (pre_le P1) (sup_le hl1H hTH),
        modO2Image_sup hl1H hTH, modO2Image_pre] at e
      rw [← e, sup_assoc]
    have hT2 : IsPGroup 2 ↥(modO2Image H T) := isPGroup_modO2Image S.hyp.fsu.sylow.1
    have hTA : modO2Image H T ≤ Subgroup.normalizer ((P1 ⊔ L1s : Subgroup _) : Set _) :=
      fun t ht => mem_normalizer_sup (hLT (Subgroup.mem_sup_right ht)) (hTL1 ht)
    have hKA : K ≤ P1 ⊔ L1s := by
      intro x hx
      obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 hTA (hTop (Subgroup.mem_top x))
      obtain ⟨i, hi⟩ := hK ⟨x, hx⟩
      have hi' : x ^ 3 ^ i = 1 := by simpa using congrArg Subtype.val hi
      have hcop : Nat.Coprime (2 ^ k) (orderOf x) := by
        obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hi')
        rw [hl]
        exact Nat.Coprime.pow k l (by decide)
      exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

    have hc1 := TJ1.card_sup_mul_card_inf (X := L1s) (N := K) (fun l _ => hKN l)
    have hc2 := TJ1.card_sup_mul_card_inf (X := L1s) (N := P1)
      (fun l hl => hLT (Subgroup.mem_sup_left hl))
    rw [hLKinf, Subgroup.card_bot, mul_one, hL3card] at hc1
    have hle1 : Nat.card ↥(L1s ⊔ K) ≤ Nat.card ↥(L1s ⊔ P1) :=
      Subgroup.card_le_of_le (sup_le le_sup_left (hKA.trans (sup_comm P1 L1s).le))
    have hpos : 0 < Nat.card ↥(L1s ⊓ P1) := Nat.card_pos
    rw [hL3card] at hc2
    have h3 : Nat.card ↥(L1s ⊔ P1) ≤ 3 * Nat.card ↥P1 := by
      rw [← hc2]
      exact Nat.le_mul_of_pos_right _ hpos
    have hKle : Nat.card ↥K ≤ Nat.card ↥P1 := by omega
    exact hP1lt.ne (Subgroup.eq_of_le_of_card_ge inf_le_left hKle)

  have hP1M : pre H P1 ≤ Subgroup.normalizer (L : Set G) := by
    by_cases hH1M : H1 ≤ Subgroup.normalizer (L : Set G)
    · exact le_sup_left.trans hH1M
    have S1 := setting_of_le_F4 S h1332 h1334 le_sup_right hH1H hH1M
    exact le_M_of_concl_F4 S1 h1332 (ih H1 hH1lt S1) le_sup_left hP1n
      ((pCoreOf_le_pre P1).trans le_sup_left) (hH1H.trans (le_normalizer_pCoreOf 2 H))
      (pCoreOf_isPGroup 2 H) fun n hn => pow_mem_of_isPGroup hP13 hn

  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    (le_normalizer_pre hKn).trans (normalizer_le_normalizer_oTwoUpper _)
  have hYH : Y ≤ H := (oTwoUpper_le _).trans (pre_le K)
  have hO2 : pCoreOf 2 Y ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
      (hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
  have hP1b : P1 ≤ ⊥ := by
    rw [← modO2Image_oTwoUpper_pre hP13, ← modO2Image_pCoreOf_eq_bot (H := H)]
    refine modO2Image_mono' (le_trans ?_ (hle.trans hO2))
    exact le_inf (oTwoUpper_mono (pre_mono inf_le_left)) ((oTwoUpper_le _).trans hP1M)
  exact hP1ne (le_bot_iff.mp hP1b)

end CFSG.Quasithin.H13.L32A.R727
