module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace Unc25G2

variable {G : Type} [Group G]

theorem card_alternatingGroup_fin_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_alternatingGroup_fin_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_alt_cases {m : ℕ} (hm : m = 6 ∨ m = 7) :
    Nat.card (alternatingGroup (Fin m)) = 360 ∨ Nat.card (alternatingGroup (Fin m)) = 2520 := by
  rcases hm with rfl | rfl
  · exact Or.inl card_alternatingGroup_fin_six'
  · exact Or.inr card_alternatingGroup_fin_seven

theorem center_eq_bot_of_simple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hs : IsSimpleGroup ↥L) : Subgroup.center ↥L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
      rw [h]; exact QuotientGroup.subsingleton_quotient_top
    exact hab (Subsingleton.elim _ _)

theorem not_centralQuotientAlt_of_center_bot {L : Subgroup G} (hZ : Subgroup.center ↥L = ⊥)
    {m : ℕ} (hcard : Nat.card ↥L ≠ Nat.card (alternatingGroup (Fin m))) :
    ¬ CentralQuotientAlt L m := by
  rintro ⟨e⟩
  apply hcard
  rw [← Nat.card_congr e.toEquiv]
  rw [hZ]
  exact (Nat.card_congr (QuotientGroup.quotientBot (G := ↥L)).toEquiv).symm

theorem ne_alt_of_sixteen_dvd {N m : ℕ} (hN : 16 ∣ N) (hm : m = 6 ∨ m = 7) :
    N ≠ Nat.card (alternatingGroup (Fin m)) := by
  rcases card_alt_cases hm with h | h <;> rw [h] <;> omega

theorem ne_alt_of_ne {N m : ℕ} (h1 : N ≠ 360) (h2 : N ≠ 2520) (hm : m = 6 ∨ m = 7) :
    N ≠ Nat.card (alternatingGroup (Fin m)) := by
  rcases card_alt_cases hm with h | h <;> rw [h] <;> assumption

theorem sixteen_dvd_of_pow {q k : ℕ} (hq : 4 ≤ q) (hq2 : ∃ a, q = 2 ^ a) (hk : 2 ≤ k) :
    16 ∣ q ^ k := by
  obtain ⟨a, rfl⟩ := hq2
  have ha : 2 ≤ a := by
    by_contra h
    push Not at h
    interval_cases a <;> simp at hq
  rw [← pow_mul]
  exact (pow_dvd_pow 2 (by nlinarith : 4 ≤ a * k))


theorem charP_two_of_card_eq' {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem not_centralQuotientAlt_of_bender [Finite G] {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hB : fusionIsBenderGroup ↥L) {m : ℕ} (hm : m = 6 ∨ m = 7) : ¬ CentralQuotientAlt L m := by
  have hs : IsSimpleGroup ↥L := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  refine not_centralQuotientAlt_of_center_bot (center_eq_bot_of_simple hq hs) ?_
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    have hf0 : f ≠ 0 := by omega
    have hKc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
    have hN : Nat.card ↥L = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
          (GaloisField 2 f)).toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 2) (by norm_num), hKc]
      have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := by
        apply Nat.Coprime.gcd_eq_one
        rw [Nat.coprime_two_left]
        have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
        rw [Nat.odd_iff]
        omega
      simp [hg, Finset.Icc_self]
    by_cases hf4 : 4 ≤ f
    · apply ne_alt_of_sixteen_dvd _ hm
      rw [hN]
      have h16 : 16 ∣ 2 ^ f := by
        have := Nat.pow_dvd_pow 2 hf4
        norm_num at this
        exact this
      exact Dvd.dvd.mul_right h16 _
    · have : f = 2 ∨ f = 3 := by omega
      rcases this with rfl | rfl <;>
      · rw [hN]
        exact ne_alt_of_ne (by norm_num) (by norm_num) hm
  ·
    have : Finite (PSU3 2 f) := finite_psu3 f
    obtain ⟨Q⟩ : Nonempty (Sylow 2 (PSU3 2 f)) := inferInstance
    have hQ := (bender_psu3_borel_full f hf Q).2.2.2.2
    have hdvd : Nat.card (Q : Subgroup (PSU3 2 f)) ∣ Nat.card (PSU3 2 f) :=
      Subgroup.card_subgroup_dvd_card _
    apply ne_alt_of_sixteen_dvd _ hm
    rw [Nat.card_congr e.toEquiv]
    refine dvd_trans ?_ hdvd
    rw [hQ]
    exact sixteen_dvd_of_pow (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf) ⟨f, rfl⟩ (by norm_num)
  ·
    have : Finite (Sz a) := finite_sz a
    obtain ⟨Q⟩ : Nonempty (Sylow 2 (Sz a)) := inferInstance
    have hQ := (bender_suzuki_borel_full a ha Q).2.2.2.2
    have hdvd : Nat.card (Q : Subgroup (Sz a)) ∣ Nat.card (Sz a) :=
      Subgroup.card_subgroup_dvd_card _
    apply ne_alt_of_sixteen_dvd _ hm
    rw [Nat.card_congr e.toEquiv]
    refine dvd_trans ?_ hdvd
    rw [hQ]
    exact sixteen_dvd_of_pow (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) ⟨2 * a + 1, rfl⟩
      (by norm_num)


theorem not_centralQuotientAlt_of_psl_three [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) {n : ℕ} (hn : 1 ≤ n)
    (h : StatedClassicalModel ↥L .PSL 3 2 n) {m : ℕ} (hm : m = 6 ∨ m = 7) :
    ¬ CentralQuotientAlt L m := by
  have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n h).2
  refine not_centralQuotientAlt_of_center_bot (center_eq_bot_of_simple hq hs) ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K) := e
  have hN : Nat.card ↥L = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) /
      Nat.gcd 3 (2 ^ n - 1) := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 3) (by norm_num), hK]
    have : Finset.Icc 2 3 = {2, 3} := by decide
    simp [this]
  by_cases hn2 : 2 ≤ n
  · apply ne_alt_of_sixteen_dvd _ hm
    rw [hN]
    have hg : Nat.gcd 3 (2 ^ n - 1) ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
      refine dvd_mul_of_dvd_left ?_ _
      refine dvd_trans (Nat.gcd_dvd_right 3 (2 ^ n - 1)) ?_
      have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
      simpa using this
    rw [Nat.mul_div_assoc _ hg]
    refine Dvd.dvd.mul_right ?_ _
    exact sixteen_dvd_of_pow (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2) ⟨n, rfl⟩ (by norm_num)
  · have : n = 1 := by omega
    subst this
    rw [hN]
    exact ne_alt_of_ne (by norm_num) (by norm_num) hm

theorem not_centralQuotientAlt_of_psp_four [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) {n : ℕ} (hn : 2 ≤ n)
    (h : StatedClassicalModel ↥L .PSp 2 2 n) {m : ℕ} (hm : m = 6 ∨ m = 7) :
    ¬ CentralQuotientAlt L m := by
  have hs : IsSimpleGroup ↥L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n h
  refine not_centralQuotientAlt_of_center_bot (center_eq_bot_of_simple hq hs) ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) := e
  have := charP_two_of_card_eq' hK
  apply ne_alt_of_sixteen_dvd _ hm
  rw [Nat.card_congr e'.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK]
  refine Dvd.dvd.mul_right ?_ _
  exact sixteen_dvd_of_pow (by calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn) ⟨n, rfl⟩ (by norm_num)


theorem not_centralQuotientAlt_of_psl_three_three [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (h : StatedClassicalModel ↥L .PSL 3 3 1) {m : ℕ}
    (hm : m = 6 ∨ m = 7) : ¬ CentralQuotientAlt L m := by
  have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 h).2
  refine not_centralQuotientAlt_of_center_bot (center_eq_bot_of_simple hq hs) ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K) := e
  have hN : Nat.card ↥L = 5616 := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 3) (by norm_num), hK]
    have : Finset.Icc 2 3 = {2, 3} := by decide
    simp [this]
  rw [hN]
  exact ne_alt_of_ne (by norm_num) (by norm_num) hm

theorem not_centralQuotientAlt_of_m11 [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (h : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11))
    {m : ℕ} (hm : m = 6 ∨ m = 7) : ¬ CentralQuotientAlt L m := by
  obtain ⟨e⟩ := h
  have hs : IsSimpleGroup ↥L :=
    e.isSimpleGroup_congr.mpr CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  refine not_centralQuotientAlt_of_center_bot (center_eq_bot_of_simple hq hs) ?_
  have hN : Nat.card ↥L = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  rw [hN]
  exact ne_alt_of_ne (by norm_num) (by norm_num) hm

theorem not_centralQuotientAlt_of_psl_two [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) {p : ℕ} (hp : IsFermatOrMersenne p)
    (h : StatedClassicalModel ↥L .PSL 2 p 1) {m : ℕ} (hm : m = 6 ∨ m = 7) :
    ¬ CentralQuotientAlt L m := by
  have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 h).2
  refine not_centralQuotientAlt_of_center_bot (center_eq_bot_of_simple hq hs) ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
  have h3 : 3 ≤ p := three_le_of_isFermatOrMersenne hp
  have hodd : Odd p := hp.1.odd_of_ne_two (by omega)
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    apply Nat.gcd_eq_left
    rcases hodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hN : Nat.card ↥L = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 2) (by norm_num), hK]
    simp [hg, Finset.Icc_self]
  rw [hN]
  have hp9 : p ≠ 9 := by
    rintro rfl
    exact absurd hp.1 (by norm_num)
  have key : p * (p ^ 2 - 1) / 2 ≠ 360 ∧ p * (p ^ 2 - 1) / 2 ≠ 2520 := by
    constructor
    · intro h360
      have h1 : 720 ≤ p * (p ^ 2 - 1) := by omega
      have h2 : p * (p ^ 2 - 1) ≤ 721 := by omega
      have hp10 : p < 10 := by
        by_contra hge
        push Not at hge
        have : 10 * (10 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := by
          apply Nat.mul_le_mul hge
          exact Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1
        omega
      interval_cases p <;> simp_all
    · intro h2520
      have h1 : 5040 ≤ p * (p ^ 2 - 1) := by omega
      have h2 : p * (p ^ 2 - 1) ≤ 5041 := by omega
      have hp19 : p < 19 := by
        by_contra hge
        push Not at hge
        have : 19 * (19 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := by
          apply Nat.mul_le_mul hge
          exact Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1
        omega
      interval_cases p <;> simp_all
  exact ne_alt_of_ne key.1 key.2 hm


theorem not_centralQuotientAlt_of_quotient [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (h : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2)
    {m : ℕ} (hm : m = 6 ∨ m = 7) : ¬ CentralQuotientAlt L m := by
  have hsX : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).2
  have hnX : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).1
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have e' : (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K) := e
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 3) (by norm_num), hK]
    have : Finset.Icc 2 3 = {2, 3} := by decide
    simp [this]
  rintro ⟨e⟩
  have hsZ : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have h21 : Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := by
    let π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    have hn : ((Subgroup.center ↥L).map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center ↥L).map π) with h0 | h0
    · intro x hx
      have : π x ∈ (Subgroup.center ↥L).map π := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    · exfalso
      have hcomm : ∀ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b = b * a := by
        intro a b
        have ha : a ∈ (Subgroup.center ↥L).map π := by rw [h0]; trivial
        have hb : b ∈ (Subgroup.center ↥L).map π := by rw [h0]; trivial
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨y, hy, rfl⟩ := hb
        calc π x * π y = π (x * y) := (map_mul π x y).symm
          _ = π (y * x) := by rw [Subgroup.mem_center_iff.mp hx y]
          _ = π y * π x := map_mul π y x
      let _ : CommGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
        { (inferInstance : Group (↥L ⧸ CFSG.pCore 2 ↥L)) with mul_comm := hcomm }
      have hpr := IsSimpleGroup.prime_card (α := ↥L ⧸ CFSG.pCore 2 ↥L)
      rw [hcard] at hpr
      exact absurd hpr (by norm_num)
  have heq : Subgroup.center ↥L = CFSG.pCore 2 ↥L := by
    let π₂ := QuotientGroup.mk' (Subgroup.center ↥L)
    have hn : ((CFSG.pCore 2 ↥L).map π₂).Normal :=
      Subgroup.Normal.map inferInstance π₂ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map π₂) with h0 | h0
    · refine le_antisymm h21 ?_
      intro x hx
      have : π₂ x ∈ (CFSG.pCore 2 ↥L).map π₂ := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    · exfalso
      have htop : CFSG.pCore 2 ↥L = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : π₂ x ∈ (CFSG.pCore 2 ↥L).map π₂ := by rw [h0]; trivial
        obtain ⟨y, hy, hyx⟩ := hx
        have hxy : (y⁻¹ * x) ∈ Subgroup.center ↥L := by
          have hyx' : (QuotientGroup.mk y : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk x := hyx
          exact QuotientGroup.eq.mp hyx'
        have : x = y * (y⁻¹ * x) := by group
        rw [this]
        exact Subgroup.mul_mem _ hy (h21 hxy)
      rw [htop] at hnX
      exact (not_nontrivial_iff_subsingleton.mpr (QuotientGroup.subsingleton_quotient_top)) hnX
  apply ne_alt_of_ne (N := 20160) (by norm_num) (by norm_num) hm
  rw [← hcard, ← Nat.card_congr e.toEquiv]
  rw [heq]

end Unc25G2

theorem notAltQuotientFacts : NotAltQuotientFacts := by
  intro G _ _ L hq hL
  suffices h : ∀ m : ℕ, (m = 6 ∨ m = 7) → ¬ CentralQuotientAlt L m from
    ⟨h 6 (Or.inl rfl), h 7 (Or.inr rfl)⟩
  intro m hm
  rcases hL with hB | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | h | h | ⟨p, hp, h⟩
  · exact Unc25G2.not_centralQuotientAlt_of_bender hq hB hm
  · exact Unc25G2.not_centralQuotientAlt_of_psl_three hq hn h hm
  · exact Unc25G2.not_centralQuotientAlt_of_psp_four hq hn h hm
  · exact Unc25G2.not_centralQuotientAlt_of_quotient hq h hm
  · exact Unc25G2.not_centralQuotientAlt_of_psl_three_three hq h hm
  · exact Unc25G2.not_centralQuotientAlt_of_m11 hq h hm
  · exact Unc25G2.not_centralQuotientAlt_of_psl_two hq hp h hm

end CFSG.QuasithinUnique
