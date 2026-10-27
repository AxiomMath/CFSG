module

public import CFSG.Quasithin.H13.L32A706a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A709a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem reduce_F4 (h520 : Lemma14_5_20_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hO : CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H) ≠ ⊥) :
    ∃ Y : Subgroup G, oTwoUpper Y = Y ∧ Y ≤ H ∧ H ≤ Subgroup.normalizer (Y : Set G) ∧
      (∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) ∧ pCoreOf 2 Y < Y ∧
      Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y ∧
      (∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
        N = modO2Image H Y) ∧
      Setting147 G T L V (Y ⊔ (l1 T L V ⊔ T)) ∧
      CFSG.pCore p (↥(Y ⊔ (l1 T L V ⊔ T)) ⧸ CFSG.pCore 2 ↥(Y ⊔ (l1 T L V ⊔ T))) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPn, hPne, -, hPp, hPmin⟩ := exists_minimal_normal_exp hp hO
  set Y₁ : Subgroup G := (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype with hY₁
  have hY₁H : Y₁ ≤ H := Subgroup.map_subtype_le _
  set Y := oTwoUpper Y₁ with hYdef
  have hYY₁ : Y ≤ Y₁ := oTwoUpper_le Y₁
  have hYH : Y ≤ H := hYY₁.trans hY₁H

  have hmemY₁ : ∀ a : ↥H, (a : G) ∈ Y₁ ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥H) a ∈ P :=
      fun a => by
    constructor
    · rintro ⟨b, hb, hba⟩
      rw [show a = b from Subtype.ext hba.symm]
      exact hb
    · exact fun ha => ⟨a, ha, rfl⟩

  have hHY₁ : H ≤ Subgroup.normalizer (Y₁ : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨h, hh⟩ * a * ⟨h, hh⟩⁻¹) ∈ P := by
      rw [map_mul, map_mul, map_inv]
      exact hPn.conj_mem _ ha _
    exact ⟨_, hmem, rfl⟩
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    hHY₁.trans (normalizer_le_normalizer_oTwoUpper Y₁)
  have hYO : oTwoUpper Y = Y := oTwoUpper_oTwoUpper Y₁

  have hY₁p : ∀ y ∈ Y₁, y ^ p ∈ pCoreOf 2 H := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (a ^ p) = 1 := by
      rw [map_pow]; exact hPp _ ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hYp : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y := fun y hy =>
    inf_pCoreOf_le hYH ⟨hY₁p y (hYY₁ hy), Y.pow_mem hy p⟩

  have hYstar : modO2Image H Y = P := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hx
      exact (hmemY₁ a).mp (hYY₁ ha)
    · intro x hx
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) x
      have haY₁ : (a : G) ∈ Y₁ := (hmemY₁ a).mpr hx
      obtain ⟨j, hj⟩ := exists_pow_mem_oTwoUpper Y₁ haY₁
      have hcop : Nat.Coprime (2 ^ j) p :=
        Nat.Coprime.pow_left j ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      have hap : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (a ^ p) = 1 := by
        rw [map_pow]; exact hPp _ hx
      refine mem_modO2Image'.mpr ⟨(a ^ 2 ^ j) ^ u, ?_, ?_⟩
      · rw [Subgroup.coe_zpow, Subgroup.coe_pow]
        exact Y.zpow_mem hj u
      · have e : a = (a ^ 2 ^ j) ^ u * (a ^ p) ^ v := by
          calc a = a ^ (u * ((2 ^ j : ℕ) : ℤ) + v * (p : ℤ)) := by rw [huv, zpow_one]
            _ = (a ^ 2 ^ j) ^ u * (a ^ p) ^ v := by
              rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast,
                zpow_natCast]
        calc QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((a ^ 2 ^ j) ^ u) =
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((a ^ 2 ^ j) ^ u) *
              QuotientGroup.mk' (CFSG.pCore 2 ↥H) (a ^ p) ^ v := by rw [hap, one_zpow, mul_one]
          _ = QuotientGroup.mk' (CFSG.pCore 2 ↥H) a := by rw [← map_zpow, ← map_mul, ← e]

  have hYlt : pCoreOf 2 Y < Y := by
    refine lt_of_le_of_ne (pCoreOf_le 2 Y) fun he => hPne ?_
    have hY2 : IsPGroup 2 ↥Y := he ▸ pCoreOf_isPGroup 2 Y
    rw [← hYstar, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hx
    obtain ⟨k, hk⟩ := hY2 ⟨a, ha⟩
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : a ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have hpx : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a ^ p = 1 :=
      hPp _ ((hmemY₁ a).mp (hYY₁ ha))
    have hd1 := orderOf_dvd_of_pow_eq_one h2
    have hd2 := orderOf_dvd_of_pow_eq_one hpx
    have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a)) (2 ^ k) :=
      Nat.Coprime.coprime_dvd_left hd2
        (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)))
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hd1)

  have hYM : Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y := by
    rcases h520 G T L V H S Y p hp hYH hHY hYp with h | ⟨hp3, -⟩
    · exact h
    · omega
  have hYnM : ¬ Y ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hYlt.ne (by rw [← hYM, inf_eq_left.mpr h])

  have hS₀ : Setting147 G T L V (Y ⊔ (l1 T L V ⊔ T)) := by
    rw [← sup_assoc]
    exact setting_Y0_F4 S h1222 h1332 h1334 (sup_le hYH (l1H' S)) le_sup_right
      fun h => hYnM (le_sup_left.trans h)
  refine ⟨Y, hYO, hYH, hHY, hYp, hYlt, hYM, fun N hNn hNne hNY => ?_, hS₀, ?_⟩
  · rw [hYstar] at hNY ⊢
    exact hPmin N hNn hNne hNY

  set H₀ := Y ⊔ (l1 T L V ⊔ T) with hH₀
  have hH₀H : H₀ ≤ H := sup_le hYH S.hz.1.1
  have hYH₀ : Y ≤ H₀ := le_sup_left
  have hO₂Y : pCoreOf 2 Y ≤ pCoreOf 2 H₀ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH₀)
      ((hH₀H.trans hHY).trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
  have hn : (modO2Image H₀ Y).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := mem_modO2Image'.mp hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H₀) g
    rw [← map_inv, ← map_mul, ← map_mul]
    refine mem_modO2Image'.mpr ⟨h * y * h⁻¹, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ((hH₀H.trans hHY) h.2) y).mp hy
  have hxp : ∀ x ∈ modO2Image H₀ Y, x ^ p = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_modO2Image'.mp hx
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
    simpa using hO₂Y (hYp y hy)
  have hpg : IsPGroup p ↥(modO2Image H₀ Y) := fun x => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hxp x x.2)⟩
  have hne : modO2Image H₀ Y ≠ ⊥ := by
    intro hbot
    apply hYlt.ne
    refine le_antisymm (pCoreOf_le 2 Y) ?_
    have hle : Y ≤ pCoreOf 2 H₀ := fun y hy => by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨y, hYH₀ hy⟩ = 1 := by
        rw [← Subgroup.mem_bot, ← hbot]
        exact mem_modO2Image'.mpr ⟨⟨y, hYH₀ hy⟩, hy, rfl⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
        Subgroup.mem_subgroupOf] at h1
      exact h1
    exact le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
      ((pCoreOf_isPGroup 2 H₀).to_le hle)
  intro hbot
  apply hne
  rw [eq_bot_iff, ← hbot]
  exact le_sSup ⟨hn, hpg⟩

end Setting147

end CFSG.Quasithin.H13.L32A
