module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PT
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PSpM
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoCentralCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PS

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace P211

theorem v2_odd {q : ℕ} (hq : Odd q) : padicValNat 2 q = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr h)

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring_nf; omega
  rw [h]
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  rw [hj]
  exact ⟨j, by ring⟩

theorem three_le_v2 {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) : 3 ≤ padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  exact (padicValNat_dvd_iff_le h0).mp (by simpa using eight_dvd_sq_sub_one hq)

theorem v2_four {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (q ^ 4 - 1) = padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 4 - 1 = ((2 * k + 1) ^ 2 - 1) * (2 * (2 * k * k + 2 * k + 1)) := by
    have : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, Nat.one_le_pow 4 (2 * k + 1) (by omega)]
    ring
  have h0 : (2 * k + 1) ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ (2 * k + 1) ^ 2 := by nlinarith
    omega
  rw [h1, padicValNat.mul h0 (by positivity), padicValNat.mul (by norm_num) (by positivity),
    padicValNat.self (by norm_num), v2_odd (q := 2 * k * k + 2 * k + 1) ⟨k * k + k, by ring⟩]

theorem v2_SL2 {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (q * (q ^ 2 - 1)) = padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  rw [padicValNat.mul (by omega) h0, v2_odd hq, zero_add]

theorem v2_ordA {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (Open.ordA 1 (q ^ 2)) = padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hq
  have hg : Nat.gcd 2 ((2 * k + 1) ^ 2 - 1) = 2 := by
    rw [show (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * k + 2 * k) by ring_nf; omega]
    exact Nat.gcd_mul_right_right _ 2
  have h2 : 2 ∣ ((2 * k + 1) ^ 2) ^ 2 - 1 :=
    ⟨2 * ((2 * k + 1) ^ 2 * (k * k + k)) + 2 * k * k + 2 * k, by ring_nf; omega⟩
  have hx : Open.ordA 1 ((2 * k + 1) ^ 2) * 2 = (2 * k + 1) ^ 2 * ((2 * k + 1) ^ 4 - 1) := by
    rw [Open.ordA, hg, show Finset.Icc 2 (1 + 1) = {2} by rfl, Finset.prod_singleton,
      show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, Nat.div_mul_cancel (Dvd.dvd.mul_left h2 _),
      ← pow_mul]
  have h4 : (2 * k + 1) ^ 4 - 1 ≠ 0 := by
    have : 1 < (2 * k + 1) ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hx0 : Open.ordA 1 ((2 * k + 1) ^ 2) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hx
    exact Nat.mul_ne_zero (by positivity) h4 hx.symm
  have := congrArg (padicValNat 2) hx
  rw [padicValNat.mul hx0 (by norm_num), padicValNat.self (by norm_num),
    padicValNat.mul (by positivity) h4, padicValNat.pow, v2_odd ⟨k, rfl⟩,
    v2_four ⟨k, rfl⟩ hq3] at this
  omega

theorem v2_ordBC {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (Open.ordBC 2 q) = 2 * padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx := ordBC_two_mul hq
  have h0 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have h4 : q ^ 4 - 1 ≠ 0 := by
    have : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hx0 : Open.ordBC 2 q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hx
    exact Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero h0 h4) hx.symm
  have := congrArg (padicValNat 2) hx
  rw [padicValNat.mul hx0 (by norm_num), padicValNat.self (by norm_num),
    padicValNat.mul (by positivity) (Nat.mul_ne_zero h0 h4), padicValNat.pow,
    v2_odd hq, padicValNat.mul h0 h4, v2_four hq hq3] at this
  omega

theorem le_v2_of_dvd {k y x : ℕ} (hx : x ≠ 0) (hk : 2 ^ k ∣ y) (hy : y ∣ x) :
    k ≤ padicValNat 2 x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (padicValNat_dvd_iff_le hx).mp (hk.trans hy)

theorem v2_card_quot {Y : Type*} [Group Y] [Finite Y] :
    padicValNat 2 (Nat.card Y) = padicValNat 2 (Nat.card (Y ⧸ pPrimeCore 2 Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 Y)
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 Y)) := pPrimeCore_coprime_card
  rw [hO, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
    v2_odd (Nat.coprime_two_left.mp hcop), add_zero]

end P211

open P211

theorem cf81E6P211Sp4 : CF81E6P211Sp4 := by
  intro X _ _ hsimp hC ⟨p', f', hp', hp2', hf', hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  exfalso
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨-, -, K', _, _, hK', ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hLie
  set F := generalizedFitting X with hFdef
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have hq'odd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp2').pow
  have hq'3 : 3 ≤ p' ^ f' :=
    le_trans (by have := hp'.two_le; omega) (Nat.le_self_pow (by omega) p')
  have hchar' : ringChar K' ≠ 2 := GH74.Generic.ringChar_ne_two_of_card_eq hp' hp2' hK'
  have hKF : K ≤ F :=
    le_fstar_of_perfect hC e (derivedSeries_two_le_PSp hchar') (commutator_eq_of_isPComp hKC hK)
  have hFcard : Nat.card F = Open.ordBC 2 (p' ^ f') :=
    GH74.card_of_lieModel_PSp (by norm_num) hp2' hLie
  set n := padicValNat 2 ((p' ^ f') ^ 2 - 1) with hn
  set m := padicValNat 2 ((p ^ f) ^ 2 - 1) with hm
  have hn3 : 3 ≤ n := three_le_v2 hq'odd hq'3
  have hD : Nat.card D = 2 ^ m := by
    obtain ⟨R, hR⟩ := hDsyl
    have h1 := R.card_eq_multiplicity
    rw [hR, Nat.factorization_def _ Nat.prime_two, v2_card_quot, card_sec8J hJt,
      show p ^ (2 * f) = (p ^ f) ^ 2 by ring, v2_ordA hqodd hq3] at h1
    rw [← h1]
    exact (Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv).symm
  have hKv : 2 ^ (2 * m) ∣ Nat.card K := by
    refine dvd_trans ?_ (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K))
    rcases hKt with hL | ⟨rfl, rfl, ⟨eA⟩⟩
    · rw [GH74.card_of_lieModel_PSp (by norm_num) hp2 hL, ← v2_ordBC hqodd hq3]
      exact pow_padicValNat_dvd
    · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hm,
        show (3 ^ 1) ^ 2 - 1 = 2 ^ 3 by norm_num, padicValNat.prime_pow]
      decide
  have hnm : n ≤ m := by
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥F) := inferInstance
    have hT := T.card_eq_multiplicity
    rw [Nat.factorization_def _ Nat.prime_two, hFcard, v2_ordBC hq'odd hq'3] at hT
    have hb2 := hbound ((T : Subgroup ↥F).map F.subtype) (map_subtype_le _) (T.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective F.subtype_injective, hT, hD, ← pow_mul 2 m 2,
      ← pow_succ'] at hb2
    have := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hb2
    omega
  have hK2n : 2 ^ (2 * n) ∣ Nat.card K := (pow_dvd_pow 2 (by omega)).trans hKv
  by_cases h3 : p' ^ f' = 3
  · have hF3 : Nat.card F = 25920 := by rw [hFcard, h3]; decide
    have hKd : Nat.card K ∣ 25920 := hF3 ▸ Subgroup.card_dvd_of_le hKF
    have hK20 := le_card_of_socle hp hp2 hf hKt
    have hKeq : Nat.card K = 25920 := by
      obtain ⟨c, hc⟩ := hKd
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · interval_cases c <;> omega
      · nlinarith
    exact hb1 (eq_one_of_card_le hC hKF hKC (by rw [hF3, hKeq]))
  have h5 : 5 ≤ p' ^ f' := by
    obtain ⟨k, hk⟩ := hq'odd
    omega
  have := hsimp
  have hsP : IsSimpleGroup (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K')) :=
    e.symm.isSimpleGroup
  set α₀ : MulAut ↥F := MulAut.conjNormal b with hα₀
  set α : MulAut (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K')) :=
    MulAut.congr e α₀ with hαdef
  have hcomm : ∀ x, e (α₀ x) = α (e x) := fun x => by
    simp [hαdef, MulAut.congr_apply]
  have hα2 : α * α = 1 := by
    have h1 : α₀ * α₀ = 1 := by rw [hα₀, ← map_mul, hb, map_one]
    rw [hαdef, ← map_mul, h1, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have h1 : α₀ = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
    exact hb1 (conjNormal_injective' F hC (h1.trans (map_one _).symm))
  have hfix : CatFactsSp4.fixOf α₀ = (centralizer ({b} : Set X)).subgroupOf F := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_iff]
    change α₀ x = x ↔ _
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := congrArg Subtype.val h
      simp only [hα₀, MulAut.conjNormal_apply] at h1
      calc b * (x : X) = b * (x : X) * b⁻¹ * b := by group
        _ = x * b := by rw [h1]
    · intro h
      apply Subtype.ext
      simp only [hα₀, MulAut.conjNormal_apply]
      rw [h b rfl, mul_inv_cancel_right]
  have hK₀C : K.subgroupOf F ≤ (centralizer ({b} : Set X)).subgroupOf F :=
    fun x hx => hKC hx
  have hK₀X : K.subgroupOf F ≤ CatFactsSp4.fixOf α₀ := hfix ▸ hK₀C
  have hK₀ : IsPComponent 2 ((K.subgroupOf F).subgroupOf (CatFactsSp4.fixOf α₀)) := by
    rw [hfix, ← CatFactsSp4.isPComponent_map_subgroupOf_iff 2 F.subtype F.subtype_injective hK₀C,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hKF]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKC hKF) inf_le_left hK
  obtain ⟨hMX, hM⟩ := CatFactsSp4.isPComponent_map_fixOf hcomm hK₀X hK₀
  have hcardM : Nat.card ((K.subgroupOf F).map e.toMonoidHom) = Nat.card K := by
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hKF).toEquiv
  rcases card_dvd_of_pComponent hp' hp2' hf' hK' h5 hsP α hα2 hα1 hMX hM with h | h | ⟨k, hk, h⟩
  · rw [hcardM] at h
    have h0 : p' ^ f' * ((p' ^ f') ^ 2 - 1) ≠ 0 := by
      have : 9 ≤ (p' ^ f') ^ 2 := by nlinarith
      exact Nat.mul_ne_zero (by omega) (by omega)
    have := le_v2_of_dvd h0 hK2n h
    rw [v2_SL2 hq'odd hq'3] at this
    omega
  · rw [hcardM, show ((p' ^ f') ^ 2) ^ 2 = (p' ^ f') ^ 4 by ring] at h
    have h4 : (p' ^ f') ^ 4 - 1 ≠ 0 := by
      have : 81 ≤ (p' ^ f') ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ (p' ^ f') ^ 4 := Nat.pow_le_pow_left hq'3 4
      omega
    have h0 : (p' ^ f') ^ 2 * ((p' ^ f') ^ 4 - 1) ≠ 0 := Nat.mul_ne_zero (by positivity) h4
    have := le_v2_of_dvd h0 hK2n h
    rw [padicValNat.mul (by positivity) h4, padicValNat.pow, v2_odd hq'odd,
      v2_four hq'odd hq'3] at this
    omega
  · rw [hcardM] at h
    have hkodd : Odd k := by
      have : Odd (k ^ 2) := hk ▸ hq'odd
      exact (Nat.odd_mul.mp (by rwa [sq] at this)).1
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k <;> omega
    have h2k : k ^ 2 - 1 ≠ 0 := by
      have : 9 ≤ k ^ 2 := by nlinarith
      omega
    have h4k : k ^ 4 - 1 ≠ 0 := by
      have : 81 ≤ k ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ k ^ 4 := Nat.pow_le_pow_left hk3 4
      omega
    have h0 : k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) ≠ 0 :=
      Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero h2k h4k)
    have := le_v2_of_dvd h0 hK2n h
    rw [padicValNat.mul (by positivity) (Nat.mul_ne_zero h2k h4k), padicValNat.pow,
      v2_odd hkodd, padicValNat.mul h2k h4k, v2_four hkodd hk3] at this
    have hnk : n = padicValNat 2 (k ^ 2 - 1) + 1 := by
      rw [hn, ← hk, ← pow_mul, v2_four hkodd hk3]
    omega

end CFSG.ComponentClassification.GSThmB
