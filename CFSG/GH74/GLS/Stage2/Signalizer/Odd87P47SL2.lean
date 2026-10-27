module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GH74.GLS.Stage4.T6Borel
public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.GLS.Stage4.T6Grp
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
  CFSG.GH74.GLS.Stage4.Rest.T6
open scoped Pointwise

section Transfer

variable {A : Type} [Group A]

theorem p47_le_normalizer_of_map {K : Subgroup A} {S T : Subgroup K} {X Q : Subgroup A}
    (hX : S.map K.subtype = X) (hQ : T.map K.subtype = Q) (h : Q ≤ normalizer (X : Set A)) :
    T ≤ normalizer (S : Set K) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have hmem : ∀ y : K, y ∈ S ↔ (y : A) ∈ X := fun y => by
    rw [← hX]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have htQ : (t : A) ∈ Q := hQ ▸ Subgroup.mem_map_of_mem K.subtype ht
  have h1 := Subgroup.mem_normalizer_iff.1 (h htQ) (s : A)
  rw [hmem, hmem]
  simpa using h1

end Transfer

section Arith

theorem p47_not_two_pow_dvd {r : ℕ} (hr : Odd r) (hr3 : 3 ≤ r) :
    ¬ 2 ^ (r * (r ^ 2 - 1)).factorization 2 ∣ r * (r - 1) := by
  intro hd
  have hab : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, show 1 ≤ r by omega]
    ring
  have ha : r - 1 ≠ 0 := by omega
  have hb : r + 1 ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  have hr2 : ¬ 2 ∣ r := hr.not_two_dvd_nat
  have hb2 : 2 ∣ r + 1 := by
    obtain ⟨m, rfl⟩ := hr
    exact ⟨m + 1, by ring⟩
  have hfb : 1 ≤ (r + 1).factorization 2 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hb hb2)
  have hfac : (r * (r ^ 2 - 1)).factorization 2 =
      (r - 1).factorization 2 + (r + 1).factorization 2 := by
    rw [hab, Nat.factorization_mul hr0 (Nat.mul_ne_zero ha hb), Finsupp.add_apply,
      Nat.factorization_mul ha hb, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hr2,
      zero_add]
  rw [hfac] at hd
  have hcop : Nat.Coprime (2 ^ ((r - 1).factorization 2 + (r + 1).factorization 2)) r :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hr2)
  have hd' := hcop.dvd_of_dvd_mul_left hd
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha).1 hd'
  omega

end Arith

section Core

theorem p47_factorization_card_sl2 {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hq : Nat.card F = p ^ n) (hn : n ≠ 0) :
    (Nat.card (SL2 F)).factorization p = n := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hq]
  have h0 : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero
  have hpd : ¬ p ∣ (p ^ n) ^ 2 - 1 := by
    intro hd
    have h2 : p ∣ (p ^ n) ^ 2 := dvd_pow (dvd_pow_self p hn) (by norm_num)
    have h3 : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero h0)
    have : p ∣ 1 := by
      have := Nat.dvd_sub h2 hd
      rwa [Nat.sub_sub_self h3] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hne : (p ^ n) ^ 2 - 1 ≠ 0 := by
    have : 2 ≤ p ^ n := by
      have := Nat.one_lt_pow hn hp.one_lt
      omega
    have : 4 ≤ (p ^ n) ^ 2 := by nlinarith
    omega
  rw [Nat.factorization_mul h0 hne, Finsupp.add_apply, hp.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd hpd]
  simp

theorem p47_core {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (φ : SL2 F ≃* K) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hF : Nat.card F = p ^ n) (S : Sylow p K) (T : Sylow 2 K) :
    ¬ (T : Subgroup K) ≤ normalizer ((S : Subgroup K) : Set K) := by
  intro hTS
  have hp : p.Prime := Fact.out
  have hodd' : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card F) := hF ▸ hodd'
  have hFcard : 3 ≤ Nat.card F := by
    have h1 := Nat.one_lt_pow hn hp.one_lt
    rw [hF]
    obtain ⟨m, hm⟩ := hodd'
    omega
  have hK : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr φ.toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  have hfac : (Nat.card K).factorization p = n := by
    rw [← Nat.card_congr φ.toEquiv]
    exact p47_factorization_card_sl2 hp hF hn
  let U : Subgroup K := (uSub F).map φ.toMonoidHom
  have hUcard : Nat.card U = p ^ (Nat.card K).factorization p := by
    rw [hfac, Subgroup.card_map_of_injective φ.injective, card_uSub, hF]
  let PU : Sylow p K := Sylow.ofCard U hUcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K PU S
  let φ' : SL2 F →* K := (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom
  have hinj : Function.Injective φ' := (MulAut.conj g).injective.comp φ.injective
  have hrange : φ'.range = ⊤ :=
    MonoidHom.range_eq_top.2 ((MulAut.conj g).surjective.comp φ.surjective)
  have hSU : (S : Subgroup K) = (uSub F).map φ' := by
    have h1 : (S : Subgroup K) = MulAut.conj g • (PU : Subgroup K) := by
      rw [← hg]
      exact Sylow.coe_subgroup_smul
    rw [h1]
    show U.map (MulAut.conj g).toMonoidHom =
      (uSub F).map ((MulAut.conj g).toMonoidHom.comp φ.toMonoidHom)
    rw [← Subgroup.map_map]
  have h1 := t6_card_normalizer_dvd (G := K) (F := F) (φ := φ') hinj
  rw [← hSU, hrange, inf_top_eq] at h1
  have h2 : Nat.card (T : Subgroup K) ∣ Nat.card F * (Nat.card F - 1) :=
    (Subgroup.card_dvd_of_le hTS).trans h1
  rw [Sylow.card_eq_multiplicity T, hK] at h2
  exact p47_not_two_pow_dvd hodd hFcard h2

end Core

section Main

variable {A : Type} [Group A] [Finite A]

theorem not_sylow2_le_normalizer_C43b {p : ℕ} {X : Subgroup A} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : C43b p X) {Q : Subgroup A} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (ncl X)) :
    ¬ Q ≤ normalizer (X : Set A) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn3, hmodel, S, hS⟩ := hX
  obtain ⟨T, hT⟩ := hQ
  obtain ⟨F, _, _, hFq, ⟨φ⟩⟩ := CFSG.GH74.Generic.S1.exists_sl2_equiv hmodel
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hn3
  intro hQN
  exact p47_core φ hp2 hn hFq S T (p47_le_normalizer_of_map hS hT hQN)

theorem p47_factorization_120_two : (120 : ℕ).factorization 2 = 3 := by
  rw [show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.prime_two.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem p47_factorization_120_three : (120 : ℕ).factorization 3 = 1 := by
  rw [show (120 : ℕ) = 3 * 40 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem not_sylow2_le_normalizer_C43e {X : Subgroup A} (hX : C43e X) {Q : Subgroup A}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (ncl X)) : ¬ Q ≤ normalizer (X : Set A) := by
  classical
  obtain ⟨hmodel, hcard⟩ := hX
  obtain ⟨T, hT⟩ := hQ
  intro hQN
  have hXK : X ≤ ncl X := Subgroup.subset_normalClosure
  obtain ⟨F, _, _, hF5, ⟨φ⟩⟩ := CFSG.GH74.Generic.S1.exists_sl2_equiv hmodel
  have hq : CFSG.IsQuasisimple ↥(ncl X) :=
    CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 (by norm_num) hmodel
  let X' : Subgroup ↥(ncl X) := X.subgroupOf (ncl X)
  have hX' : X'.map (ncl X).subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hXK]
  have hTS : (T : Subgroup ↥(ncl X)) ≤ normalizer (X' : Set ↥(ncl X)) :=
    p47_le_normalizer_of_map hX' hT hQN
  have hK : Nat.card ↥(ncl X) = 120 := by
    rw [← Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF5]
    norm_num
  have hX'card : Nat.card X' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
    exact hcard
  have hTcard : Nat.card (T : Subgroup ↥(ncl X)) = 8 := by
    rw [Sylow.card_eq_multiplicity T, hK, p47_factorization_120_two]
    norm_num
  have hTindex : (T : Subgroup ↥(ncl X)).index = 15 := by
    have h1 := Subgroup.card_mul_index (T : Subgroup ↥(ncl X))
    rw [hTcard, hK] at h1
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let PX : Sylow 3 ↥(ncl X) :=
    Sylow.ofCard X' (by rw [hK, p47_factorization_120_three, hX'card]; norm_num)
  have h1 := card_sylow_modEq_one 3 ↥(ncl X)
  rw [PX.card_eq_index_normalizer] at h1
  have h2 : (normalizer (X' : Set ↥(ncl X))).index ∣ (T : Subgroup ↥(ncl X)).index :=
    Subgroup.index_dvd_of_le hTS
  rw [hTindex] at h2
  have hm : (normalizer (X' : Set ↥(ncl X))).index = 1 := by
    have hle : (normalizer (X' : Set ↥(ncl X))).index ≤ 15 := Nat.le_of_dvd (by norm_num) h2
    have h1' : (normalizer (X' : Set ↥(ncl X))).index % 3 = 1 := h1
    generalize (normalizer (X' : Set ↥(ncl X))).index = m at hle h1' h2 ⊢
    interval_cases m <;> omega
  have hnormal : X'.Normal :=
    normalizer_eq_top_iff.1 (Subgroup.index_eq_one.1 hm)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hnormal with htop | hcen
  · have : Nat.card X' = Nat.card ↥(ncl X) := by rw [htop]; exact Subgroup.card_top
    omega
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X') 3 (by rw [hX'card])
    obtain ⟨t, htV, ht2, -, hcentral⟩ :=
      CFSG.GH74.Generic.S1.sl2_involution_facts (by decide : Odd 5) hmodel
    have hy : ((x : ↥X') : ↥(ncl X)) ∈ center ↥(ncl X) := hcen x.2
    have hz : ∀ w ∈ ncl X, (((x : ↥X') : ↥(ncl X)) : A) * w = w * (((x : ↥X') : ↥(ncl X)) : A) := by
      intro w hw
      have h3 := Subgroup.mem_center_iff.1 hy ⟨w, hw⟩
      exact (congrArg Subtype.val h3).symm
    have h4 : orderOf ((((x : ↥X') : ↥(ncl X)) : A)) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    rcases hcentral _ ((x : ↥X') : ↥(ncl X)).2 hz with h5 | h5
    · rw [h5, orderOf_one] at h4
      omega
    · rw [h5, ht2] at h4
      omega

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
