module

public import CFSG.GroupTheory.OddInversion
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Elements
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Toolkit

variable {X : Type*} [Group X] [Finite X]

theorem exists_involution_mem_zpowers_coset {N : Subgroup X} (hN : Odd (Nat.card N)) {c : X}
    (hc : c * c ∈ N) (hcN : c ∉ N) :
    ∃ y ∈ zpowers c, orderOf y = 2 ∧ y * c⁻¹ ∈ N := by
  have hodd2 : Odd (orderOf (c * c)) :=
    Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hc)
  have hsq : orderOf (c * c) = orderOf c / (orderOf c).gcd 2 := by
    rw [← sq]
    exact orderOf_pow' c two_ne_zero
  have heven : Even (orderOf c) := by
    by_contra h
    rw [Nat.not_even_iff_odd] at h
    obtain ⟨k, hk⟩ := h
    apply hcN
    have : (c * c) ^ (k + 1) = c := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
        pow_orderOf_eq_one, one_mul]
    rw [← this]
    exact N.pow_mem hc (k + 1)
  obtain ⟨m, hm⟩ := heven
  have hm2 : orderOf c = 2 * m := by omega
  have hmpos : 0 < m := by
    have := orderOf_pos c
    omega
  have hsq' : orderOf (c * c) = m := by
    rw [hsq, hm2, Nat.gcd_eq_right (dvd_mul_right 2 m), Nat.mul_div_cancel_left _ two_pos]
  rw [hsq'] at hodd2
  obtain ⟨k, hk⟩ := hodd2
  refine ⟨c ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers c) m, ?_, ?_⟩
  · rw [orderOf_pow' c hmpos.ne', hm2, Nat.gcd_eq_right (dvd_mul_left m 2),
      Nat.mul_div_cancel _ hmpos]
  · have : c ^ m * c⁻¹ = (c * c) ^ k := by
      rw [← sq, ← pow_mul, hk, pow_succ, mul_inv_cancel_right]
    rw [this]
    exact N.pow_mem hc k

theorem exists_fixed_mem_coset {N : Subgroup X} (hN : Odd (Nat.card N)) {w d : X}
    (hw : w * w = 1) (hwN : w ∈ normalizer (N : Set X)) (hdN : d ∈ normalizer (N : Set X))
    (hd : w * d * w⁻¹ * d⁻¹ ∈ N) : ∃ n ∈ N, w * (d * n) * w⁻¹ = d * n := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hu : d⁻¹ * w * d * w⁻¹ ∈ N := by
    have h := (Subgroup.mem_normalizer_iff.mp ((normalizer (N : Set X)).inv_mem hdN)
      (w * d * w⁻¹ * d⁻¹)).mp hd
    have e : d⁻¹ * (w * d * w⁻¹ * d⁻¹) * d⁻¹⁻¹ = d⁻¹ * w * d * w⁻¹ := by group
    rwa [e] at h
  have hmem : ∀ n : N, d⁻¹ * w * d * (n : X) * w⁻¹ ∈ N := by
    intro n
    have e : d⁻¹ * w * d * (n : X) * w⁻¹ = (d⁻¹ * w * d * w⁻¹) * (w * (n : X) * w⁻¹) := by group
    rw [e]
    exact N.mul_mem hu ((Subgroup.mem_normalizer_iff.mp hwN _).mp n.2)
  let f : N → N := fun n => ⟨d⁻¹ * w * d * (n : X) * w⁻¹, hmem n⟩
  have hf : Function.Involutive f := by
    intro n
    apply Subtype.ext
    show d⁻¹ * w * d * (d⁻¹ * w * d * (n : X) * w⁻¹) * w⁻¹ = n
    rw [hwi]
    calc d⁻¹ * w * d * (d⁻¹ * w * d * (n : X) * w) * w
        = d⁻¹ * (w * w) * d * (n : X) * (w * w) := by group
      _ = n := by rw [hw]; group
  have : Fintype N := Fintype.ofFinite N
  let σ : Equiv.Perm N := hf.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext n
    exact congrArg Subtype.val (hf n)
  have hcard : ¬ 2 ∣ Fintype.card N := by
    rw [← Nat.card_eq_fintype_card]
    exact hN.not_two_dvd_nat
  obtain ⟨n, hn⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨n, n.2, ?_⟩
  have h : d⁻¹ * w * d * (n : X) * w⁻¹ = n := congrArg Subtype.val hn
  calc w * (d * (n : X)) * w⁻¹ = d * (d⁻¹ * w * d * (n : X) * w⁻¹) := by group
    _ = d * n := by rw [h]

theorem exists_commuting_involution_conj {N : Subgroup X} (hN : Odd (Nat.card N)) {x y : X}
    (hx : x * x = 1) (hy : orderOf y = 2) (hxN : x ∈ normalizer (N : Set X))
    (hyN : y ∈ normalizer (N : Set X)) (hxy : x * y * x⁻¹ * y⁻¹ ∈ N) :
    ∃ b ∈ N, x * (b⁻¹ * y * b) = (b⁻¹ * y * b) * x := by
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyNot : y ∉ N := CFSG.OddInversion.notMem_of_odd_card hN hy
  obtain ⟨n, hnN, hfix⟩ := exists_fixed_mem_coset hN hx hxN hyN hxy
  have hyn : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hyN n).mp hnN
  have hcc : (y * n) * (y * n) ∈ N := by
    have e : (y * n) * (y * n) = (y * n * y⁻¹) * n := by
      rw [hyi]
      group
    rw [e]
    exact N.mul_mem hyn hnN
  have hcN : y * n ∉ N := by
    intro h
    apply hyNot
    have := N.mul_mem h (N.inv_mem hnN)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨y₁, hy₁mem, hy₁ord, hy₁N⟩ := exists_involution_mem_zpowers_coset hN hcc hcN
  have hcomm : Commute x (y * n) := by
    have : x * (y * n) * x⁻¹ = y * n := hfix
    exact mul_inv_eq_iff_eq_mul.mp this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy₁mem
  have hcomm₁ : x * y₁ = y₁ * x := by
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  have hy₁y : y₁ * y⁻¹ ∈ N := by
    have e : y₁ * y⁻¹ = (y₁ * (y * n)⁻¹) * (y * n * y⁻¹) := by group
    rw [e]
    exact N.mul_mem hy₁N hyn
  have hcoset := (CFSG.OddInversion.odd_inversion_coset_count hN hyN hyNot hy).1
  have hmem : y₁ ∈ {v : X | v * y⁻¹ ∈ N ∧ orderOf v = 2} := ⟨hy₁y, hy₁ord⟩
  rw [hcoset] at hmem
  obtain ⟨b, hbN, hb⟩ := hmem
  refine ⟨b, hbN, ?_⟩
  rw [← hb]
  exact hcomm₁

theorem pPrimeCore_quotient_pPrimeCore (X : Type*) [Group X] [Finite X] :
    pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2

omit [Finite X] in
theorem pPrimeCore_quotient_central_two {A : Subgroup X} [A.Normal] (hA : A ≤ center X)
    (hA2 : Nat.card A = 2) (h : pPrimeCore 2 X = ⊥) : pPrimeCore 2 (X ⧸ A) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCore_eq_bot_iff]
  intro Q hQ hQcop
  let π : X →* X ⧸ A := QuotientGroup.mk' A
  let U : Subgroup X := Q.comap π
  have hUn : U.Normal := hQ.comap π
  have hAU : A ≤ U := fun a ha => by
    have h1 : π a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    show π a ∈ Q
    rw [h1]
    exact Q.one_mem
  have hUcard : Nat.card U = Nat.card A * Nat.card Q :=
    QuotientGroup.card_preimage_mk A (Q : Set (X ⧸ A))
  have hQodd : Odd (Nat.card Q) := Nat.coprime_two_left.mp hQcop
  have hA'card : Nat.card (A.subgroupOf U) = 2 := by
    rw [← hA2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAU).toEquiv
  have hidx : (A.subgroupOf U).index = Nat.card Q := by
    have := (A.subgroupOf U).card_mul_index
    rw [hA'card, hUcard, hA2] at this
    omega
  have hcop : Nat.Coprime (Nat.card (A.subgroupOf U)) (A.subgroupOf U).index := by
    rw [hA'card, hidx]
    exact hQcop
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime (N := A.subgroupOf U) hcop
  have hK'card : Nat.card K' = Nat.card Q := by
    have := hK'.card_mul_card
    rw [hA'card, hUcard, hA2] at this
    omega
  let K : Subgroup X := K'.map U.subtype
  have hKcard : Nat.card K = Nat.card Q := by
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact hK'card
  have hkm : ∀ k ∈ K, k ^ Nat.card Q = 1 := by
    rintro _ ⟨k', hk', rfl⟩
    have := pow_card_eq_one' (G := K') (x := ⟨k', hk'⟩)
    rw [hK'card] at this
    have h2 := congrArg (fun z : K' => ((z : U) : X)) this
    simpa using h2
  have hkey : ∀ u ∈ U, u ^ Nat.card Q = 1 → u ∈ K := by
    intro u hu hum
    obtain ⟨⟨a', k'⟩, hak⟩ := hK'.2 ⟨u, hu⟩
    have hu' : (((a' : U) : X)) * (((k' : U)) : X) = u := congrArg Subtype.val hak
    have haA : (((a' : U) : X)) ∈ A := a'.2
    have hkK : (((k' : U)) : X) ∈ K := ⟨(k' : U), k'.2, rfl⟩
    have hcomm : Commute (((a' : U) : X)) (((k' : U)) : X) :=
      ((Subgroup.mem_center_iff.mp (hA haA) _)).symm
    have ha2 : (((a' : U) : X)) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := A) (x := ⟨_, haA⟩)
      rw [hA2] at this
      simpa using congrArg Subtype.val this
    have ham : (((a' : U) : X)) ^ Nat.card Q = ((a' : U) : X) := by
      obtain ⟨j, hj⟩ := hQodd
      rw [hj, pow_succ, pow_mul, ha2, one_pow, one_mul]
    have : u ^ Nat.card Q = ((a' : U) : X) := by
      rw [← hu', hcomm.mul_pow, ham, hkm _ hkK, mul_one]
    have ha1 : ((a' : U) : X) = 1 := by rw [← this, hum]
    rw [ha1, one_mul] at hu'
    rw [← hu']
    exact hkK
  have hKn : K.Normal := by
    refine ⟨fun k hk x => ?_⟩
    have hkU : k ∈ U := by
      obtain ⟨k', -, rfl⟩ := hk
      exact k'.2
    apply hkey
    · exact hUn.conj_mem k hkU x
    · rw [conj_pow, hkm k hk, mul_one, mul_inv_cancel]
  have hKcop : Nat.Coprime 2 (Nat.card K) := by
    rw [hKcard]
    exact hQcop
  have hKle : K ≤ pPrimeCore 2 X := le_sSup ⟨hKn, hKcop⟩
  rw [h, le_bot_iff] at hKle
  rw [hKle, Subgroup.card_bot] at hKcard
  exact Subgroup.card_eq_one.mp hKcard.symm

theorem exists_sylow_map_subtype_eq_inf {N : Subgroup X} (hN : N.Normal) (S : Sylow 2 X) :
    ∃ P : Sylow 2 ↥N, (P : Subgroup ↥N).map N.subtype = (S : Subgroup X) ⊓ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : ABGLocalTools.IsSylowOf 2 (S : Subgroup X) ⊤ := by
    rw [ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  exact ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS le_top
    (by rw [Subgroup.normalizer_eq_top])

theorem exists_abelian_elemental_normal_of_solvable {N : Subgroup X} (hN : N.Normal)
    (hs : Group.IsSolvable ↥N) (hne : N ≠ ⊥) :
    ∃ (p : ℕ) (_ : p.Prime) (B : Subgroup X), B.Normal ∧ B ≠ ⊥ ∧ B ≤ N ∧
      (∀ b ∈ B, b ^ p = 1) ∧ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  classical
  have hex : ∃ n, derivedSeries ↥N n = ⊥ := (Group.isSolvable_def _).mp hs
  have h0 : derivedSeries ↥N (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hn₀ : Nat.find hex ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : ↥N) ∈ (⊥ : Subgroup ↥N) := h0 ▸ Subgroup.mem_top _
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp this)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
  have hD : derivedSeries ↥N n ≠ ⊥ := Nat.find_min hex (by omega)
  have hD1 : derivedSeries ↥N (n + 1) = ⊥ := by rw [← Nat.succ_eq_add_one, ← hn]; exact h0
  have hcomm : ∀ a ∈ derivedSeries ↥N n, ∀ b ∈ derivedSeries ↥N n, a * b = b * a := by
    intro a ha b hb
    have h := Subgroup.commutator_mem_commutator ha hb
    rw [← derivedSeries_succ, hD1, Subgroup.mem_bot] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have := hN
  let A : Subgroup X := (derivedSeries ↥N n).map N.subtype
  have hAn : A.Normal := inferInstance
  have hAN : A ≤ N := Subgroup.map_subtype_le _
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm a ha b hb)
  have hAne : A ≠ ⊥ := by
    intro h
    apply hD
    rw [eq_bot_iff]
    intro x hx
    have : (x : X) ∈ A := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    simpa using Subtype.ext this
  have hcard : Nat.card A ≠ 1 := fun h => hAne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpd
  let B : Subgroup X :=
    { carrier := {b | b ∈ A ∧ b ^ p = 1}
      one_mem' := ⟨A.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        have hc : Commute a b := hAcomm a ha.1 b hb.1
        rw [hc.mul_pow, ha.2, hb.2, mul_one]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  refine ⟨p, hp, B, ⟨fun a ha g => ⟨hAn.conj_mem a ha.1 g, ?_⟩⟩, ?_, fun x hx => hAN hx.1,
    fun x hx => hx.2, fun a ha b hb => hAcomm a ha.1 b hb.1⟩
  · rw [conj_pow, ha.2, mul_one, mul_inv_cancel]
  · intro hB
    have hb1 : (b : X) ∈ B := ⟨b.2, by
      have := pow_orderOf_eq_one b
      rw [hb] at this
      simpa using congrArg Subtype.val this⟩
    rw [hB, Subgroup.mem_bot] at hb1
    have hb2 : b = 1 := Subtype.ext hb1
    rw [hb2, orderOf_one] at hb
    exact hp.one_lt.ne hb

theorem exists_commuting_involutions_of_two_le_pRank {H : Subgroup X}
    (hH : 2 ≤ Open.pRank 2 H) :
    ∃ a b : X, a ∈ H ∧ b ∈ H ∧ orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by decide : 1 < 2) H
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Open.pRank 2 H := Nat.pow_le_pow_right (by norm_num) hH
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, haE⟩, ha1⟩ := exists_ne (1 : E)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hE.2 a haE) ha1'
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers a from hall)
    rw [Nat.card_zpowers, ha2] at hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  refine ⟨a, b, hEH haE, hEH hbE, ha2, orderOf_eq_prime (hE.2 b hbE) hb1,
    fun h => hba (h ▸ Subgroup.mem_zpowers a), ?_⟩
  exact congrArg Subtype.val (@mul_comm' E _ hE.1 ⟨a, haE⟩ ⟨b, hbE⟩)

theorem two_le_pRank_of_commute_involutions {H : Subgroup X} {a b : X} (haH : a ∈ H)
    (hbH : b ∈ H) (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b)
    (hab : a * b = b * a) : 2 ≤ Open.pRank 2 H := by
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    norm_num at ha
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    norm_num at hb
  have hba : b * a = a * b := hab.symm
  have ha_ab : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have hb_ab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hbb, mul_one]
  have hab_a : (a * b) * a = b := by rw [mul_assoc, hba, ha_ab]
  have hab_b : (a * b) * b = a := by rw [mul_assoc, hbb, mul_one]
  have hab_sq : (a * b) * (a * b) = 1 := by rw [← mul_assoc, hab_a, hbb]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have habi : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab_sq
  let E : Subgroup X :=
    { carrier := {1, a, b, a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with (rfl | rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl | rfl) <;>
          simp [haa, hbb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with (rfl | rfl | rfl | rfl) <;> simp [hai, hbi, habi] }
  have hEmem : ∀ x : X, x ∈ E ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := fun x => Iff.rfl
  have hEH : E ≤ H := by
    intro x hx
    rcases (hEmem x).mp hx with (rfl | rfl | rfl | rfl)
    · exact H.one_mem
    · exact haH
    · exact hbH
    · exact H.mul_mem haH hbH
  have hE : Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      change x * y = y * x
      rcases (hEmem x).mp hx with (rfl | rfl | rfl | rfl) <;>
        rcases (hEmem y).mp hy with (rfl | rfl | rfl | rfl) <;>
        simp [haa, hbb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
    · rcases (hEmem x).mp hx with (rfl | rfl | rfl | rfl) <;>
        simp [pow_two, haa, hbb, hab_sq]
  have hcard : Nat.card E = 2 ^ 2 := by
    have h1a : (1 : X) ≠ a := ha1.symm
    have h1b : (1 : X) ≠ b := hb1.symm
    have h1ab : (1 : X) ≠ a * b := by
      intro h
      apply hne
      have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h.symm
      rw [this, hbi]
    have haab : a ≠ a * b := by
      intro h
      apply hb1
      exact (mul_eq_left.mp h.symm)
    have hbab : b ≠ a * b := by
      intro h
      apply ha1
      exact (mul_eq_right.mp h.symm)
    show Nat.card ({1, a, b, a * b} : Set X) = 2 ^ 2
    rw [Nat.card_coe_set_eq,
      Set.ncard_insert_of_notMem (by simp [h1a, h1b, h1ab]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [hne, haab]) (Set.toFinite _), Set.ncard_pair hbab]
    norm_num
  exact CFSG.SectionRank.le_pRank (by decide : 1 < 2) hEH hE hcard

theorem isConj_of_involutions_of_twoRank_le_one {G : Type*} [Group G] [Finite G]
    (h : Open.twoRank G ≤ 1) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b := by
    intro a b ha hb hab
    by_contra hne
    have h2 := two_le_pRank_of_commute_involutions (H := ⊤) (Subgroup.mem_top a)
      (Subgroup.mem_top b) ha hb hne hab
    unfold Open.twoRank at h
    omega
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have hconj : ∀ w : G, orderOf w = 2 → ∃ g : G, g⁻¹ * w * g ∈ (P : Subgroup G) := by
    intro w hw
    have hwp : IsPGroup 2 (zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
    obtain ⟨T, hT⟩ := hwp.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P T
    refine ⟨g, ?_⟩
    have h1 := hT (Subgroup.mem_zpowers w)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa [MulAut.smul_def, mul_assoc] using h1
  have hordconj : ∀ a w : G, orderOf w = 2 → orderOf (a * w * a⁻¹) = 2 := by
    intro a w hw
    have := orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective w
    simpa [MulAut.conj_apply, hw] using this
  obtain ⟨g₀, hg₀⟩ := hconj x hx
  have hx₀ : orderOf (g₀⁻¹ * x * g₀) = 2 := by
    have := hordconj g₀⁻¹ x hx
    simpa using this
  have hPnt : Nontrivial (P : Subgroup G) :=
    ⟨⟨⟨g₀⁻¹ * x * g₀, hg₀⟩, 1, fun h1 => by
      have h2 : g₀⁻¹ * x * g₀ = 1 := congrArg Subtype.val h1
      rw [h2, orderOf_one] at hx₀
      exact absurd hx₀ (by norm_num)⟩⟩
  have hPp : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  have : Nontrivial (center ↥(P : Subgroup G)) := hPp.center_nontrivial
  have hdiv : 2 ∣ Nat.card (center ↥(P : Subgroup G)) := by
    rcases (hPp.to_subgroup (center ↥(P : Subgroup G))).card_eq_or_dvd with hone | hd
    · exfalso
      have hsub : Subsingleton (center ↥(P : Subgroup G)) :=
        (Nat.card_eq_one_iff_unique.mp hone).1
      exact not_subsingleton _ hsub
    · exact hd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center ↥(P : Subgroup G)) 2 hdiv
  have hc₀ : orderOf (((c : ↥(P : Subgroup G)) : G)) = 2 := by
    rw [Subgroup.orderOf_coe (c : ↥(P : Subgroup G)), Subgroup.orderOf_coe c]
    exact hc
  have key : ∀ w : G, orderOf w = 2 → ∃ g : G, g⁻¹ * w * g = ((c : ↥(P : Subgroup G)) : G) := by
    intro w hw
    obtain ⟨g, hg⟩ := hconj w hw
    refine ⟨g, hcomm _ _ ?_ hc₀ ?_⟩
    · have := hordconj g⁻¹ w hw
      simpa using this
    · have hcen := Subgroup.mem_center_iff.mp c.2 ⟨g⁻¹ * w * g, hg⟩
      exact congrArg Subtype.val hcen
  obtain ⟨gx, hgx⟩ := key x hx
  obtain ⟨gy, hgy⟩ := key y hy
  refine isConj_iff.mpr ⟨gy * gx⁻¹, ?_⟩
  calc gy * gx⁻¹ * x * (gy * gx⁻¹)⁻¹ = gy * (gx⁻¹ * x * gx) * gy⁻¹ := by group
    _ = y := by rw [hgx, ← hgy]; group

omit [Finite X] in
theorem card_eq_card_map_mul_card_ker_of_le {K : Type*} [Group K] {φ : X →* K} {H : Subgroup X}
    (hH : φ.ker ≤ H) : Nat.card H = Nat.card (H.map φ) * Nat.card φ.ker := by
  have h := Subgroup.relIndex_mul_card (H := φ.ker) (K := H)
  rw [Subgroup.relIndex_ker, inf_of_le_left hH] at h
  exact h.symm

theorem isStronglyEmbedded_of_map {G K : Type*} [Group G] [Finite G] [Group K] (φ : G →* K)
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) {M : Subgroup G}
    (hM : φ.ker ≤ M) (h : CFSG.IsStronglyEmbedded (M.map φ)) : CFSG.IsStronglyEmbedded M := by
  obtain ⟨hne, heven, hodd⟩ := h
  have hcardM := card_eq_card_map_mul_card_ker_of_le hM
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply hne
    rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective φ hφ]
  · rw [hcardM]
    exact heven.mul_right _
  · intro g hg
    have hφg : φ g ∉ M.map φ := by
      rintro ⟨m, hm, hmg⟩
      apply hg
      have hker' : m⁻¹ * g ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel]
      simpa using M.mul_mem hm (hM hker')
    have hoddK := hodd (φ g) hφg
    have hkerH : φ.ker ≤ M ⊓ CFSG.conjugate M g := by
      refine le_inf hM fun x hx => ?_
      rw [mem_conjugate_iff]
      exact hM ((φ.normal_ker).conj_mem x hx g)
    have hHcard := card_eq_card_map_mul_card_ker_of_le hkerH
    have hmapH : (M ⊓ CFSG.conjugate M g).map φ ≤
        M.map φ ⊓ CFSG.conjugate (M.map φ) (φ g) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨⟨x, hxM, rfl⟩, ?_⟩
      rw [mem_conjugate_iff]
      refine ⟨g * x * g⁻¹, mem_conjugate_iff.mp hxc, ?_⟩
      simp
    rw [hHcard]
    exact (Odd.of_dvd_nat hoddK (Subgroup.card_dvd_of_le hmapH)).mul hker

end Toolkit

end CFSG.GH74.Uniqueness
