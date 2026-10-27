module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.CGT.T75I.AltRank
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Perm

open Equiv Equiv.Perm

theorem not_commute_even_involution {k : ℕ} (hk : k ≤ 7) {g σ : Perm (Fin k)} {q : ℕ}
    (hq : q.Prime) (hq5 : 5 ≤ q) (hg : orderOf g = q) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσs : sign σ = 1) (hc : Commute g σ) : False := by
  classical
  have hsupp := CFSG.CGT.T75I.card_support_of_even_involution hk hσ2 hσ1 hσs
  have hcomm : ∀ x, g (σ x) = σ (g x) := fun x => by
    have := congrArg (fun f : Perm (Fin k) => f x) hc.eq
    simpa using this
  have hinv : ∀ x, g x ∈ σ.support ↔ x ∈ σ.support := by
    intro x
    simp only [Equiv.Perm.mem_support]
    constructor
    · intro hgx hx
      apply hgx
      rw [← hcomm, hx]
    · intro hx hgx
      apply hx
      apply g.injective
      rw [hcomm, hgx]
  set g' : Perm σ.support := g.subtypePerm hinv with hg'
  have hgq : g ^ q = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg'q : g' ^ q = 1 := by
    rw [hg', Equiv.Perm.subtypePerm_pow]
    ext x
    simp only [Equiv.Perm.subtypePerm_apply, hgq, Equiv.Perm.coe_one, id_eq]
  have hdvd1 : orderOf g' ∣ q := orderOf_dvd_of_pow_eq_one hg'q
  have hdvd2 : orderOf g' ∣ 24 := by
    have h := orderOf_dvd_natCard g'
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hsupp] at h
    simpa [Nat.factorial] using h
  have hq24 : ¬ q ∣ 24 := by
    intro h
    have h' : q ∣ 2 ^ 3 * 3 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hq).1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  have hord1 : orderOf g' = 1 := by
    rcases (Nat.dvd_prime hq).1 hdvd1 with h | h
    · exact h
    · exact absurd (h ▸ hdvd2) hq24
  have hfix : ∀ x ∈ σ.support, g x = x := by
    intro x hx
    have h1 : g' = 1 := orderOf_eq_one_iff.1 hord1
    have := congrArg (fun f : Perm σ.support => (f ⟨x, hx⟩ : Fin k)) h1
    simpa [hg'] using this
  have hdisj : Disjoint g.support σ.support := by
    rw [Finset.disjoint_left]
    intro x hxg hxσ
    exact (Equiv.Perm.mem_support.1 hxg) (hfix x hxσ)
  have hcard : g.support.card + σ.support.card ≤ k := by
    rw [← Finset.card_union_of_disjoint hdisj]
    simpa using Finset.card_le_univ (g.support ∪ σ.support)
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    omega
  obtain ⟨n, hn⟩ : ∃ n, n ∈ g.cycleType := by
    by_contra hno
    push Not at hno
    apply hg1
    apply Equiv.Perm.cycleType_eq_zero.1
    exact Multiset.eq_zero_iff_forall_notMem.2 hno
  have hndvd : n ∣ q := hg ▸ Equiv.Perm.dvd_of_mem_cycleType hn
  have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hnq : n = q := by
    rcases (Nat.dvd_prime hq).1 hndvd with h | h
    · omega
    · exact h
  have hnle : n ≤ g.support.card := by
    rw [← Equiv.Perm.sum_cycleType]
    exact Multiset.le_sum_of_mem hn
  omega

end Perm

theorem not_commute_involution_alt {Y : Type} [Group Y] {k : ℕ} (hk : k ≤ 7)
    (e : Y ≃* alternatingGroup (Fin k)) {g σ : Y} {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hg : orderOf g = q) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (hc : g * σ = σ * g) : False := by
  have h1 : orderOf ((e g : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) = q := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg]
  have h2 : ((e σ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) ^ 2 = 1 := by
    have : (e σ) * (e σ) = 1 := by rw [← map_mul, hσ, map_one]
    rw [sq]
    exact congrArg Subtype.val this
  have h3 : ((e σ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) ≠ 1 := by
    intro h
    apply hσ1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h
  have h4 : Equiv.Perm.sign ((e σ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.1 (e σ).2
  have h5 : Commute ((e g : alternatingGroup (Fin k)) : Equiv.Perm (Fin k))
      ((e σ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) := by
    have := congrArg e hc
    rw [map_mul, map_mul] at this
    exact congrArg Subtype.val this
  exact not_commute_even_involution hk hq hq5 h1 h2 h3 h4 h5

theorem card_eq_168 {Y : Type} [Group Y] (h : StatedClassicalModel Y .PSL 3 2 1) :
    Nat.card Y = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem not_commute_involution_L3two {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 168) {g σ : Y} (hg : orderOf g = 7) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hc : g * σ = σ * g) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set P : Subgroup Y := Subgroup.zpowers g with hP
  have hPcard : Nat.card P = 7 := by rw [hP, Nat.card_zpowers, hg]
  have hP7 : IsPGroup 7 P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hidx : P.index = 24 := by
    have := P.card_mul_index
    rw [hPcard, hcard] at this
    omega
  have hnd : ¬ 7 ∣ P.index := by rw [hidx]; norm_num
  let S : Sylow 7 Y := hP7.toSylow hnd
  have hSP : (S : Subgroup Y) = P := IsPGroup.toSylow_coe hP7 hnd
  have hmod := card_sylow_modEq_one 7 Y
  have hdvd : Nat.card (Sylow 7 Y) ∣ 24 := by
    have := S.card_dvd_index
    rwa [hSP, hidx] at this
  have hN : Nat.card (Sylow 7 Y) = (Subgroup.normalizer (P : Set Y)).index := by
    have := S.card_eq_index_normalizer
    have hset : (S : Set Y) = (P : Set Y) := congrArg (fun H : Subgroup Y => (H : Set Y)) hSP
    rwa [hset] at this
  have hcases : Nat.card (Sylow 7 Y) = 1 ∨ Nat.card (Sylow 7 Y) = 8 := by
    have hle : Nat.card (Sylow 7 Y) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have hmod' : Nat.card (Sylow 7 Y) % 7 = 1 := hmod
    interval_cases h : Nat.card (Sylow 7 Y) <;> omega
  rcases hcases with h1 | h8
  ·
    have hnorm : Subgroup.normalizer (P : Set Y) = ⊤ := by
      rw [← Subgroup.index_eq_one, ← hN, h1]
    have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.1 hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
    · rw [h, Subgroup.card_bot] at hPcard
      omega
    · rw [h, Subgroup.card_top, hcard] at hPcard
      omega
  · have hNidx : (Subgroup.normalizer (P : Set Y)).index = 8 := by rw [← hN, h8]
    have hNcard : Nat.card (Subgroup.normalizer (P : Set Y)) = 21 := by
      have := (Subgroup.normalizer (P : Set Y)).card_mul_index
      rw [hNidx, hcard] at this
      omega
    have hσC : σ ∈ Subgroup.centralizer (P : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact ((Commute.zpow_left (show Commute g σ from hc) j)).eq
    have hσN : σ ∈ Subgroup.normalizer (P : Set Y) :=
      (Subgroup.centralizer_le_normalizer (P : Set Y)) hσC
    have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hσ1
    have hdv : orderOf σ ∣ Nat.card (Subgroup.normalizer (P : Set Y)) := by
      have := orderOf_dvd_natCard (⟨σ, hσN⟩ : Subgroup.normalizer (P : Set Y))
      rwa [Subgroup.orderOf_mk] at this
    rw [hσ2, hNcard] at hdv
    omega

theorem false_of_borel_pair {Y : Type} [Group Y] [Finite Y] {T T₁ : Subgroup Y} (hT : IsWC T)
    (S : Sylow 2 Y)
    (hN : Subgroup.normalizer (T : Set Y) = Subgroup.normalizer ((S : Subgroup Y) : Set Y))
    (hS : (S : Subgroup Y) = T ∨
      T = (Subgroup.center (S : Subgroup Y)).map (S : Subgroup Y).subtype)
    (g : Y) (hg : T₁ = conjSubgroup g T) (hne : T₁ ≠ T) {t : Y} (htT : t ∈ T) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (T₁ : Set Y)) : False := by
  classical
  have htt : t * t = 1 := elemAbelian_mul_self hT.1 htT
  have hu : g⁻¹ * t * g ∈ Subgroup.normalizer (T : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.1 htN) (g * x * g⁻¹)
    rw [hg, mem_conjSubgroup, mem_conjSubgroup] at h1
    have e1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have e2 : g⁻¹ * (t * (g * x * g⁻¹) * t⁻¹) * g = (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  have huS : g⁻¹ * t * g ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := hN ▸ hu
  have hu2 : orderOf (g⁻¹ * t * g) = 2 := by
    have : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt]; group
    refine orderOf_eq_prime (by rw [sq]; exact this) ?_
    intro h
    apply ht1
    have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hz : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * t * g)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu2, pow_one]
  have hmemS : g⁻¹ * t * g ∈ (S : Subgroup Y) := by
    have h := hz.inf_normalizer_sylow S
    exact (h.le ⟨Subgroup.mem_zpowers _, huS⟩).2
  have htS₁ : t ∈ conjSubgroup g (S : Subgroup Y) := by
    rw [mem_conjSubgroup]
    exact hmemS
  have hcomm : ∀ x ∈ T₁, x * t = t * x := by
    intro x hx
    rw [hg] at hx
    have hx' : g⁻¹ * x * g ∈ T := mem_conjSubgroup.1 hx
    rcases hS with hS | hS
    ·
      have hu' : g⁻¹ * t * g ∈ T := hS ▸ hmemS
      have hc := elemAbelian_mul_comm hT.1 hx' hu'
      calc x * t = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
        _ = t * x := by group
    ·
      have hxz : g⁻¹ * x * g ∈ (Subgroup.center (S : Subgroup Y)).map (S : Subgroup Y).subtype := by
        rw [← hS]
        exact hx'
      obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hxz
      have hcc := Subgroup.mem_center_iff.1 hc ⟨g⁻¹ * t * g, hmemS⟩
      have hcc' : (g⁻¹ * t * g) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (g⁻¹ * t * g) := by
        have := congrArg Subtype.val hcc
        simp only [Subgroup.coe_mul] at this
        rw [← hce]
        exact this
      calc x * t = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcc']
        _ = t * x := by group
  have hT₁le : T₁ ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm x hx
  have := (hT.2 t htT ht1).2 g (by rw [← hg]; exact hT₁le)
  exact hne (hg.trans this)

theorem sylow_eq_of_le_normalizer {Y : Type} [Group Y] [Finite Y] (S₀ S₁ : Sylow 2 Y)
    (h : (S₀ : Subgroup Y) ≤ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y)) : S₀ = S₁ := by
  have h1 := S₀.isPGroup'.inf_normalizer_sylow S₁
  have h2 : (S₀ : Subgroup Y) ≤ S₁ := by
    intro x hx
    exact (h1.le ⟨hx, h hx⟩).2
  have h3 : (S₁ : Subgroup Y) = S₀ := S₀.is_maximal' S₁.isPGroup' h2
  exact Sylow.ext h3.symm

theorem false_of_borel_pair' {Y : Type} [Group Y] [Finite Y] {T T₁ : Subgroup Y} (hT : IsWC T)
    (S₀ S₁ : Sylow 2 Y)
    (hN : Subgroup.normalizer (T : Set Y) = Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y))
    (hS : (S₀ : Subgroup Y) = T ∨
      T = (Subgroup.center (S₀ : Subgroup Y)).map (S₀ : Subgroup Y).subtype)
    (g : Y) (hg : T₁ = conjSubgroup g T) (hne : T₁ ≠ T) {t : Y} (htT : t ∈ T) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (T₁ : Set Y)) : False := by
  have hle : (S₀ : Subgroup Y) ≤ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y) := by
    rw [← hN]
    rcases hS with hS | hS
    · rw [hS]
      exact Subgroup.le_normalizer
    · intro x hx
      have hxc : x ∈ Subgroup.centralizer (T : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hw' : w ∈ (Subgroup.center (S₀ : Subgroup Y)).map (S₀ : Subgroup Y).subtype := by
          rw [← hS]; exact hw
        obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hw'
        have hv := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨x, hx⟩)
        simp only [Subgroup.coe_mul] at hv
        rw [← hce]
        exact hv.symm
      exact (Subgroup.centralizer_le_normalizer (T : Set Y)) hxc
  have hS01 : S₀ = S₁ := sylow_eq_of_le_normalizer S₀ S₁ hle
  subst hS01
  exact false_of_borel_pair hT S₀ hN hS g hg hne htT ht1 htN

theorem classify_of_pair {Y : Type} [Group Y] [Finite Y] {T T₁ : Subgroup Y}
    (hT : IsWC T) (hstd : StdPair Y T) (hc4 : Nat.card T = 4) (g : Y)
    (hg : T₁ = conjSubgroup g T) (hne : T₁ ≠ T) {t : Y} (htT : t ∈ T) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (T₁ : Set Y)) :
    StatedClassicalModel Y .PSL 3 2 1 ∨ Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Y ≃* alternatingGroup (Fin 7)) := by
  rcases hstd.listGroup with ⟨m, s, hm2, hs1, hmodel⟩ | ⟨s, hs2, hmodel⟩ |
    ⟨s, hso, hs3, hmodel⟩ | ⟨k, hk6, hk9, ⟨e⟩⟩ | hM | hM | hM
  · rcases Nat.lt_or_ge m 3 with hm | hm
    · have hm2' : m = 2 := by omega
      subst hm2'
      obtain ⟨-, ⟨S₀, hS₀⟩, -, S₁, hS₁⟩ := hstd.of_psl2 hmodel
      exact (false_of_borel_pair' hT S₀ S₁ hS₁ (Or.inl hS₀) g hg hne htT ht1 htN).elim
    · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmodel
      obtain ⟨hcardT, -⟩ := hstd.of_psl hm K hK e
      rw [hc4] at hcardT
      have h2 : s * (m - 1) = 2 := by
        have : (2 : ℕ) ^ 2 = 2 ^ (s * (m - 1)) := by rw [← hcardT]; norm_num
        exact (Nat.pow_right_injective (le_refl 2) this).symm
      have hs : s = 1 := by
        rcases Nat.lt_or_ge s 2 with h | h
        · omega
        · have : s * (m - 1) ≥ 2 * 2 := Nat.mul_le_mul h (by omega)
          omega
      have hm3 : m = 3 := by subst hs; omega
      subst hs
      subst hm3
      exact Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  · obtain ⟨-, ⟨S₀, hS₀⟩, -, S₁, hS₁⟩ := hstd.of_psu3 hs2 hmodel
    exact (false_of_borel_pair' hT S₀ S₁ hS₁ (Or.inr hS₀) g hg hne htT ht1 htN).elim
  · obtain ⟨-, ⟨S₀, hS₀⟩, -, S₁, hS₁⟩ := hstd.of_sz hso hs3 hmodel
    exact (false_of_borel_pair' hT S₀ S₁ hS₁ (Or.inr hS₀) g hg hne htT ht1 htN).elim
  · have hcardT := hstd.card_alternating hk6 hk9 ⟨e⟩
    rw [hc4] at hcardT
    have hk : k ≤ 7 := by
      by_contra hk
      simp only [hk, ite_false] at hcardT
      omega
    have hk' : k = 6 ∨ k = 7 := by omega
    rcases hk' with rfl | rfl
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr ⟨e⟩)
  · have := hstd.card_sporadic (Or.inl hM)
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inl hM))
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inr hM))
    omega

theorem eq_one_of_centralizes {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {T T₁ : Subgroup Y} (hT : IsWC T) (hstd : StdPair Y T) (hc4 : Nat.card T = 4) (g : Y)
    (hg : T₁ = conjSubgroup g T) (hne : T₁ ≠ T) {t : Y} (htT : t ∈ T) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (T₁ : Set Y)) {z : Y} {q k : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hz : orderOf z = q ^ k) (hzc : ∀ s ∈ T, z * s = s * z) : z = 1 := by
  by_contra hz1
  have hk : k ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.1 (by simpa using hz))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set z' : Y := z ^ (q ^ j) with hz'
  have hz'q : orderOf z' = q := by
    have hdvd : q ^ j ∣ orderOf z := by rw [hz]; exact pow_dvd_pow q (Nat.le_succ j)
    rw [hz', orderOf_pow_of_dvd (pow_ne_zero j hq.ne_zero) hdvd, hz, pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hq.pos j)]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ', hσ'⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [hc4]; norm_num)
  set σ : Y := (σ' : Y) with hσ
  have hσT : σ ∈ T := σ'.2
  have hσo : orderOf σ = 2 := by rw [hσ, Subgroup.orderOf_coe, hσ']
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσo, sq] at this
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσo
    omega
  have hcomm : z' * σ = σ * z' := by
    have := (Commute.pow_left (show Commute z σ from hzc σ hσT) (q ^ j)).eq
    exact this
  rcases classify_of_pair hT hstd hc4 g hg hne htT ht1 htN with hL | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have h168 := card_eq_168 hL
    have hq7 : q = 7 := by
      have hdvd : q ∣ 168 := by
        rw [← h168, ← hz'q]
        exact orderOf_dvd_natCard z'
      have h' : q ∣ 2 ^ 3 * 3 * 7 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hq).1 h' with h1 | h7
      · rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h3
        · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
          omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h7
    exact not_commute_involution_L3two h168 (hq7 ▸ hz'q) hσσ hσ1 hcomm
  · exact not_commute_involution_alt (k := 6) (by norm_num) e hq hq5 hz'q hσσ hσ1 hcomm
  · exact not_commute_involution_alt (k := 7) (by norm_num) e hq hq5 hz'q hσσ hσ1 hcomm

end CFSG.CGT.T75H
