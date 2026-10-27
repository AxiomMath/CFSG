module

public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LieType.ChevTwo.OppCl.SmallU33
public import Certificates.Certificate214002

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
  (outer_card_le_four card_alternating_six inner_conjugation_injective)

section Small

theorem alt6_centralizer_pow_eight :
    ∀ s g : alternatingGroup (Fin 6), s ≠ 1 → s ^ 8 = 1 → g * s = s * g → g ^ 8 = 1 :=
  Certificates.certificate214002

theorem not_three_dvd_card_outer_alt6 : ¬ 3 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have hf1 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (Equiv.swap 0 1)) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← CFSG.Quasithin.SteinbergCB.map_conjPerm_alternatingGroup] at h
    obtain ⟨a, ha, hae⟩ := h
    have := CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num) hae
    rw [this, SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]
      at ha
    exact absurd ha (by decide)
  have hf2 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (Equiv.swap 0 1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, sq, Equiv.swap_mul_self, map_one, map_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord := orderOf_eq_prime hf2 hf1
  have hdvd : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) :=
    hord ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have hle : Nat.card (Outer (alternatingGroup (Fin 6))) ≤ 4 := outer_card_le_four
  intro h3
  omega

theorem mem_inner_of_odd_orderOf {α : MulAut (alternatingGroup (Fin 6))} (hα : Odd (orderOf α)) :
    α ∈ inner (alternatingGroup (Fin 6)) := by
  have hle : Nat.card (Outer (alternatingGroup (Fin 6))) ≤ 4 := outer_card_le_four
  have hndvd := not_three_dvd_card_outer_alt6
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  obtain ⟨c, hc⟩ : ∃ c, Nat.card (Outer (alternatingGroup (Fin 6))) = c := ⟨_, rfl⟩
  rw [hc] at hle hpos hndvd
  have hcases : c = 1 ∨ c = 2 ∨ c = 4 := by omega
  have hdvd4 : c ∣ 4 := by
    rcases hcases with rfl | rfl | rfl <;> norm_num
  set q := QuotientGroup.mk' (inner (alternatingGroup (Fin 6))) α with hq
  have h1 : orderOf q ∣ orderOf α := orderOf_map_dvd _ _
  have h2 : orderOf q ∣ c := hc ▸ orderOf_dvd_natCard q
  have h3 : orderOf q ∣ 2 ^ 2 := h2.trans hdvd4
  have h4 : orderOf q = 1 := by
    obtain ⟨j, hj, hqj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hqj, hj0, pow_zero]
    · exfalso
      have h2q : 2 ∣ orderOf q := by
        rw [hqj]
        exact dvd_pow_self 2 (by omega)
      obtain ⟨m, hm⟩ := hα
      obtain ⟨k, hk⟩ := h2q.trans h1
      omega
  rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact h4

theorem oppositeFixed_alternating_six :
    OppositeFixed (alternatingGroup (Fin 6)) := by
  intro p hp hp2 R hR Q _hQ0 hQ2 _hcore hnorm _hQR hCent
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    apply hnorm
    rw [eq_top_iff]
    intro s _
    apply hCent
    show ∀ α ∈ (⊥ : Subgroup (MulAut (alternatingGroup (Fin 6)))), α s = s
    intro α hα
    rw [Subgroup.mem_bot] at hα
    rw [hα, MulAut.one_apply]
  obtain ⟨β, hβR, hβord⟩ : ∃ β ∈ R, orderOf β = p := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
    have h1 : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).2 hRbot
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [hn, pow_zero] at h1
      exact lt_irrefl 1 h1
    have hdvd : p ∣ Nat.card R := by
      rw [hn]
      exact dvd_pow_self p hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨x.1, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1
    (mem_inner_of_odd_orderOf (odd_orderOf_of_mem_isPGroup hp hp2 hR hβR))
  have hgord : orderOf g = p := by
    rw [← orderOf_injective _ inner_conjugation_injective g, hg, hβord]
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hgord
    exact hp.one_lt.ne hgord
  have hgp : g ^ p = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one g
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨hsC, hsQ⟩ := Subgroup.mem_inf.1 hs
  have hsC' : ∀ α ∈ R, α s = s := hsC
  rw [Subgroup.mem_bot]
  by_contra hs1
  have hs8 : s ^ 8 = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
    have hdvd : Nat.card Q ∣ Nat.card (alternatingGroup (Fin 6)) :=
      Subgroup.card_subgroup_dvd_card Q
    rw [hn, card_alternating_six] at hdvd
    have hn3 : n ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have := dvd_trans h16 hdvd
      norm_num at this
    have hsp : s ^ Nat.card Q = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨s, hsQ⟩ : Q)))
    rw [hn] at hsp
    obtain ⟨c, hc⟩ : 2 ^ n ∣ 8 := by
      interval_cases n <;> norm_num
    rw [hc, pow_mul, hsp, one_pow]
  have hcomm : g * s = s * g := by
    have h := hsC' β hβR
    rw [← hg, MulAut.conj_apply] at h
    calc g * s = g * s * g⁻¹ * g := by group
      _ = s * g := by rw [h]
  have hg8 : g ^ 8 = 1 := alt6_centralizer_pow_eight s g hs1 hs8 hcomm
  have hcop : Nat.Coprime 8 p := by
    have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    simpa using Nat.Coprime.pow_left 3 h2p
  have hgone : g = 1 := by
    have h := (pow_gcd_eq_one (a := g)).2 ⟨hg8, hgp⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
    exact h
  exact hg1 hgone

theorem oppositeFixed_PSU_three_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (3 ^ 1) ^ 2) :
    OppositeFixed (StatedProj (StatedSU 3 (3 ^ 1) K)) := by
  have hL : CFSG.Blueprint.LieModel (StatedProj (StatedSU 3 (3 ^ 1) K)) .PSU 3 3 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩, K,
      inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  exact U33Fin.oppositeFixed_of_iso e

end Small

end CFSG.LieType.ChevTwo.OppCl
