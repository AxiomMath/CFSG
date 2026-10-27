module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification CFSG.GH74.GLS
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12

section Count

theorem false_of_normalizes_three {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 60)
    (hs : IsSimpleGroup Y) {U S0 : Subgroup Y} (hU : U ≠ ⊥) (hUp : IsPGroup 3 ↥U)
    (hS0 : Odd S0.index) (hN : S0 ≤ normalizer (U : Set Y)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle3 : ∀ H : Subgroup Y, IsPGroup 3 ↥H → Nat.card H ≤ 3 := by
    intro H hH
    obtain ⟨n, hn⟩ := hH.exists_card_eq
    have hd : 3 ^ n ∣ 60 := hn ▸ hY ▸ Subgroup.card_subgroup_dvd_card H
    have hn1 : n ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ∣ 60 := (pow_dvd_pow 3 (by omega)).trans hd
      omega
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 3 := pow_one 3
  have hU3 : Nat.card U = 3 := by
    obtain ⟨n, hn⟩ := hUp.exists_card_eq
    have h1 := hle3 U hUp
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      apply hU
      rw [h0, pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq U hn
    · have : 3 ≤ 3 ^ n := by
        calc 3 = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h0
      omega
  have hUindex : ¬ 3 ∣ U.index := by
    have h := Subgroup.card_mul_index U
    rw [hY, hU3] at h
    have : U.index = 20 := by omega
    rw [this]
    norm_num
  let P : Sylow 3 Y := hUp.toSylow hUindex
  have hPU : (P : Subgroup Y) = U := rfl
  set N := normalizer (U : Set Y) with hNdef
  have hUN : U ≤ N := Subgroup.le_normalizer
  have h4 : 4 ∣ Nat.card S0 := by
    have h := Subgroup.card_mul_index S0
    rw [hY] at h
    have hcop : Nat.Coprime 4 S0.index := by
      have : Nat.Coprime 2 S0.index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by rcases hS0 with ⟨j, hj⟩; omega)
      simpa using this.pow_left 2
    exact hcop.dvd_of_dvd_mul_right ⟨15, by omega⟩
  have h12 : 12 ∣ Nat.card N := by
    have h3 : 3 ∣ Nat.card N := hU3 ▸ Subgroup.card_dvd_of_le hUN
    have h4' : 4 ∣ Nat.card N := h4.trans (Subgroup.card_dvd_of_le hN)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4' h3
  have hidx : N.index ∣ 5 := by
    have h := Subgroup.index_mul_card N
    rw [hY] at h
    obtain ⟨m, hm⟩ := h12
    rw [hm] at h
    have h' : N.index * m * 12 = 5 * 12 :=
      calc N.index * m * 12 = N.index * (12 * m) := by ring
        _ = 60 := h
        _ = 5 * 12 := by norm_num
    exact ⟨m, (Nat.eq_of_mul_eq_mul_right (by norm_num) h').symm⟩
  have hmod : N.index ≡ 1 [MOD 3] := by
    have h1 := card_sylow_modEq_one 3 Y
    rwa [P.card_eq_index_normalizer] at h1
  have hN1 : N.index = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hidx with h | h
    · exact h
    · rw [h] at hmod
      exact absurd hmod (by decide)
  have hNtop : N = ⊤ := Subgroup.index_eq_one.mp hN1
  have hnormal : U.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have := hnormal
  rcases hs.eq_bot_or_eq_top_of_normal U with h | h
  · exact hU h
  · rw [h, Subgroup.card_top, hY] at hU3
    omega

end Count

section Outer

variable {Y : Type} [Group Y]

theorem inner_of_pow_three_eq_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    (e : Y ≃* PSL2 F) {α : MulAut Y} (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  classical
  by_contra hαinn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα1 : α ≠ 1 := fun h1 => hαinn (h1 ▸ (MonoidHom.range _).one_mem)
  have hαord : orderOf α = 3 := orderOf_eq_prime hα hα1
  have hgord : orderOf (AutL2Facts.autEquiv e α) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hαord
  have hF' : Nat.card F = 5 ^ 1 := by rw [hF, pow_one]
  obtain ⟨h3, -⟩ := outer_conj_fieldAut (by norm_num : Nat.Prime 5) (by norm_num)
    Nat.prime_three (by norm_num) le_rfl hF' hgord (autEquiv_not_psl e hαinn)
  omega

theorem quotient_center_equiv_psl2 {K : Type} [Group K] (hK : HasSL2Model K (fun q => q = 5)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 5 ∧
      Nonempty ((K ⧸ center K) ≃* PSL2 F) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  let e' : K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨QuotientGroup.congr (center K) (center (Matrix.SpecialLinearGroup (Fin 2) F)) e'
      (Subgroup.map_center_eq e')⟩⟩

end Outer

section Frame

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} [K.Normal] {a : Γ}
  {P R : Subgroup Γ}

theorem Frame55.exists_odd_index_le_normalizer (hf : Frame55 k p ρ K a P R) :
    ∃ S0 : Subgroup (K ⧸ center ↥K), Odd S0.index ∧
      S0 ≤ normalizer ((innerPart (K := K) P : Subgroup (K ⧸ center ↥K)) :
        Set (K ⧸ center ↥K)) := by
  obtain ⟨Q, hQ⟩ := hf.sylow
  let π : ↥K →* K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  refine ⟨(Q : Subgroup ↥K).map π, ?_, ?_⟩
  · have h1 : ((Q : Subgroup ↥K).map π).index ∣ (Q : Subgroup ↥K).index :=
      Subgroup.index_map_dvd (Q : Subgroup ↥K) hπ
    have h2 : ¬ 2 ∣ (Q : Subgroup ↥K).index := Sylow.not_dvd_index Q
    by_contra hodd
    exact h2 ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)).trans h1)
  · rintro _ ⟨q, hq, rfl⟩
    have hqRK : (q : Γ) ∈ R ⊓ K := by
      rw [← hQ]
      exact ⟨q, hq, rfl⟩
    exact mk_mem_normalizer_innerPart hf.norm hqRK.1 hqRK.2

theorem Frame55.false_of_sl2_five [Module.Finite (ZMod p) V] (hf : Frame55 k p ρ K a P R)
    (hp3 : p = 3)
    (hK : HasSL2Model ↥K (fun q => q = 5)) : False := by
  classical
  subst hp3
  obtain ⟨F, _, _, hF, ⟨eY⟩⟩ := quotient_center_equiv_psl2 hK
  have hs : IsSimpleGroup (K ⧸ center ↥K) := hf.quasi.2.1
  by_cases hU : innerPart (K := K) P = ⊥
  ·
    obtain ⟨y, hy⟩ := inner_of_pow_three_eq_one hF eY hf.actYHom_pow
    have hyU : y ∈ innerPart (K := K) P := mem_innerPart.mpr ⟨a, hf.a_mem, hy.symm⟩
    rw [hU, Subgroup.mem_bot] at hyU
    apply hf.actYHom_ne_one
    rw [← hy, hyU, map_one]
  · have hodd : IsOddPrimePower (Nat.card F) :=
      ⟨5, 1, by norm_num, by decide, le_rfl, by simpa using hF⟩
    have hY : Nat.card (K ⧸ center ↥K) = 60 := by
      rw [Nat.card_congr eY.toEquiv, psl2_card_formula F hodd, hF]
      norm_num
    obtain ⟨S0, hS0, hS0N⟩ := hf.exists_odd_index_le_normalizer
    exact false_of_normalizes_three hY hs hU
      (isPGroup_innerPart (center_quot_eq_bot hf.quasi) hf.pgrp) hS0 hS0N

end Frame

theorem sl2Five55 : Sl2Five55 := by
  intro k p Γ _ _ V _ _ _ ρ K a P R hf hp3 hK
  have := hf.normal
  exact hf.false_of_sl2_five hp3 hK

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
