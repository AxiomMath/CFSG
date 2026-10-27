module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOmega
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type} [Group X]

theorem cube_mul_eq_of_commutator {g f u : X} (hu : g * f * g⁻¹ * f⁻¹ = u) (hug : Commute u g)
    (huf : Commute u f) (hu3 : u ^ 3 = 1) (hf3 : f ^ 3 = 1) : (g * f) ^ 3 = g ^ 3 := by
  have hc1 : g * f * g⁻¹ = u * f := by rw [← hu]; group
  have hgu : ∀ x : X, g * (u * x) * g⁻¹ = u * (g * x * g⁻¹) := fun x => by
    rw [show g * (u * x) * g⁻¹ = (g * u) * x * g⁻¹ by group, ← hug.eq]
    group
  have hc2 : (g * g) * f * (g * g)⁻¹ = u * (u * f) := by
    rw [show (g * g) * f * (g * g)⁻¹ = g * (g * f * g⁻¹) * g⁻¹ by group, hc1, hgu, hc1]
  have hc3 : (g * g * g) * f * (g * g * g)⁻¹ = u * (u * (u * f)) := by
    rw [show (g * g * g) * f * (g * g * g)⁻¹ = g * ((g * g) * f * (g * g)⁻¹) * g⁻¹ by group, hc2,
      hgu, hgu, hc1]
  have e1 : (g * f) ^ 3 = (g * f * g⁻¹) * ((g * g) * f * (g * g)⁻¹) *
      ((g * g * g) * f * (g * g * g)⁻¹) * (g * g * g) := by
    rw [pow_three]
    group
  rw [e1, hc1, hc2, hc3]
  have hfu : ∀ x : X, f * (u * x) = u * (f * x) := fun x => by
    rw [← mul_assoc, ← huf.eq, mul_assoc]
  have hf3' : ∀ x : X, f * (f * (f * x)) = x := fun x => by
    rw [← mul_assoc, ← mul_assoc, show f * f * f = f ^ 3 by simp only [pow_succ, pow_zero,
      one_mul], hf3, one_mul]
  have hu3x : ∀ x : X, u * (u * (u * x)) = x := fun x => by
    rw [← mul_assoc, ← mul_assoc, show u * u * u = u ^ 3 by simp only [pow_succ, pow_zero,
      one_mul], hu3, one_mul]
  simp only [mul_assoc, hfu, hu3x, hf3']
  rw [pow_three]

theorem card_le_of_transvection [Finite X] {D : Subgroup X} (hD : IsPGroup 3 D) {c w d : X}
    (hcD : c ∈ D) (hwD : w ∈ D) (hdD : d ∈ D) (hwc : ∀ g ∈ D, Commute w g)
    (hc3 : c ^ 3 = 1) (hwo : orderOf w = 3) (hcw : c ∉ Subgroup.zpowers w)
    (hCD : ∀ y ∈ D, y * c = c * y → y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers w)
    (hd3 : d ^ 3 ∈ Subgroup.zpowers w) (hd31 : d ^ 3 ≠ 1)
    (he : d * c * d⁻¹ * c⁻¹ ∈ Subgroup.zpowers w) (he1 : d * c * d⁻¹ * c⁻¹ ≠ 1) :
    Nat.card D ≤ 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw3 : w ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  set W := Subgroup.zpowers w with hW
  set F₀ := Subgroup.zpowers c ⊔ W with hF₀
  set e := d * c * d⁻¹ * c⁻¹ with he_def
  have hWc : ∀ x ∈ W, ∀ g ∈ D, Commute x g := by
    intro x hx g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hwc g hg).zpow_left n
  have hcwc : Commute c w := (hwc c hcD).symm
  have hWD : W ≤ D := Subgroup.zpowers_le.mpr hwD
  have hF₀D : F₀ ≤ D := sup_le (Subgroup.zpowers_le.mpr hcD) hWD
  have hF₀mem : ∀ f ∈ F₀, ∃ i j : ℤ, f = c ^ i * w ^ j := by
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_zpowers_sup_zpowers_iff hcwc).mp hf
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨i, j, rfl⟩
  have hpow3 : ∀ {x : X} (i : ℤ), x ^ 3 = 1 → (x ^ i) ^ 3 = 1 := fun {x} i hx => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hF3 : ∀ f ∈ F₀, f ^ 3 = 1 := by
    intro f hf
    obtain ⟨i, j, rfl⟩ := hF₀mem f hf
    rw [((hcwc.zpow_left i).zpow_right j).mul_pow, hpow3 i hc3, hpow3 j hw3, mul_one]
  have hFc : ∀ f ∈ F₀, Commute f c := by
    intro f hf
    obtain ⟨i, j, rfl⟩ := hF₀mem f hf
    exact ((Commute.refl c).zpow_left i).mul_left (hcwc.symm.zpow_left j)
  have hdc : d * c * d⁻¹ = e * c := by rw [he_def]; group
  have hed : Commute e d := hWc e he d hdD
  have hec : Commute e c := hWc e he c hcD
  have hdn : ∀ n : ℕ, d ^ n * c * (d ^ n)⁻¹ = e ^ n * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc d ^ (n + 1) * c * (d ^ (n + 1))⁻¹ = d * (d ^ n * c * (d ^ n)⁻¹) * d⁻¹ := by
            rw [pow_succ']; group
        _ = d * (e ^ n * c) * d⁻¹ := by rw [ih]
        _ = (d * e ^ n) * c * d⁻¹ := by group
        _ = e ^ n * (d * c * d⁻¹) := by rw [← (hed.pow_left n).eq]; group
        _ = e ^ (n + 1) * c := by rw [hdc, pow_succ]; group
  have hdpow : ∀ g ∈ Subgroup.zpowers d, ∃ n : ℕ, g = d ^ n := by
    intro g hg
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
    exact ⟨n, hn.symm⟩
  have hgf : ∀ g ∈ Subgroup.zpowers d, ∀ f ∈ F₀, g * f * g⁻¹ * f⁻¹ ∈ W := by
    intro g hg f hf
    obtain ⟨n, rfl⟩ := hdpow g hg
    obtain ⟨i, j, rfl⟩ := hF₀mem f hf
    have hwd : Commute (w ^ j) (d ^ n) := ((hwc d hdD).zpow_left j).pow_right n
    have h1 : d ^ n * (c ^ i * w ^ j) * (d ^ n)⁻¹ * (c ^ i * w ^ j)⁻¹ = (e ^ n) ^ i := by
      calc d ^ n * (c ^ i * w ^ j) * (d ^ n)⁻¹ * (c ^ i * w ^ j)⁻¹
          = (d ^ n * c * (d ^ n)⁻¹) ^ i * (d ^ n * w ^ j * (d ^ n)⁻¹) *
              (c ^ i * w ^ j)⁻¹ := by rw [conj_zpow]; group
        _ = (e ^ n * c) ^ i * w ^ j * (c ^ i * w ^ j)⁻¹ := by
            rw [hdn n, ← hwd.eq, mul_inv_cancel_right]
        _ = (e ^ n) ^ i * c ^ i * w ^ j * (c ^ i * w ^ j)⁻¹ := by
            rw [(hec.pow_left n).mul_zpow]
        _ = (e ^ n) ^ i := by group
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ he n) i
  have hgfC : ∀ g ∈ Subgroup.zpowers d, ∀ f ∈ F₀, g * f * g⁻¹ ∈ F₀ := by
    intro g hg f hf
    rw [show g * f * g⁻¹ = (g * f * g⁻¹ * f⁻¹) * f by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hgf g hg f hf)) hf
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (F₀ : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · exact fun hf => hgfC g hg f hf
    · intro hf
      have h1 := hgfC g⁻¹ (Subgroup.inv_mem _ hg) _ hf
      rwa [show g⁻¹ * (g * f * g⁻¹) * g⁻¹⁻¹ = f by group] at h1
  set B := Subgroup.zpowers d ⊔ F₀ with hB
  have hdDle : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
  have hBD : B ≤ D := sup_le hdDle hF₀D
  have hd3o : orderOf (d ^ 3) = 3 := by
    refine orderOf_eq_prime ?_ hd31
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd3
    rw [← hk]
    exact hpow3 k hw3
  have hWd : W ≤ Subgroup.zpowers d := by
    have heq : Subgroup.zpowers (d ^ 3) = W := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hd3) (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hd3o])
    rw [← heq, Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) 3
  have hΩB : ∀ b ∈ B, b ^ 3 = 1 → b ∈ F₀ := by
    intro b hb hb3
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdN] at hb
    obtain ⟨g, hg, f, hf, rfl⟩ := hb
    have hu := hgf g hg f hf
    have hg3 : g ^ 3 = 1 := by
      rw [← cube_mul_eq_of_commutator rfl (hWc _ hu g (hdDle hg)) (hWc _ hu f (hF₀D hf))
        (hF3 _ (Subgroup.mem_sup_right hu)) (hF3 f hf)]
      exact hb3
    have hgw : g ∈ W :=
      mem_zpowers_of_pow_eq_one Nat.prime_three (hWd (Subgroup.mem_zpowers w)) hwo hg hg3
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgw) hf
  have hc1 : c ≠ 1 := fun h => hcw (h ▸ Subgroup.one_mem _)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcB : c ∈ B := Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hNB : ∀ y ∈ D, (∀ b ∈ B, y * b * y⁻¹ ∈ B) → y ∈ B := by
    intro y hyD hyB
    have hyc : y * c * y⁻¹ ∈ F₀ := hΩB _ (hyB c hcB) (by rw [conj_pow, hc3]; group)
    obtain ⟨j, k, hjk⟩ := hF₀mem _ hyc
    have hwky : Commute (w ^ k) y := hWc _ (Subgroup.zpow_mem_zpowers w k) y hyD
    have hcj : c ^ j = c ^ (j % 3) := by
      rw [show (3 : ℤ) = (orderOf c : ℤ) by rw [hco]; rfl, zpow_mod_orderOf]
    have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj3 with h0 | h1 | h2
    ·
      exfalso
      rw [hcj, h0, zpow_zero, one_mul] at hjk
      apply hcw
      have : c = y⁻¹ * (y * c * y⁻¹) * y := by group
      rw [this, hjk, mul_assoc, hwky.eq, ← mul_assoc, inv_mul_cancel, one_mul]
      exact Subgroup.zpow_mem_zpowers w k
    ·
      rw [hcj, h1, zpow_one] at hjk
      have he1' : orderOf e = 3 := orderOf_eq_prime (by
        obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp he
        rw [← hk']
        exact hpow3 k' hw3) he1
      have hWe : W = Subgroup.zpowers e := (Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr he) (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, he1'])).symm
      have hwk : w ^ k ∈ Subgroup.zpowers e := hWe ▸ Subgroup.zpow_mem_zpowers w k
      obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hwk)
      set g := d ^ m with hg
      have hgc : g * c * g⁻¹ = w ^ k * c := by rw [hg, hdn m, hm]
      have hgD : g ∈ D := D.pow_mem hdD m
      have hgy : (g⁻¹ * y) * c = c * (g⁻¹ * y) := by
        have h3 : y * c * y⁻¹ = g * c * g⁻¹ := by rw [hjk, hgc, (hcwc.zpow_right k).eq]
        calc g⁻¹ * y * c = g⁻¹ * (y * c * y⁻¹) * y := by group
          _ = g⁻¹ * (g * c * g⁻¹) * y := by rw [h3]
          _ = c * (g⁻¹ * y) := by group
      have hF := hCD _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgD) hyD) hgy
      have hgB : g ∈ B := Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) m)
      rw [show y = g * (g⁻¹ * y) by group]
      exact Subgroup.mul_mem _ hgB (Subgroup.mem_sup_right hF)
    ·
      exfalso
      rw [hcj, h2] at hjk
      have hc2 : c ^ (2 : ℤ) = c * c := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two]
      rw [hc2] at hjk
      have hcc : c * c * c = 1 := by rw [← hc3]; simp only [pow_succ, pow_zero, one_mul]
      have hwk3 : w ^ k * w ^ k * w ^ k = 1 := by
        rw [← hpow3 k hw3]; simp only [pow_succ, pow_zero, one_mul]
      have hcwk : Commute c (w ^ k) := hcwc.zpow_right k
      have hyy : (y * y) * c = c * (y * y) := by
        have h3 : (y * y) * c * (y * y)⁻¹ = c := by
          calc (y * y) * c * (y * y)⁻¹ = y * (y * c * y⁻¹) * y⁻¹ := by group
            _ = y * (c * c * w ^ k) * y⁻¹ := by rw [hjk]
            _ = (y * c * y⁻¹) * (y * c * y⁻¹) * (y * w ^ k * y⁻¹) := by group
            _ = (c * c * w ^ k) * (c * c * w ^ k) * w ^ k := by
                rw [hjk, ← hwky.eq, mul_inv_cancel_right]
            _ = (c * c * (c * c)) * (w ^ k * w ^ k) * w ^ k := by
                rw [Commute.mul_mul_mul_comm (hcwk.symm.mul_right hcwk.symm)]
            _ = (c * c * c) * c * (w ^ k * w ^ k * w ^ k) := by group
            _ = c := by rw [hcc, hwk3]; group
        calc (y * y) * c = ((y * y) * c * (y * y)⁻¹) * (y * y) := by group
          _ = c * (y * y) := by rw [h3]
      have hyyF := hCD _ (Subgroup.mul_mem _ hyD hyD) hyy
      obtain ⟨n, hn⟩ := hD ⟨y, hyD⟩
      have hyn : y ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hodd : Odd (3 ^ n) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := hodd
      have hyt : y = (y * y) ^ (t + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (t + 1) = 3 ^ n + 1 by omega, pow_succ, hyn, one_mul]
      have hyF : y ∈ F₀ := by rw [hyt]; exact Subgroup.pow_mem _ hyyF _
      have hyc' : y * c * y⁻¹ = c := by rw [(hFc y hyF).eq, mul_inv_cancel_right]
      rw [hyc'] at hjk
      apply hcw
      have h4 : c * w ^ k = 1 := by
        have h5 := congrArg (fun x => c⁻¹ * x) hjk
        simp only [inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at h5
        exact h5.symm
      rw [eq_inv_of_mul_eq_one_left h4]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers w k)
  have hDB : D ≤ B := by
    by_contra hnot
    have : Group.IsNilpotent D := hD.isNilpotent
    set H := B.subgroupOf D with hH
    have hlt : H < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hnot fun x hx => ?_
      have : (⟨x, hx⟩ : D) ∈ H := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨y, hyN, hyH⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hlt)
    apply hyH
    refine Subgroup.mem_subgroupOf.mpr (hNB y y.2 fun b hb => ?_)
    have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨b, hBD hb⟩).mp (Subgroup.mem_subgroupOf.mpr hb)
    exact Subgroup.mem_subgroupOf.mp h1
  have hd9 : d ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by rfl, pow_mul]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd3
    rw [← hk]
    exact hpow3 k hw3
  have hdo : Nat.card (Subgroup.zpowers d) ≤ 9 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hd9
  have hF₀c : Nat.card F₀ ≤ 9 := by
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set X) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ((hcwc.zpow_right n).eq).symm)
    have h1 := card_sup_mul_card_inf_eq_of_le_normalizer hcN
    rw [sup_comm, inf_comm, Nat.card_zpowers, Nat.card_zpowers, hwo, hco] at h1
    have h2 : 0 < Nat.card (Subgroup.zpowers c ⊓ W : Subgroup X) := Nat.card_pos
    nlinarith
  have hcard := card_sup_mul_card_inf_eq_of_le_normalizer hdN
  rw [sup_comm, inf_comm] at hcard
  have hW3 : 3 ≤ Nat.card (Subgroup.zpowers d ⊓ F₀ : Subgroup X) := by
    have := Subgroup.card_le_of_le (le_inf hWd (le_sup_right : W ≤ F₀))
    rwa [Nat.card_zpowers, hwo] at this
  have hB27 : Nat.card B ≤ 3 ^ 3 := by
    have h1 : Nat.card B * 3 ≤ 9 * 9 := by
      calc Nat.card B * 3 ≤ Nat.card B * Nat.card (Subgroup.zpowers d ⊓ F₀ : Subgroup X) :=
            Nat.mul_le_mul_left _ hW3
        _ = Nat.card (Subgroup.zpowers d) * Nat.card F₀ := by rw [hcard, mul_comm]
        _ ≤ 9 * 9 := Nat.mul_le_mul hdo hF₀c
    norm_num
    omega
  exact (Subgroup.card_le_of_le hDB).trans hB27

end CFSG.AGLEmbedding
