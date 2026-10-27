module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

section Tool1

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem false_of_not_sq_dvd (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S) (hS : ¬ p ^ 2 ∣ Nat.card (MulAut S)) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, -, hcard⟩ := card_B_eq hp h
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian h.elem
  have hrp : IsPGroup p ↥ψ.range := hBp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := hrp.exists_card_eq
  let eS : PSimple p K ≃* S := (pSimpleEquiv h.core).trans e
  have hAut : Nat.card (MulAut (PSimple p K)) = Nat.card (MulAut S) :=
    Nat.card_congr (MulAut.congr eS).toEquiv
  have hdvd : p ^ j ∣ Nat.card (MulAut S) := by
    rw [← hAut, ← hj]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    exact hS ((pow_dvd_pow p hj2).trans hdvd)
  have hrange : Nat.card ψ.range ≤ p := by
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
      _ = p := pow_one p
  have h4 := h.card
  have hCpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := Nat.card_pos
  have hBle : Nat.card B ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    rw [← hcard, mul_comm]
    exact Nat.mul_le_mul_right _ hrange
  have : p ^ 4 ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := h4.trans hBle
  have h3 : p ^ 3 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    have : p * p ^ 3 ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ _ := this
    exact Nat.le_of_mul_le_mul_left this hp.pos
  omega

end Tool1

section Tool2

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

private theorem isElemAbelian_sup_of_commute {E F : Subgroup Y} (hE : IsElemAbelian p E)
    (hF : IsElemAbelian p F) (hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e) :
    IsElemAbelian p (E ⊔ F) := by
  have hEN : E ≤ Subgroup.normalizer (F : Set Y) := fun e he =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun f hf => (hcomm e he f hf).symm)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right E F hEN
  have hmem : ∀ x ∈ E ⊔ F, ∃ e ∈ E, ∃ f ∈ F, x = e * f := by
    intro x hx
    have : x ∈ (E : Set Y) * (F : Set Y) := by
      rw [← hset]
      exact hx
    obtain ⟨e, he, f, hf, rfl⟩ := Set.mem_mul.1 this
    exact ⟨e, he, f, hf, rfl⟩
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, f, hf, ha⟩ := hmem a.1 a.2
    obtain ⟨e', he', f', hf', hb⟩ := hmem b.1 b.2
    apply Subtype.ext
    show (a : Y) * b = b * a
    rw [ha, hb]
    have h1 : e * e' = e' * e := isElemAbelian_commute hE he he'
    have h2 : f * f' = f' * f := isElemAbelian_commute hF hf hf'
    have h3 : e * f' = f' * e := hcomm e he f' hf'
    have h4 : e' * f = f * e' := hcomm e' he' f hf
    have lhs : e * f * (e' * f') = (e * e') * (f * f') := by
      calc e * f * (e' * f') = e * (f * e') * f' := by group
        _ = e * (e' * f) * f' := by rw [← h4]
        _ = (e * e') * (f * f') := by group
    have rhs : e' * f' * (e * f) = (e' * e) * (f' * f) := by
      calc e' * f' * (e * f) = e' * (f' * e) * f := by group
        _ = e' * (e * f') * f := by rw [← h3]
        _ = (e' * e) * (f' * f) := by group
    rw [lhs, rhs, h1, h2]
  · obtain ⟨e, he, f, hf, rfl⟩ := hmem x hx
    have hc : Commute e f := hcomm e he f hf
    rw [hc.mul_pow, hE.2 e he, hF.2 f hf, one_mul]

end Tool2

section Inner

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem inf_centralizer_eq_bot {K : Subgroup Y} (hZ : Subgroup.center ↥K = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hcen : (⟨z, hz.1⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hz.2 (g : Y) g.2)
  rw [hZ, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem conjNormal_eq_one_iff {K : Subgroup Y} [K.Normal] (y : Y) :
    (MulAut.conjNormal y : MulAut ↥K) = 1 ↔ y ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hy x hx
    have := congrArg (fun φ : MulAut ↥K => (φ ⟨x, hx⟩ : Y)) hy
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc x * y = y * x * y⁻¹ * y := by rw [this]
      _ = y * x := by group
  · intro hy
    ext x
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    have := hy (x : Y) x.2
    calc y * (x : Y) * y⁻¹ = (x : Y) * y * y⁻¹ := by rw [this]
      _ = x := by group

theorem exists_innerPart {K B : Subgroup Y} [K.Normal] (hB : IsElemAbelian p B)
    (hKCK : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥)
    (hin : ∀ b ∈ B, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹) :
    ∃ Ē : Subgroup Y, Ē ≤ K ∧ IsElemAbelian p Ē ∧
      (∀ T : Subgroup Y, T ≤ K → B ≤ Subgroup.normalizer (T : Set Y) →
        Ē ≤ Subgroup.normalizer (T : Set Y)) ∧
      Nat.card Ē * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = Nat.card B := by
  classical
  set CK : Subgroup Y := Subgroup.centralizer (K : Set Y) with hCK
  haveI hCKn : CK.Normal := inferInstance
  set C : Subgroup Y := B ⊓ CK with hC
  let β : Y →* MulAut ↥K := MulAut.conjNormal
  have hβ : ∀ y : Y, β y = 1 ↔ y ∈ CK := fun y => conjNormal_eq_one_iff y
  set Ē : Subgroup Y := K ⊓ (B ⊔ CK) with hĒ
  have hBN : B ≤ Subgroup.normalizer (CK : Set Y) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 hCKn]; exact Subgroup.mem_top g
  have hdec : ∀ k ∈ Ē, ∃ b ∈ B, ∃ c ∈ CK, k = b * c ∧ β k = β b := by
    intro k hk
    obtain ⟨b, hb, c, hc', hbc⟩ := Subgroup.mem_sup_of_normal_right.1 hk.2
    refine ⟨b, hb, c, hc', hbc.symm, ?_⟩
    rw [← hbc, map_mul, (hβ c).2 hc', mul_one]
  have hkpow : ∀ k ∈ Ē, k ^ p = 1 := by
    intro k hk
    obtain ⟨b, hb, c, hc', -, hβk⟩ := hdec k hk
    have h1 : β (k ^ p) = 1 := by
      rw [map_pow, hβk, ← map_pow, hB.2 b hb, map_one]
    have hmem : k ^ p ∈ K ⊓ CK := ⟨K.pow_mem hk.1 p, (hβ _).1 h1⟩
    rw [hKCK, Subgroup.mem_bot] at hmem
    exact hmem
  have hĒel : IsElemAbelian p Ē := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hkpow x hx⟩
    obtain ⟨b₁, hb₁, c₁, hc₁, -, hβ₁⟩ := hdec a.1 a.2
    obtain ⟨b₂, hb₂, c₂, hc₂, -, hβ₂⟩ := hdec b.1 b.2
    apply Subtype.ext
    show (a : Y) * b = b * a
    have hcommβ : β ((a : Y) * b * (a : Y)⁻¹ * (b : Y)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hβ₁, hβ₂]
      have hbc : β b₁ * β b₂ = β b₂ * β b₁ := by
        rw [← map_mul, ← map_mul, isElemAbelian_commute hB hb₁ hb₂]
      calc β b₁ * β b₂ * (β b₁)⁻¹ * (β b₂)⁻¹ = β b₂ * β b₁ * (β b₁)⁻¹ * (β b₂)⁻¹ := by rw [hbc]
        _ = 1 := by group
    have hmem : (a : Y) * b * (a : Y)⁻¹ * (b : Y)⁻¹ ∈ K ⊓ CK :=
      ⟨K.mul_mem (K.mul_mem (K.mul_mem a.2.1 b.2.1) (K.inv_mem a.2.1)) (K.inv_mem b.2.1),
        (hβ _).1 hcommβ⟩
    rw [hKCK, Subgroup.mem_bot] at hmem
    have hx : (a : Y) * b * (a : Y)⁻¹ = b := mul_inv_eq_one.1 hmem
    calc (a : Y) * b = (a : Y) * b * (a : Y)⁻¹ * a := by group
      _ = b * a := by rw [hx]
  have hĒN : ∀ T : Subgroup Y, T ≤ K → B ≤ Subgroup.normalizer (T : Set Y) →
      Ē ≤ Subgroup.normalizer (T : Set Y) := by
    intro T hTK hBT k hk
    have key : ∀ k ∈ Ē, ∀ t ∈ T, k * t * k⁻¹ ∈ T := by
      intro k hk t ht
      obtain ⟨b, hb, c, hc', hkbc, -⟩ := hdec k hk
      have h1 : k * t * k⁻¹ = b * t * b⁻¹ := by
        have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.1 hc' t (hTK ht)).symm
        rw [hkbc]
        calc b * c * t * (b * c)⁻¹ = b * (c * t) * c⁻¹ * b⁻¹ := by group
          _ = b * (t * c) * c⁻¹ * b⁻¹ := by rw [hct]
          _ = b * t * b⁻¹ := by group
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => key k hk y hy
    · intro hy
      have := key k⁻¹ (Ē.inv_mem hk) _ hy
      simpa [mul_assoc] using this
  have hĒCK : Ē ≤ Subgroup.normalizer (CK : Set Y) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 hCKn]; exact Subgroup.mem_top g
  have hsup : CK ⊔ Ē = CK ⊔ B := by
    apply le_antisymm
    · exact sup_le le_sup_left (le_trans inf_le_right (sup_le le_sup_right le_sup_left))
    · refine sup_le le_sup_left ?_
      intro b hb
      obtain ⟨k, hkK, hk⟩ := hin b hb
      have hc1 : b⁻¹ * k ∈ CK := by
        rw [hCK, Subgroup.mem_centralizer_iff]
        intro x hx
        have := hk x hx
        calc x * (b⁻¹ * k) = b⁻¹ * (b * x * b⁻¹) * k := by group
          _ = b⁻¹ * (k * x * k⁻¹) * k := by rw [this]
          _ = (b⁻¹ * k) * x := by group
      have hkĒ : k ∈ Ē :=
        ⟨hkK, Subgroup.mem_sup_of_normal_right.2 ⟨b, hb, b⁻¹ * k, hc1, by group⟩⟩
      have : b = k * (b⁻¹ * k)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkĒ)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hc1))
  refine ⟨Ē, inf_le_left, hĒel, hĒN, ?_⟩
  have h1 := card_sup_mul_card_inf_of_le_normalizer hBN
  have h2 := card_sup_mul_card_inf_of_le_normalizer hĒCK
  have hbot : CK ⊓ Ē = ⊥ := by
    rw [eq_bot_iff, ← hKCK]
    exact le_inf (le_trans inf_le_right inf_le_left) inf_le_left
  rw [hbot, Subgroup.card_bot, mul_one, hsup] at h2
  have hCinf : CK ⊓ B = C := inf_comm _ _
  rw [hCinf] at h1
  have hpos : 0 < Nat.card CK := Nat.card_pos
  have : Nat.card CK * (Nat.card Ē * Nat.card C) = Nat.card CK * Nat.card B := by
    calc Nat.card CK * (Nat.card Ē * Nat.card C) = (Nat.card CK * Nat.card Ē) * Nat.card C := by ring
      _ = Nat.card (CK ⊔ B : Subgroup Y) * Nat.card C := by rw [h2]
      _ = Nat.card CK * Nat.card B := h1
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem false_of_inner {K B : Subgroup Y} (h : KHyp p K B)
    (hZ : Subgroup.center ↥K = ⊥)
    (hin : ∀ b ∈ B, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹)
    {R : ℕ}
    (hR : ∀ E T : Subgroup Y, E ≤ K → IsElemAbelian p E → T ≤ K → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set Y) → Nat.card E ≤ R)
    (hE₀ : ∃ E₀ : Subgroup Y, E₀ ≤ K ∧ IsElemAbelian p E₀ ∧ R < Nat.card E₀) : False := by
  classical
  haveI := h.normal
  have hKCK := inf_centralizer_eq_bot hZ
  obtain ⟨Ē, hĒK, hĒel, hĒN, hcard⟩ := exists_innerPart (p := p) h.elem hKCK hin
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := h.twogrp
  have hĒR : Nat.card Ē ≤ R := hR Ē T hĒK hĒel hTK hT2 hTne (hĒN T hTK hBT)
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hC
  have hBR : Nat.card B ≤ R * Nat.card C := by
    rw [← hcard]
    exact Nat.mul_le_mul_right _ hĒR
  obtain ⟨E₀, hE₀K, hE₀el, hE₀R⟩ := hE₀
  have hCel : IsElemAbelian p C := isElemAbelian_mono h.elem inf_le_left
  have hcomm : ∀ e ∈ E₀, ∀ c ∈ C, e * c = c * e := fun e he c hcc =>
    Subgroup.mem_centralizer_iff.1 hcc.2 e (hE₀K he)
  have hsupel : IsElemAbelian p (E₀ ⊔ C) := isElemAbelian_sup_of_commute hE₀el hCel hcomm
  have hCN : C ≤ Subgroup.normalizer (E₀ : Set Y) := fun c hcc =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun e he => hcomm e he c hcc)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCN
  have hinf : E₀ ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hKCK]
    exact le_inf (inf_le_left.trans hE₀K) (inf_le_right.trans inf_le_right)
  rw [hinf, Subgroup.card_bot, mul_one] at hprod
  have hle : Nat.card (E₀ ⊔ C : Subgroup Y) ≤ Nat.card B := h.maxrank _ le_top hsupel
  have h1 : Nat.card E₀ * Nat.card C ≤ R * Nat.card C := by
    rw [← hprod]
    exact hle.trans hBR
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have := Nat.le_of_mul_le_mul_right h1 hCpos
  omega

end Inner

end CFSG.LocalAnalysis.GLTheoremA
