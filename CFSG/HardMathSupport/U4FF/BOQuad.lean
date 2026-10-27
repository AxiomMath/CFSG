module

public import CFSG.HardMathSupport.U4FF.BOSemi
public import CFSG.HardMathSupport.U4FF.BOCore

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix CFSG.LocalAnalysis.RankThreeUC CFSG.Open Module
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)

section Arith

theorem bo_arith_lin {b c q r : ℕ} (hq : 0 < q) (hr : r ≤ 3)
    (hb : b ≤ 2 * q ^ (r * (r - 1) / 2)) (hc : c = q ^ (6 - r)) : b * c ≤ 2 * q ^ 6 := by
  have hexp : r * (r - 1) / 2 + (6 - r) ≤ 6 := by interval_cases r <;> norm_num
  calc b * c ≤ 2 * q ^ (r * (r - 1) / 2) * q ^ (6 - r) := by
        rw [hc]
        exact Nat.mul_le_mul_right _ hb
    _ = 2 * q ^ (r * (r - 1) / 2 + (6 - r)) := by rw [pow_add]; ring
    _ ≤ 2 * q ^ 6 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hq hexp)

theorem bo_arith_nonlin {b c l q r : ℕ} (hq : 4 ≤ q) (hr : r ≤ 3) (hb : b ≤ 2 * l)
    (hl : l ≤ 2 * q ^ (r * (r - 1) / 2)) (hc : c ^ 2 ≤ q ^ (6 - r)) : b * c ≤ 2 * q ^ 6 := by
  have hq0 : 0 < q := by omega
  have hb2 : b ≤ 4 * q ^ (r * (r - 1) / 2) := by omega
  have hexp : 2 * (r * (r - 1) / 2) + (6 - r) ≤ 9 := by interval_cases r <;> norm_num
  have h64 : 4 ≤ q ^ 3 := by
    calc 4 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 3 := Nat.pow_le_pow_right hq0 (by norm_num)
  have hsq : (b * c) ^ 2 ≤ (2 * q ^ 6) ^ 2 := by
    calc (b * c) ^ 2 = b ^ 2 * c ^ 2 := mul_pow b c 2
      _ ≤ (4 * q ^ (r * (r - 1) / 2)) ^ 2 * q ^ (6 - r) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hb2 2) hc
      _ = 4 * (q ^ (2 * (r * (r - 1) / 2) + (6 - r)) * 4) := by
          rw [pow_add, pow_mul]
          ring
      _ ≤ 4 * (q ^ (2 * (r * (r - 1) / 2) + (6 - r)) * q ^ 3) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h64)
      _ ≤ 4 * q ^ 12 := by
          have : q ^ (2 * (r * (r - 1) / 2) + (6 - r)) * q ^ 3 ≤ q ^ 12 := by
            rw [← pow_add]
            exact Nat.pow_le_pow_right hq0 (by omega)
          omega
      _ = (2 * q ^ 6) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left two_ne_zero).mp hsq

end Arith

section Small

theorem eq_zero_or_one_of_card_two {F : Type} [Field F] [Finite F] (h : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  classical
  by_contra hc
  push Not at hc
  haveI := Fintype.ofFinite F
  have h3 : ({0, 1, c} : Finset F).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm, rfl⟩
  have := Finset.card_le_univ ({0, 1, c} : Finset F)
  rw [← Nat.card_eq_fintype_card, h] at this
  omega

theorem four_le_card_of_ne {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {θ : F →+* F} (hne : ∃ c, θ c ≠ c) : 4 ≤ Nat.card F := by
  obtain ⟨c, hc⟩ := hne
  by_contra hlt
  push Not at hlt
  have hn1 : n = 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  subst hn1
  have h2 : Nat.card F = 2 := by rw [hF]; norm_num
  rcases eq_zero_or_one_of_card_two h2 c with rfl | rfl
  · exact hc (map_zero θ)
  · exact hc (map_one θ)

end Small

section Quadratic

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

@[expose] def boLinEnd (a : AddAut (OIdx → F)) (ha : boIsLin a) : Module.End F (OIdx → F) where
  toFun x := a x - x
  map_add' x y := by
    rw [map_add a x y]
    abel
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [ha r x, smul_sub]

theorem partBO_quadratic {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (B : AddSubgroup (AddAut (OIdx → F)))
    (h2 : ∀ a ∈ B, a + a = 0)
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ x, a (b x - x) = b x - x)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OIdx → F,
        a (((g : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x) =
          ((g' : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ (a x)) :
    Nat.card B * Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x} ≤ 2 * Nat.card (OIdx → F) := by
  classical
  haveI : Nonempty OIdx := ⟨Sum.inr (Sum.inr 0)⟩
  have hsemi : ∀ a ∈ B, ∃ θ : F →+* F, ∀ (c : F) (x : OIdx → F), a (c • x) = θ c • a x :=
    fun a ha => bo_exists_semilinear_omega hirr (h2 a ha) (hN a ha)
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a + b = b + a := fun a ha b hb => AddEquiv.ext fun x => by
    show a (b x) = b (a x)
    have h1 := hquad a ha b hb x
    have h2' := hquad b hb a ha x
    rw [map_sub] at h1 h2'
    linear_combination h1 - h2'
  have hisoL : ∀ a ∈ boLinSub B, ∀ x, quadMinus 3 F b c (a x) = quadMinus 3 F b c x :=
    fun a ha x => by
      have := bo_isometry_of_isLin hirr (h2 a ha.1) ha.2 (hN a ha.1) x
      rwa [← coe_quadMinus 3 F b c] at this
  let Λ : boLinSub B →+ Module.End F (OIdx → F) :=
    AddMonoidHom.mk' (fun a => boLinEnd a.1 a.2.2) (fun a a' => LinearMap.ext fun x => by
      show (a + a' : boLinSub B).1 x - x = (a.1 x - x) + (a'.1 x - x)
      have hq := hquad a.1 a.2.1 a'.1 a'.2.1 x
      rw [map_sub] at hq
      rw [AddSubgroup.coe_add, bo_add_apply]
      linear_combination hq)
  have hΛapp : ∀ (a : boLinSub B) (x : OIdx → F), Λ a x = a.1 x - x := fun a x => rfl
  have hΛinj : Function.Injective Λ := fun a a' h => Subtype.ext (AddEquiv.ext fun x => by
    have := congrArg (fun φ : Module.End F (OIdx → F) => φ x) h
    simp only [hΛapp] at this
    exact sub_left_inj.mp this)
  have hsq : ∀ φ ∈ Λ.range, ∀ ψ ∈ Λ.range, ∀ x, φ (ψ x) = 0 := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ x
    rw [hΛapp, hΛapp]
    rw [hquad a.1 a.2.1 a'.1 a'.2.1 x, sub_self]
  have hiso : ∀ φ ∈ Λ.range, ∀ x, quadMinus 3 F b c (x + φ x) = quadMinus 3 F b c x := by
    rintro _ ⟨a, rfl⟩ x
    rw [hΛapp, add_sub_cancel]
    exact hisoL a.1 a.2 x
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hdim : finrank F (OIdx → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [OIdx]
  obtain ⟨r, hr3, hCr, hΦr⟩ := quad_count_params hnd hsq hiso hdim
  have hΦcard : Nat.card Λ.range = Nat.card (boLinSub B) :=
    (Nat.card_congr (AddMonoidHom.ofInjective hΛinj).toEquiv).symm
  have hfix : fixSub Λ.range = boLinFix B := by
    ext x
    rw [mem_fixSub, mem_boLinFix]
    constructor
    · intro h a ha
      have := h (Λ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
      rw [hΛapp] at this
      exact sub_eq_zero.mp this
    · rintro h _ ⟨a, rfl⟩
      rw [hΛapp, h a.1 a.2, sub_self]
  rw [hfix] at hCr
  rw [hΦcard] at hΦr
  have hq6 : Nat.card (OIdx → F) = Nat.card F ^ 6 := by
    rw [Nat.card_fun]
    simp [OIdx]
  have hq0 : 0 < Nat.card F := Nat.card_pos
  rw [hq6]
  by_cases hall : ∀ a ∈ B, boIsLin a
  · have hBc : Nat.card B = Nat.card (boLinSub B) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun a =>
        ⟨fun ha => ⟨ha, hall a ha⟩, fun h => h.1⟩)
    have hfixc : Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x} = Nat.card (boLinFix B) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun hx a ha => hx a (mem_boLinSub.mp ha).1, fun hx a ha => hx a ⟨ha, hall a ha⟩⟩)
    rw [hBc, hfixc]
    exact bo_arith_lin hq0 hr3 hΦr hCr
  · obtain ⟨s, hsB, hsnl⟩ : ∃ s ∈ B, ¬ boIsLin s := by
      by_contra h
      exact hall fun a ha => by_contra fun hna => h ⟨a, ha, hna⟩
    obtain ⟨θ, hθ⟩ := hsemi s hsB
    have hq4 : 4 ≤ Nat.card F := four_le_card_of_ne hn hF (bo_exists_ne hθ hsnl)
    have hb := bo_card_le_two B h2 hsemi hsB hsnl
    have hc := bo_nonlin_fix_sq B h2 hcomm hsemi hsB hsnl
    rw [hCr] at hc
    exact bo_arith_nonlin hq4 hr3 hb hΦr hc

end Quadratic

end CFSG.HardMathSupport.U4FF
