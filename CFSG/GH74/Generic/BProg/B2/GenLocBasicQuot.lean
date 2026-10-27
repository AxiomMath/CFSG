module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace GenLocBasic

section Quot

variable {J : Type} [Group J] {A : Type} [Group A]

theorem comm_central_mul (h₁ h₂ z₁ z₂ : J) (hz₁ : z₁ ∈ center J) (hz₂ : z₂ ∈ center J) :
    (h₁ * z₁) * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by
  have cm : ∀ z : J, z ∈ center J → ∀ g X : J, z * (g * X) = g * (z * X) := by
    intro z hz g X
    rw [← mul_assoc, ← mem_center_iff.1 hz g, mul_assoc]
  simp only [mul_inv_rev, mul_assoc]
  rw [cm z₁ hz₁ h₂, cm z₁ hz₁ z₂, mul_inv_cancel_left, cm z₂ hz₂ h₁⁻¹, mul_inv_cancel_left]

theorem exists_fixed_lift [Finite J] (Z : Subgroup J) [Z.Normal] (hodd : Odd (Nat.card ↥Z))
    (α : A →* MulAut J) (α' : A →* MulAut (J ⧸ Z))
    (hcompat : ∀ (a : A) (x : J), α' a (QuotientGroup.mk x) = QuotientGroup.mk (α a x))
    (E : Subgroup A) (hE : IsPGroup 2 ↥E) (x : J)
    (hfix : ∀ a ∈ E, α' a (QuotientGroup.mk x) = QuotientGroup.mk x) :
    ∃ y : J, (QuotientGroup.mk y : J ⧸ Z) = QuotientGroup.mk x ∧ ∀ a ∈ E, α a y = y := by
  let S : Type := {w : J // (QuotientGroup.mk w : J ⧸ Z) = QuotientGroup.mk x}
  let _ : MulAction ↥E S :=
    { smul := fun a w => ⟨α (a : A) w.1, by rw [← hcompat, w.2]; exact hfix a a.2⟩
      one_smul := fun w => Subtype.ext (by
        change α (((1 : ↥E) : A)) w.1 = w.1
        simp)
      mul_smul := fun a b w => Subtype.ext (by
        change α (((a * b : ↥E) : A)) w.1 = α (a : A) (α (b : A) w.1)
        simp [map_mul]) }
  let f : S ≃ ↥Z :=
    { toFun := fun w => ⟨x⁻¹ * w.1, QuotientGroup.eq.1 w.2.symm⟩
      invFun := fun z => ⟨x * z.1, by
        rw [QuotientGroup.eq]
        simp⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  have hcard : Nat.card S = Nat.card ↥Z := Nat.card_congr f
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := IsPGroup.card_modEq_card_fixedPoints hE S
  have hne : Nat.card ↑(MulAction.fixedPoints ↥E S) ≠ 0 := by
    intro h0
    rw [h0, hcard] at hmod
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((Nat.modEq_zero_iff_dvd).1 hmod))
  obtain ⟨⟨⟨w, hw⟩⟩, -⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  refine ⟨w.1, w.2, fun a ha => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hw ⟨a, ha⟩)

theorem fixedIn_quotient_le [Finite J] (hA : CFSG.IsElementaryAbelian 2 A) (Z : Subgroup J) [Z.Normal]
    (hodd : Odd (Nat.card ↥Z)) (α : A →* MulAut J) (α' : A →* MulAut (J ⧸ Z))
    (hcompat : ∀ (a : A) (x : J), α' a (QuotientGroup.mk x) = QuotientGroup.mk (α a x))
    (E : Subgroup A) :
    fixedIn (J ⧸ Z) (E.map α') ≤ (fixedIn J (E.map α)).map (QuotientGroup.mk' Z) := by
  intro xb hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have := isEA_subgroup hA E
  have hE : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
  obtain ⟨y, hy, hfixy⟩ := exists_fixed_lift Z hodd α α' hcompat E hE x
    (fun a ha => (mem_fixedIn_map α' E _).1 hx a ha)
  exact ⟨y, (mem_fixedIn_map α E y).2 hfixy, hy⟩

end Quot

end GenLocBasic

section G8

variable {J : Type} [Group J] {A : Type} [Group A]

theorem gammaAct_eq_top_of_quotient [Finite J] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hperf : commutator J = ⊤) (Z : Subgroup J) [Z.Normal] (hZ : Z ≤ center J)
    (hodd : Odd (Nat.card ↥Z)) (α : A →* MulAut J) (α' : A →* MulAut (J ⧸ Z))
    (hcompat : ∀ (a : A) (x : J), α' a (QuotientGroup.mk x) = QuotientGroup.mk (α a x))
    (h : gammaAct α' = ⊤) : gammaAct α = ⊤ := by
  have hle : gammaAct α' ≤ (gammaAct α).map (QuotientGroup.mk' Z) := by
    refine iSup₂_le fun E hE => ?_
    exact (GenLocBasic.fixedIn_quotient_le hA Z hodd α α' hcompat E).trans
      (Subgroup.map_mono (le_gammaAct α hE))
  rw [h, top_le_iff] at hle
  have hsurj : ∀ g : J, ∃ h ∈ gammaAct α, ∃ z ∈ Z, g = h * z := by
    intro g
    have hg : QuotientGroup.mk' Z g ∈ (gammaAct α).map (QuotientGroup.mk' Z) := by
      rw [hle]; trivial
    obtain ⟨h, hh, hhg⟩ := hg
    exact ⟨h, hh, h⁻¹ * g, QuotientGroup.eq.1 hhg, by group⟩
  have hcomm : commutator J ≤ gammaAct α := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hsurj g₁
    obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hsurj g₂
    change (h₁ * z₁) * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹ ∈ gammaAct α
    rw [GenLocBasic.comm_central_mul h₁ h₂ z₁ z₂ (hZ hz₁) (hZ hz₂)]
    exact mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)
  rw [hperf] at hcomm
  exact top_le_iff.1 hcomm

end G8

end CFSG.GH74.Generic.BProg.B2
