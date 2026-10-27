module

public import CFSG.ClassicalInvolution.Q3.Q3PPKleinAt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups

section Abstract

theorem KleinData.of_conjClass {c : CompData} {R₀ : Subgroup c.G} {ρ ρ₁ ρ₂ : c.G}
    (hfund : ∀ R, R ∈ c.fund ↔ ∃ g, R = conjSub g R₀) (hcenter : Subgroup.center c.G = ⊥)
    (huniq : ∀ a ∈ R₀, a * a = 1 → a ≠ 1 → a = ρ)
    (hρ₁ : ∃ g, ρ₁ = g * ρ * g⁻¹) (hρ₂ : ∃ g, ρ₂ = g * ρ * g⁻¹)
    (hcomm : ρ₁ * ρ = ρ * ρ₁) (hprod : ρ * ρ₁ = ρ₂) (hne : ρ₁ ≠ ρ) : KleinData c := by
  have key : ∀ g : c.G, ∀ x ∈ conjSub g R₀, x * x = 1 → x ≠ 1 → x = g * ρ * g⁻¹ := by
    intro g x hx hx2 hx1
    rw [mem_conjSub_iff] at hx
    have h2 : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
      calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [hx2]; group
    have h1 : g⁻¹ * x * g ≠ 1 := by
      intro h
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]
      group
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * ρ * g⁻¹ := by rw [huniq _ hx h2 h1]
  refine ⟨hcenter, ?_, ?_, ?_⟩
  · intro R hR a ha b hb ha2 hb2 ha1 hb1
    obtain ⟨g, rfl⟩ := (hfund R).mp hR
    rw [key g a ha ha2 ha1, key g b hb hb2 hb1]
  · intro R hR g
    obtain ⟨h, rfl⟩ := (hfund R).mp hR
    refine (hfund _).mpr ⟨g * h, ?_⟩
    ext x
    simp only [mem_conjSub_iff]
    have e : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
    rw [e]
  · intro R hR r hrR hr2 hr1
    obtain ⟨g, rfl⟩ := (hfund R).mp hR
    have hr : r = g * ρ * g⁻¹ := key g r hrR hr2 hr1
    obtain ⟨g₁, hg₁⟩ := hρ₁
    obtain ⟨g₂, hg₂⟩ := hρ₂
    refine ⟨g * ρ₁ * g⁻¹, g * g₁ * g⁻¹, g * g₂ * g⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [hr, hg₁]
      group
    · rw [hr]
      calc g * ρ * g⁻¹ * (g * ρ₁ * g⁻¹) = g * (ρ * ρ₁) * g⁻¹ := by group
        _ = g * ρ₂ * g⁻¹ := by rw [hprod]
        _ = g * g₂ * g⁻¹ * (g * ρ * g⁻¹) * (g * g₂ * g⁻¹)⁻¹ := by rw [hg₂]; group
    · rw [hr]
      calc g * ρ₁ * g⁻¹ * (g * ρ * g⁻¹) = g * (ρ₁ * ρ) * g⁻¹ := by group
        _ = g * (ρ * ρ₁) * g⁻¹ := by rw [hcomm]
        _ = g * ρ * g⁻¹ * (g * ρ₁ * g⁻¹) := by group
    · rw [hr]
      intro h
      apply hne
      exact mul_left_cancel (mul_right_cancel h)

end Abstract

section SL3

theorem center_sl_three_eq_bot : Subgroup.center SL(3, GaloisField 3 1) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have h3 : (r - 1) ^ 3 = 0 := by
    rw [sub_pow_char (p := 3), hr3, one_pow, sub_self]
  have h1 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)
  subst h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

theorem kleinData_psl_three : KleinData (CompData.model .PSL 3) := by
  have hn : 2 ≤ 3 := by norm_num
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  let T₀ : Models.Pair 3 :=
    ⟨{⟨0, by omega⟩, ⟨0 + 1, by omega⟩}, Finset.card_pair (by simp)⟩
  let T₁ : Models.Pair 3 :=
    ⟨{⟨0, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₂ : Models.Pair 3 :=
    ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hroot : Models.rootInv (GaloisField 3 1) hn = Models.zElt (GaloisField 3 1) T₀ := by
    apply Subtype.ext
    rw [Models.coe_rootInv, Models.coe_zElt, Models.negBlock_eq_zMat (by omega : 0 + 2 ≤ 3)]
  have hfund : ∀ R : Subgroup SL(3, GaloisField 3 1),
      R ∈ (CompData.model .PSL 3).fund ↔
        ∃ g, R = conjSub g (Models.rootSL2 (GaloisField 3 1) hn) := by
    intro R
    have := Set.ext_iff.mp (Exotic.fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := 2)
      (by omega)) R
    exact this.trans (Models.mem_longRootSet_iff hn)
  have hstd := Models.isLongRootSL2_standard (K := GaloisField 3 1) hn
  have hprod' : Models.zElt (GaloisField 3 1) T₀ * Models.zElt (GaloisField 3 1) T₁ =
      Models.zElt (GaloisField 3 1) T₂ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Models.coe_zElt, Models.coe_zElt, Models.coe_zElt]
    simp only [Models.zMat, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    fin_cases a <;> simp [T₀, T₁, T₂]
  refine KleinData.of_conjClass (R₀ := Models.rootSL2 (GaloisField 3 1) hn)
    (ρ := Models.rootInv (GaloisField 3 1) hn) (ρ₁ := Models.zElt (GaloisField 3 1) T₁)
    (ρ₂ := Models.zElt (GaloisField 3 1) T₂) hfund center_sl_three_eq_bot ?_ ?_ ?_ ?_ ?_ ?_
  · have huniq : ∀ b : SL(3, GaloisField 3 1), b ∈ Models.rootSL2 (GaloisField 3 1) hn →
        b * b = 1 → b ≠ 1 → b = Models.rootInv (GaloisField 3 1) hn := by
      intro b hb hb2 hb1
      exact hstd.eq_of_orderOf_eq_two h2 hb (orderOf_eq_prime (by rwa [pow_two]) hb1)
    intro a ha ha2 ha1
    exact huniq a ha ha2 ha1
  · obtain ⟨g, -, hg⟩ := Models.isLongRootSL2_Lc h2 hn T₁
    exact ⟨g, hg⟩
  · obtain ⟨g, -, hg⟩ := Models.isLongRootSL2_Lc h2 hn T₂
    exact ⟨g, hg⟩
  · rw [hroot]
    exact Models.signGroup_comm (Models.zElt_mem_signGroup T₁) (Models.zElt_mem_signGroup T₀)
  · rw [hroot]
    exact hprod'
  · rw [hroot]
    intro h
    have h01 : T₁ = T₀ := Models.zElt_injective h2 h
    have := congrArg Subtype.val h01
    exact absurd this (by decide)

end SL3

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

theorem EdgeData.kleinAt_of_psl_three (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hk : D.kind i = CompData.model .PSL 3) : KleinAt K K₁ z₂ :=
  h.kleinAt_of_kleinData hR D hi (by rw [hk]; exact kleinData_psl_three)

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
