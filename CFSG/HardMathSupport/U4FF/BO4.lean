module

public import CFSG.HardMathSupport.U4FF.BOQuad

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix CFSG.LocalAnalysis.RankThreeUC CFSG.Open Module QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem bo_polar_isometry {a : AddAut (OIdx → F)}
    (hiso : ∀ x, quadMinus 3 F b c (a x) = quadMinus 3 F b c x) (x y : OIdx → F) :
    polar (quadMinus 3 F b c) (a x) (a y) = polar (quadMinus 3 F b c) x y := by
  simp only [polar]
  rw [← map_add a x y, hiso (x + y), hiso x, hiso y]

theorem bo4_linear (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (B : AddSubgroup (AddAut (OIdx → F)))
    (h2 : ∀ a ∈ B, a + a = 0) (hall : ∀ a ∈ B, boIsLin a)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OIdx → F,
        a (((g : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x) =
          ((g' : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ (a x))
    (hcard : Nat.card B = 4)
    (hidx : Nat.card (OIdx → F) = 2 * Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x}) : False := by
  classical
  have hiso : ∀ a ∈ B, ∀ x, quadMinus 3 F b c (a x) = quadMinus 3 F b c x := fun a ha x => by
    have := bo_isometry_of_isLin hirr (h2 a ha) (hall a ha) (hN a ha) x
    rwa [← coe_quadMinus 3 F b c] at this
  let C : Submodule F (OIdx → F) :=
    { carrier := {x | ∀ a ∈ B, a x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => map_zero a
      smul_mem' := fun r {x} hx a ha => by rw [hall a ha r x, hx a ha] }
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hdim : finrank F (OIdx → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [OIdx]
  have hq6 : Nat.card (OIdx → F) = Nat.card F ^ 6 := by
    rw [Nat.card_fun]
    simp [OIdx]
  let D := LinearMap.BilinForm.orthogonal (polarBilin (quadMinus 3 F b c)) C
  have hDrank : finrank F D = 6 - finrank F C := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd C, hdim]
  have hCle : finrank F C ≤ 6 := hdim ▸ Submodule.finrank_le C
  have hCD : Nat.card C * Nat.card D = Nat.card F ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := C),
      Module.natCard_eq_pow_finrank (K := F) (V := D), ← pow_add, hDrank,
      Nat.add_sub_cancel' hCle]
  have hCc : Nat.card C = Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hD2 : Nat.card D = 2 := by
    have h1 : Nat.card C * Nat.card D = Nat.card C * 2 := by
      rw [hCD, ← hq6, hidx, ← hCc, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hCpos h1
  have hindex : C.toAddSubgroup.index = 2 := by
    have h := AddSubgroup.card_mul_index C.toAddSubgroup
    have h1 : Nat.card C.toAddSubgroup = Nat.card C := rfl
    rw [h1, hidx, ← hCc, mul_comm 2] at h
    exact Nat.eq_of_mul_eq_mul_left hCpos h
  obtain ⟨x₀, hx₀⟩ := (AddSubgroup.index_eq_two_iff).mp hindex
  have hcase : ∀ x, x ∈ C ∨ x + x₀ ∈ C := fun x => by
    by_cases hx : x ∈ C
    · exact Or.inl hx
    · right
      rcases hx₀ x with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd h1 hx
  have hmemD : ∀ a ∈ B, a x₀ - x₀ ∈ D := fun a ha => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [polarBilin_apply_apply, polar_comm, polar_sub_left]
    have h1 := bo_polar_isometry (hiso a ha) x₀ y
    rw [hy a ha] at h1
    rw [h1, sub_self]
  let Θ : B → D := fun a => ⟨a.1 x₀ - x₀, hmemD a.1 a.2⟩
  have hΘ : Function.Injective Θ := by
    intro a a' h
    have h' : a.1 x₀ - x₀ = a'.1 x₀ - x₀ := congrArg Subtype.val h
    have hx0 : a.1 x₀ = a'.1 x₀ := sub_left_inj.mp h'
    apply Subtype.ext
    apply AddEquiv.ext
    intro x
    rcases hcase x with hx | hx
    · rw [hx a.1 a.2, hx a'.1 a'.2]
    · have e1 : a.1 (x + x₀) = x + x₀ := hx a.1 a.2
      have e2 : a'.1 (x + x₀) = x + x₀ := hx a'.1 a'.2
      rw [map_add, hx0] at e1
      rw [map_add] at e2
      exact add_right_cancel (e1.trans e2.symm)
  have hle := Nat.card_le_card_of_injective Θ hΘ
  omega

theorem partBO4_sub {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (B : AddSubgroup (AddAut (OIdx → F)))
    (h2 : ∀ a ∈ B, a + a = 0) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a + b = b + a)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OIdx → F,
        a (((g : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x) =
          ((g' : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ (a x))
    (hcard : Nat.card B = 4)
    (hidx : Nat.card (OIdx → F) = 2 * Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x}) : False := by
  classical
  haveI : Nonempty OIdx := ⟨Sum.inr (Sum.inr 0)⟩
  have hsemi : ∀ a ∈ B, ∃ θ : F →+* F, ∀ (c : F) (x : OIdx → F), a (c • x) = θ c • a x :=
    fun a ha => bo_exists_semilinear_omega hirr (h2 a ha) (hN a ha)
  by_cases hall : ∀ a ∈ B, boIsLin a
  · exact bo4_linear hirr B h2 hall hN hcard hidx
  · obtain ⟨s, hsB, hsnl⟩ : ∃ s ∈ B, ¬ boIsLin s := by
      by_contra h
      exact hall fun a ha => by_contra fun hna => h ⟨a, ha, hna⟩
    obtain ⟨θ, hθ⟩ := hsemi s hsB
    have hq4 : 4 ≤ Nat.card F := four_le_card_of_ne hn hF (bo_exists_ne hθ hsnl)
    have hc := bo_nonlin_fix_sq B h2 hcomm hsemi hsB hsnl
    have hq6 : Nat.card (OIdx → F) = Nat.card F ^ 6 := by
      rw [Nat.card_fun]
      simp [OIdx]
    have hle : Nat.card (boLinFix B) ≤ Nat.card (OIdx → F) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    haveI : Nonempty {x : OIdx → F // ∀ a ∈ B, a x = x} := ⟨⟨0, fun a _ => map_zero a⟩⟩
    have hCpos : 0 < Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x} := Nat.card_pos
    have h64 : 4 ^ 6 ≤ Nat.card F ^ 6 := Nat.pow_le_pow_left hq4 6
    have hW4 : 4096 ≤ Nat.card (OIdx → F) := by
      rw [hq6]
      calc 4096 = 4 ^ 6 := by norm_num
        _ ≤ Nat.card F ^ 6 := h64
    generalize Nat.card {x : OIdx → F // ∀ a ∈ B, a x = x} = C at hc hidx hCpos
    have hCle : C ≤ 2 := by nlinarith
    omega

end CFSG.HardMathSupport.U4FF
