module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx22
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx41

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem h_conj_eq (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y : G} (hy : y ∈ Wsub S U) :
    h * y * h⁻¹ = h⁻¹ * (h⁻¹ * y * h) * h := by
  have hc := hs.h_cube y hy
  have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
  rw [e3] at hc
  calc h * y * h⁻¹ = h * ((h * h * h)⁻¹ * ((h * h * h) * y)) * h⁻¹ := by group
    _ = h * ((h * h * h)⁻¹ * (y * (h * h * h))) * h⁻¹ := by rw [hc]
    _ = h⁻¹ * (h⁻¹ * y * h) * h := by group

theorem theta_surj_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    ∀ b ∈ U, ∃ a ∈ U, (h⁻¹ * a * h) * a⁻¹ = b := by
  intro b hb
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk
  let θ : ↥U → ↥U := fun a =>
    ⟨(h⁻¹ * (a : G) * h) * (a : G)⁻¹, mul_mem (hs.U_conj_h a.2) (inv_mem a.2)⟩
  have hinj : Function.Injective θ := by
    intro a b hab
    have h1 : (h⁻¹ * (a : G) * h) * (a : G)⁻¹ = (h⁻¹ * (b : G) * h) * (b : G)⁻¹ :=
      congrArg Subtype.val hab
    have hp : h⁻¹ * (a : G) * h = (h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G)) := by
      calc h⁻¹ * (a : G) * h = ((h⁻¹ * (a : G) * h) * (a : G)⁻¹) * (a : G) := by group
        _ = ((h⁻¹ * (b : G) * h) * (b : G)⁻¹) * (a : G) := by rw [h1]
        _ = (h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G)) := by group
    have hqU : h⁻¹ * (b : G) * h ∈ U := hs.U_conj_h b.2
    have hbaU : (b : G)⁻¹ * (a : G) ∈ U := mul_mem (inv_mem b.2) a.2
    have hc1 : (h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G)) =
        ((b : G)⁻¹ * (a : G)) * (h⁻¹ * (b : G) * h) := hs.four_comm _ hqU _ hbaU
    have hc2 : (b : G)⁻¹ * (a : G) = (a : G) * (b : G)⁻¹ := hs.four_comm _ (inv_mem b.2) _ a.2
    have hn : h⁻¹ * ((a : G) * (b : G)⁻¹) * h = (a : G) * (b : G)⁻¹ := by
      calc h⁻¹ * ((a : G) * (b : G)⁻¹) * h = (h⁻¹ * (a : G) * h) * (h⁻¹ * (b : G) * h)⁻¹ := by group
        _ = ((h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G))) * (h⁻¹ * (b : G) * h)⁻¹ := by rw [hp]
        _ = (((b : G)⁻¹ * (a : G)) * (h⁻¹ * (b : G) * h)) * (h⁻¹ * (b : G) * h)⁻¹ := by rw [hc1]
        _ = (b : G)⁻¹ * (a : G) := by group
        _ = (a : G) * (b : G)⁻¹ := hc2
    have hn1 := hs.A_fixed_trivial hII hq hrec hk (hUA (mul_mem a.2 (inv_mem b.2))) hn
    exact Subtype.ext (mul_inv_eq_one.1 hn1)
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.1 hinj ⟨b, hb⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

theorem fpf_mod_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (hY : YData S K₁ W₂ U h Y) (hcentral : ∀ y ∈ Y, ∀ c ∈ U, y * c = c * y) {g : G} (hg : g ∈ Y)
    (hgU : (h⁻¹ * g * h) * g⁻¹ ∈ U) : g ∈ U := by
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk
  obtain ⟨a, haU, hθ⟩ := hs.theta_surj_U hII hq hrec hk _ hgU
  have hg' : g * a⁻¹ ∈ Y := mul_mem hg (inv_mem (hY.A_le (hUA haU)))
  have e1 : h⁻¹ * g * h = ((h⁻¹ * g * h) * g⁻¹) * g := by group
  have e2 : h⁻¹ * a * h = ((h⁻¹ * g * h) * g⁻¹) * a := by
    calc h⁻¹ * a * h = ((h⁻¹ * a * h) * a⁻¹) * a := by group
      _ = ((h⁻¹ * g * h) * g⁻¹) * a := by rw [hθ]
  have hfixed : h⁻¹ * (g * a⁻¹) * h = g * a⁻¹ := by
    calc h⁻¹ * (g * a⁻¹) * h = (h⁻¹ * g * h) * (h⁻¹ * a * h)⁻¹ := by group
      _ = (((h⁻¹ * g * h) * g⁻¹) * g) * ((((h⁻¹ * g * h) * g⁻¹)) * a)⁻¹ := by
          rw [← e1, ← e2]
      _ = ((h⁻¹ * g * h) * g⁻¹) * (g * a⁻¹) * ((h⁻¹ * g * h) * g⁻¹)⁻¹ := by group
      _ = (g * a⁻¹) * ((h⁻¹ * g * h) * g⁻¹) * ((h⁻¹ * g * h) * g⁻¹)⁻¹ := by
          rw [← hcentral (g * a⁻¹) hg' _ hgU]
      _ = g * a⁻¹ := by group
  have h1 : g * a⁻¹ = 1 := hY.cent_h _ hg' (by
    calc h * (g * a⁻¹) = h * (h⁻¹ * (g * a⁻¹) * h) := by rw [hfixed]
      _ = (g * a⁻¹) * h := by group)
  have : g = a := mul_inv_eq_one.1 h1
  rw [this]
  exact haU

theorem Q_mem_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (hY : YData S K₁ W₂ U h Y) (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U)
    (hcentral : ∀ y ∈ Y, ∀ c ∈ U, y * c = c * y) {y : G} (hy : y ∈ Y) :
    ((h⁻¹ * y * h) * y) * (h * y * h⁻¹) ∈ U := by
  have e : h * y * h⁻¹ = h⁻¹ * (h⁻¹ * y * h) * h := hs.h_conj_eq (hY.le_W hy)
  have hy1 : h⁻¹ * y * h ∈ Y := hY.conj_h y hy
  have hy2 : h * y * h⁻¹ ∈ Y := by
    rw [e]
    exact hY.conj_h _ hy1
  apply hs.fpf_mod_U hII hq hrec hk hY hcentral (mul_mem (mul_mem hy1 hy) hy2)
  have hconj : h⁻¹ * (((h⁻¹ * y * h) * y) * (h * y * h⁻¹)) * h =
      (h⁻¹ * (h⁻¹ * y * h) * h) * (h⁻¹ * y * h) * y := by group
  rw [hconj, ← e]
  have : (h * y * h⁻¹) * (h⁻¹ * y * h) * y * (((h⁻¹ * y * h) * y) * (h * y * h⁻¹))⁻¹ =
      (h * y * h⁻¹) * ((h⁻¹ * y * h) * y) * (h * y * h⁻¹)⁻¹ * ((h⁻¹ * y * h) * y)⁻¹ := by group
  rw [this]
  exact hcomm _ hy2 _ (mul_mem hy1 hy)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
