module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx42

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem Y_inf_Nh (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hY : YData S K₁ W₂ U h Y) : Y ⊓ Nh S h = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  exact hY.cent_h y hy.1 (hs.W_Nh_comm hII (hY.le_W hy.1) hy.2).symm

theorem S_eq_sup (hY : YData S K₁ W₂ U h Y) : S = Y ⊔ Nh S h := by
  apply le_antisymm
  · intro s hs
    obtain ⟨y, hy, d, hd, rfl⟩ := hY.decomp s hs
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hd)
  · exact sup_le hY.Y_le_S Nh_le_S

theorem card_S (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hY : YData S K₁ W₂ U h Y) : Nat.card ↥S = 64 * Nat.card ↥(Nh S h) := by
  have h1 := Basic.card_sup_mul_card_inf' (A := Y) (B := Nh S h) hY.Nh_le_normalizer
  rw [hY.Y_inf_Nh hII hs, Subgroup.card_bot, mul_one, ← hY.S_eq_sup, hY.card] at h1
  exact h1

end YData

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem card_Nh_cases (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : 2 ^ 7 ≤ Nat.card ↥S) (hY : YData S K₁ W₂ U h Y) :
    Nat.card ↥(Nh S h) = 2 ∨ Nat.card ↥(Nh S h) = 4 := by
  have h1 := hY.card_S hII hs
  obtain ⟨-, hcases⟩ := hs.cases8_aux hII hq hrec hP8
  rcases hcases with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩
  · rw [h2] at hS7
    norm_num at hS7
  · left
    rw [h2] at h1
    omega
  · right
    rw [h2] at h1
    omega

theorem exists_t (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) (hY : YData S K₁ W₂ U h Y) :
    ∃ t ∈ Nh S h, t ∉ Wsub S U ∧ t * t = 1 ∧ t * u * t⁻¹ = u * z ∧ t * h * t⁻¹ = h⁻¹ := by
  obtain ⟨t₀, ht₀P, ht₀sq, ht₀u⟩ := hs.exists_t₀ hII hq hk
  have ht₀S : t₀ ∈ S := ht₀P.1
  obtain ⟨y, hy, d, hd, hyd⟩ := hY.decomp t₀ ht₀S
  have hdW : d ∉ Wsub S U := by
    intro hdW
    apply hs.t₀_not_mem_W hII ht₀S ht₀u
    rw [hyd]
    exact mul_mem (hY.le_W hy) hdW
  have hyd2 : d * d = 1 := by
    have h1 : d * d = (y * (d * y * d⁻¹))⁻¹ := by
      calc d * d = (y * (d * y * d⁻¹))⁻¹ * ((y * d) * (y * d)) := by group
        _ = (y * (d * y * d⁻¹))⁻¹ := by rw [← hyd, ht₀sq, mul_one]
    have h2 : d * d ∈ Y := by
      rw [h1]
      exact inv_mem (mul_mem hy (hY.norm_D d hd y hy))
    have h3 : d * d ∈ Y ⊓ Nh S h := Subgroup.mem_inf.2 ⟨h2, mul_mem hd hd⟩
    rw [hY.Y_inf_Nh hII hs, Subgroup.mem_bot] at h3
    exact h3
  exact ⟨d, hd, hdW, hyd2, by
    have := hs.conj_u_of_not_mem_W hII hd.1 hdW
    exact this, hs.Nh_not_W_inv hII hd hdW⟩

theorem card_Nh_eq_two_mul (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t : G}
    (ht : t ∈ Nh S h) (htW : t ∉ Wsub S U) :
    Nat.card ↥(Nh S h) = 2 * Nat.card ↥(Nh S h ⊓ Wsub S U) := by
  have hle : Nh S h ⊓ Wsub S U ≤ Nh S h := inf_le_left
  have h2 : (Nh S h ⊓ Wsub S U).relIndex (Nh S h) = 2 := by
    refine Basic.relIndex_eq_two_of_mul (s₀ := t) ht (fun h' => htW h'.2) ?_
    intro b hb hbn
    have hbW : b ∉ Wsub S U := fun h' => hbn (Subgroup.mem_inf.2 ⟨hb, h'⟩)
    exact Subgroup.mem_inf.2 ⟨mul_mem hb ht, hs.not_mem_W_mul hII hb.1 ht.1 hbW htW⟩
  have h1 := Basic.card_mul_relIndex_of_le hle
  rw [h2] at h1
  omega

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
