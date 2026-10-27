module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx43

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem exists_w (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : 2 ^ 7 ≤ Nat.card ↥S) (hY : YData S K₁ W₂ U h Y) {t : G} (ht : t ∈ Nh S h)
    (htW : t ∉ Wsub S U) :
    ∃ w : G, w ∈ Nh S h ∧ w ∈ Wsub S U ∧ Nh S h ⊓ Wsub S U = zpowers w ∧
      (w = 1 ∨ (w ≠ 1 ∧ w * w = 1 ∧ Nat.card ↥(Nh S h) = 4)) := by
  have hcard := hs.card_Nh_eq_two_mul hII ht htW
  rcases hs.card_Nh_cases hII hq hrec hP8 hS7 hY with h2 | h4
  · have h1 : Nat.card ↥(Nh S h ⊓ Wsub S U) = 1 := by omega
    have hbot : Nh S h ⊓ Wsub S U = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact ⟨1, one_mem _, one_mem _, by rw [hbot, Subgroup.zpowers_one_eq_bot], Or.inl rfl⟩
  · have h2 : Nat.card ↥(Nh S h ⊓ Wsub S U) = 2 := by omega
    have hne : Nh S h ⊓ Wsub S U ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at h2
      omega
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
    have hwo : 2 ≤ orderOf w := by
      have h0 : 0 < orderOf w := orderOf_pos w
      have h1 : orderOf w ≠ 1 := fun h' => hw1' (orderOf_eq_one_iff.1 h')
      omega
    have heq : zpowers w = Nh S h ⊓ Wsub S U := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hw)
      rw [Nat.card_zpowers, h2]
      exact hwo
    have hw2 : w * w = 1 := by
      have := Basic.pow_card_of_mem hw
      rw [h2, pow_two] at this
      exact this
    exact ⟨w, hw.1, hw.2, heq.symm, Or.inr ⟨hw1', hw2, h4⟩⟩

theorem t_comm_w (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t w : G}
    (ht : t ∈ Nh S h) (hwD : w ∈ Nh S h) (hwW : w ∈ Wsub S U)
    (hD₀ : Nh S h ⊓ Wsub S U = zpowers w) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    t * w = w * t := by
  have hmem : t * w * t⁻¹ ∈ Nh S h ⊓ Wsub S U :=
    Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hwD) (inv_mem ht), hs.W_normS ht.1 hwW⟩
  rw [hD₀, Basic.mem_zpowers_of_sq' hw2] at hmem
  rcases hmem with h1 | h1
  · exfalso
    apply hw1
    have : w = t⁻¹ * (t * w * t⁻¹) * t := by group
    rw [this, h1]
    group
  · calc t * w = (t * w * t⁻¹) * t := by group
      _ = w * t := by rw [h1]

theorem Nh_eq_sup (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t w : G}
    (ht : t ∈ Nh S h) (htW : t ∉ Wsub S U) (hwD : w ∈ Nh S h)
    (hD₀ : Nh S h ⊓ Wsub S U = zpowers w) : Nh S h = zpowers t ⊔ zpowers w := by
  apply le_antisymm
  · intro d hd
    by_cases hdW : d ∈ Wsub S U
    · have : d ∈ Nh S h ⊓ Wsub S U := Subgroup.mem_inf.2 ⟨hd, hdW⟩
      rw [hD₀] at this
      exact Subgroup.mem_sup_right this
    · have htinv : t⁻¹ ∉ Wsub S U := fun h' => htW (by simpa using inv_mem h')
      have h1 : t⁻¹ * d ∈ Wsub S U := hs.not_mem_W_mul hII (inv_mem ht.1) hd.1 htinv hdW
      have h2 : t⁻¹ * d ∈ Nh S h ⊓ Wsub S U := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ht) hd, h1⟩
      rw [hD₀] at h2
      have : d = t * (t⁻¹ * d) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)) (Subgroup.mem_sup_right h2)
  · exact sup_le (zpowers_le.2 ht) (zpowers_le.2 hwD)

theorem Nh_inf_centralizer (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Nh S h ⊓ centralizer (U : Set G) = Nh S h ⊓ Wsub S U := by
  ext d
  constructor
  · intro hd
    exact Subgroup.mem_inf.2 ⟨hd.1, Subgroup.mem_inf.2 ⟨hd.1.1, hd.2⟩⟩
  · intro hd
    exact Subgroup.mem_inf.2 ⟨hd.1, hd.2.2⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
