module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx44

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

structure Cfg88 {G : Type} [Group G] (z : G) (S K₁ W₂ U : Subgroup G) (u h : G) (Y : Subgroup G)
    (t w : G) : Prop where
  hY : YData S K₁ W₂ U h Y
  htD : t ∈ Nh S h
  htW : t ∉ Wsub S U
  ht2 : t * t = 1
  htu : t * u * t⁻¹ = u * z
  hth : t * h * t⁻¹ = h⁻¹
  htP : t ∈ Pz S z
  hwD : w ∈ Nh S h
  hwW : w ∈ Wsub S U
  hw1 : w ≠ 1
  hw2 : w * w = 1
  hwh : w * h = h * w
  htw : t * w = w * t
  hD₀ : Nh S h ⊓ Wsub S U = zpowers w
  hDeq : Nh S h = zpowers t ⊔ zpowers w
  hD4 : Nat.card ↥(Nh S h) = 4
  hS256 : Nat.card ↥S = 2 ^ 8
  hinvA : ∀ x ∈ Aof S K₁ W₂ h, w * x * w⁻¹ = x⁻¹

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y D E₁ E₂ : Subgroup G} {t w : G}

theorem YData_of_concl86 (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hC : Concl86 z S K₁ W₂ U u h Y D t w) (hE : EData Y U E₁ E₂) :
    D = Nh S h ∧ YData S K₁ W₂ U h Y := by
  have hD : D = Nh S h := hC.2.2.2.1.2.2
  have hDS : D ≤ S := hD ▸ Nh_le_S
  have hNN : S ⊔ zpowers h ≤ normalizer (Y : Set G) :=
    normedBy_iff_le_normalizer.1 hC.2.2.1.2.2.1
  have hSN : S ≤ normalizer (Y : Set G) := le_sup_left.trans hNN
  refine ⟨hD, ⟨hC.2.2.1.1, Y_le_W hE hC, card_Y hs hE, Y_norm_h_inv hC, hC.2.2.1.2.2.2.2, ?_, ?_⟩⟩
  · intro s hsS
    have hs' : s ∈ Y ⊔ D := by
      rw [← hC.2.1]
      exact hsS
    obtain ⟨d, hd, y', hy', hsd⟩ := Basic.mem_sup_of_le_normalizer' (A := D) (B := Y)
      (fun d hd => hSN (hDS hd)) (sup_comm Y D ▸ hs')
    have hyd : d * y' * d⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.1 (hSN (hDS hd)) y').1 hy'
    refine ⟨d * y' * d⁻¹, hyd, d, hD ▸ hd, ?_⟩
    rw [hsd]
    group
  · intro d hd y hy
    have hdS : d ∈ S := Nh_le_S hd
    exact (Subgroup.mem_normalizer_iff.1 (hSN hdS) y).1 hy

theorem cfg88 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : 2 ^ 7 ≤ Nat.card ↥S) (hC : Concl86 z S K₁ W₂ U u h Y D t w) (hE : EData Y U E₁ E₂)
    (hw1 : w ≠ 1) : Cfg88 z S K₁ W₂ U u h Y t w := by
  obtain ⟨hD, hY⟩ := hs.YData_of_concl86 hC hE
  subst hD
  obtain ⟨htP, hto, htu', hth'⟩ := hC.2.2.2.2.1
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hto
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htu : t * u * t⁻¹ = u * z := by rw [ht'] at htu' ⊢; exact htu'
  have hth : t * h * t⁻¹ = h⁻¹ := by rw [ht'] at hth' ⊢; exact hth'
  have hDeq : Nh S h = zpowers t ⊔ zpowers w := hC.2.2.2.1.1
  have htD : t ∈ Nh S h := hDeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hwD : w ∈ Nh S h := hDeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwcent : Nh S h ⊓ centralizer (U : Set G) = zpowers w := hC.2.2.2.2.2.1.1
  have hw' : w ∈ Nh S h ⊓ centralizer (U : Set G) := hwcent ▸ Subgroup.mem_zpowers w
  have hwW : w ∈ Wsub S U := Subgroup.mem_inf.2 ⟨Nh_le_S hwD, hw'.2⟩
  have htW : t ∉ Wsub S U := hs.t₀_not_mem_W hII (Nh_le_S htD) htu
  have hD₀ : Nh S h ⊓ Wsub S U = zpowers w := (hs.Nh_inf_centralizer.symm).trans hwcent
  have hcard := hs.card_Nh_eq_two_mul hII htD htW
  have hcases := hs.card_Nh_cases hII hq hrec hP8 hS7 hY
  have hwo : 2 ≤ orderOf w := by
    have h0 : 0 < orderOf w := orderOf_pos w
    have h1 : orderOf w ≠ 1 := fun h' => hw1 (orderOf_eq_one_iff.1 h')
    omega
  have hz0 : Nat.card ↥(Nh S h ⊓ Wsub S U) = orderOf w := by rw [hD₀, Nat.card_zpowers]
  have hD4 : Nat.card ↥(Nh S h) = 4 := by omega
  have hw2o : orderOf w = 2 := by omega
  have hw2 : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw2o
  have hS256 : Nat.card ↥S = 2 ^ 8 := by
    have := hY.card_S hII hs
    rw [hD4] at this
    omega
  have hinvA : ∀ x ∈ Aof S K₁ W₂ h, w * x * w⁻¹ = x⁻¹ := by
    rcases hC.2.2.2.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hw1
    · exact h1
  have hwh : w * h = h * w := hC.2.2.2.2.2.1.2
  exact ⟨hY, htD, htW, ht2, htu, hth, htP, hwD, hwW, hw1, hw2, hwh,
    hs.t_comm_w hII htD hwD hwW hD₀ hw1 hw2, hD₀, hDeq, hD4, hS256, hinvA⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
