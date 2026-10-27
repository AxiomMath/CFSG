module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx54
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx52
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic15
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic17
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx53
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic13

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y E₁ E₂ : Subgroup G} {t w : G}

theorem cent_Y_yw (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) (hUY : U ≤ Y) (hcentral : ∀ y ∈ Y, ∀ c ∈ U, y * c = c * y)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U) (hsq : ∀ a ∈ Y, a * a ∈ U)
    (hCw : Y ⊓ centralizer ({w} : Set G) = U) :
    ∀ y ∈ Y, orderOf (y * w) = 2 → Y ⊓ centralizer ({y * w} : Set G) = U := by
  intro y hy hord
  have hY := cfg.hY
  have hwS : w ∈ S := Nh_le_S cfg.hwD
  have hSN : S ≤ normalizer (Y : Set G) := hY.S_le_normalizer
  have hsq1 : (y * w) * (y * w) = 1 := mul_self_eq_one_of_orderOf_eq_two hord
  have hwU := hs.w_comm_U cfg
  obtain ⟨m, hm, hmem⟩ := Basic.exists_conj_into_U hUY (fun c hc y hy => (hcentral y hy c hc).symm)
    hcomm hsq hY.card hs.U_four.2
    (fun y hy => (Subgroup.mem_normalizer_iff.1 (hSN hwS) y).1 hy) cfg.hw2
    (fun c hc => by
      have := hs.W_cent_U cfg.hwW hc
      exact this)
    (fun y hy hc => by
      rw [← hCw]
      exact Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 hc.symm⟩) y hy hsq1
  obtain ⟨c, hcU, w', hw', hcw⟩ := Set.mem_mul.1 hmem
  have hw'w : w' = w := hw'
  subst hw'w
  apply le_antisymm
  · intro g hg
    have hgY : g ∈ Y := hg.1
    have hgc : g * (y * w') = (y * w') * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
    have hg'Y : m * g * m⁻¹ ∈ Y := mul_mem (mul_mem hm hgY) (inv_mem hm)
    have hcomm' : (m * g * m⁻¹) * (c * w') = (c * w') * (m * g * m⁻¹) := by
      rw [hcw]
      calc (m * g * m⁻¹) * (m * (y * w') * m⁻¹) = m * (g * (y * w')) * m⁻¹ := by group
        _ = m * ((y * w') * g) * m⁻¹ := by rw [hgc]
        _ = (m * (y * w') * m⁻¹) * (m * g * m⁻¹) := by group
    have hcc : (m * g * m⁻¹) * c = c * (m * g * m⁻¹) := hcentral _ hg'Y c hcU
    have hgw : (m * g * m⁻¹) * w' = w' * (m * g * m⁻¹) := by
      have h1 : c * ((m * g * m⁻¹) * w') = c * (w' * (m * g * m⁻¹)) := by
        calc c * ((m * g * m⁻¹) * w') = (c * (m * g * m⁻¹)) * w' := by group
          _ = ((m * g * m⁻¹) * c) * w' := by rw [hcc]
          _ = (m * g * m⁻¹) * (c * w') := by group
          _ = (c * w') * (m * g * m⁻¹) := hcomm'
          _ = c * (w' * (m * g * m⁻¹)) := by group
      exact mul_left_cancel h1
    have hg'U : m * g * m⁻¹ ∈ U := by
      rw [← hCw]
      exact Subgroup.mem_inf.2 ⟨hg'Y, Subgroup.mem_centralizer_singleton_iff.2 hgw⟩
    have hmg : m⁻¹ * (m * g * m⁻¹) * m = m * g * m⁻¹ := by
      have h2 := hcentral m hm _ hg'U
      calc m⁻¹ * (m * g * m⁻¹) * m = m⁻¹ * ((m * g * m⁻¹) * m) := by group
        _ = m⁻¹ * (m * (m * g * m⁻¹)) := by rw [← h2]
        _ = m * g * m⁻¹ := by group
    have : g = m⁻¹ * (m * g * m⁻¹) * m := by group
    rw [this, hmg]
    exact hg'U
  · intro c' hc'
    refine Subgroup.mem_inf.2 ⟨hUY hc', Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : y * c' = c' * y := hcentral y hy c' hc'
    have h2 : w' * c' = c' * w' := hwU c' hc'
    calc c' * (y * w') = (c' * y) * w' := by group
      _ = (y * c') * w' := by rw [h1]
      _ = y * (c' * w') := by group
      _ = y * (w' * c') := by rw [h2]
      _ = (y * w') * c' := by group

end Setup8

theorem lemma_8_8 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
      (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → 2 ^ 7 ≤ Nat.card ↥S →
        Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ → w ≠ 1 →
          (∀ y ∈ Y, orderOf (y * w) = 2 → Y ⊓ centralizer ({y * w} : Set G) = U) ∧
          conjugate E₁ w = E₂ := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE hw1
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have cfg := hs.cfg88 hII hq hrec hP8 hS7 hC hE hw1
  obtain ⟨eY⟩ := hC.2.2.1.2.2.2.1
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk
  have hUY : U ≤ Y := hUA.trans cfg.hY.A_le
  have hUN : ∀ y ∈ Y, ∀ c ∈ U, y * c * y⁻¹ ∈ U := fun y hy c hc =>
    hs.U_norm y (cfg.hY.Y_le_S hy) c hc
  obtain ⟨hcomm, hcentral⟩ := Basic.comm_central_of_equiv eY hUY hs.U_four.2 hUN
  have hsq : ∀ a ∈ Y, a * a ∈ U := Basic.sq_mem_of_equiv eY hUY hs.U_four.2 hUN
  have hCw := hs.cent_Y_w hII hq hrec hk cfg hcentral (hs.card_cent_w_le32 hII hq hrec hP8 cfg)
  exact ⟨hs.cent_Y_yw hII cfg hUY hcentral hcomm hsq hCw,
    hs.conj_E₁_w hII hq hk cfg hE hcentral hCw⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
