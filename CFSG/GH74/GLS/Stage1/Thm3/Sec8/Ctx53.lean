module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx50
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx46

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G} {t w : G}

theorem Nh_comm_w (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : ∀ d ∈ Nh S h, d * w = w * d := by
  have hle : Nh S h ≤ centralizer ({w} : Set G) := by
    rw [cfg.hDeq]
    apply sup_le
    · rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact cfg.htw
    · rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)

theorem cent_Y_w (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) (hcentral : ∀ y ∈ Y, ∀ c ∈ U, y * c = c * y)
    (hC32 : Nat.card ↥(S ⊓ centralizer ({w} : Set G)) ≤ 32) :
    Y ⊓ centralizer ({w} : Set G) = U := by
  have hY := cfg.hY
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk
  have hUY : U ≤ Y := hUA.trans hY.A_le
  have hUw : ∀ c ∈ U, c * w = w * c := fun c hc => by
    have := hs.W_cent_U cfg.hwW hc
    calc c * w = (w * c * w⁻¹) * w := by rw [this]
      _ = w * c := by group
  have hUC : U ≤ Y ⊓ centralizer ({w} : Set G) := fun c hc =>
    Subgroup.mem_inf.2 ⟨hUY hc, Subgroup.mem_centralizer_singleton_iff.2 (hUw c hc)⟩
  set A := Y ⊓ centralizer ({w} : Set G) with hA
  have hDc := Nh_comm_w cfg
  have hDN : Nh S h ≤ normalizer (A : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ d ∈ Nh S h, ∀ y ∈ A, d * y * d⁻¹ ∈ A := by
      intro d hd y hy
      refine Subgroup.mem_inf.2 ⟨hY.norm_D d hd y hy.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hyw : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
      have hdw : d * w = w * d := hDc d hd
      have hdw' : d⁻¹ * w = w * d⁻¹ := hDc d⁻¹ (inv_mem hd)
      calc d * y * d⁻¹ * w = d * y * (d⁻¹ * w) := by group
        _ = d * y * (w * d⁻¹) := by rw [hdw']
        _ = d * (y * w) * d⁻¹ := by group
        _ = d * (w * y) * d⁻¹ := by rw [hyw]
        _ = (d * w) * y * d⁻¹ := by group
        _ = (w * d) * y * d⁻¹ := by rw [hdw]
        _ = w * (d * y * d⁻¹) := by group
    intro y
    constructor
    · intro hy
      exact key d hd y hy
    · intro hy
      have h1 := key d⁻¹ (inv_mem hd) _ hy
      have e : d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y := by group
      rwa [e] at h1
  have hcard := Basic.card_sup_mul_card_inf' (A := A) (B := Nh S h) hDN
  have hinf : A ⊓ Nh S h = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Y ⊓ Nh S h := Subgroup.mem_inf.2 ⟨hx.1.1, hx.2⟩
    rw [hY.Y_inf_Nh hII hs, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  rw [hinf, Subgroup.card_bot, mul_one, cfg.hD4] at hcard
  have hsup : A ⊔ Nh S h ≤ S ⊓ centralizer ({w} : Set G) := by
    apply sup_le
    · intro x hx
      exact Subgroup.mem_inf.2 ⟨hY.Y_le_S hx.1, hx.2⟩
    · intro d hd
      exact Subgroup.mem_inf.2 ⟨Nh_le_S hd, Subgroup.mem_centralizer_singleton_iff.2 (hDc d hd)⟩
  have h8 : Nat.card ↥A ≤ 8 := by
    have := Subgroup.card_le_of_le hsup
    omega
  have hU4 := hs.U_four.2
  have hrel : U.relIndex A ≤ 2 := by
    have h1 := Basic.card_mul_relIndex_of_le hUC
    have hpos : 0 < Nat.card ↥U := Nat.card_pos
    by_contra hcon
    have : Nat.card ↥U * 3 ≤ Nat.card ↥U * U.relIndex A := Nat.mul_le_mul_left _ (by omega)
    omega
  refine le_antisymm ?_ hUC
  intro y hyA
  by_contra hyU
  have hrel2 : U.relIndex A = 2 := by
    have hne : U.relIndex A ≠ 1 := by
      intro h1
      exact hyU (Subgroup.relIndex_eq_one.1 h1 hyA)
    have hpos : U.relIndex A ≠ 0 := Basic.relIndex_ne_zero' _ _
    omega
  have hyh : h⁻¹ * y * h ∈ A := by
    refine Subgroup.mem_inf.2 ⟨hY.conj_h y hyA.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hyw : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.1 hyA.2
    calc h⁻¹ * y * h * w = h⁻¹ * y * (h * w) := by group
      _ = h⁻¹ * y * (w * h) := by rw [cfg.hwh]
      _ = h⁻¹ * (y * w) * h := by group
      _ = h⁻¹ * (w * y) * h := by rw [hyw]
      _ = (h⁻¹ * w) * y * h := by group
      _ = (w * h⁻¹) * y * h := by
          have : h⁻¹ * w = w * h⁻¹ := by
            calc h⁻¹ * w = h⁻¹ * (w * h) * h⁻¹ := by group
              _ = h⁻¹ * (h * w) * h⁻¹ := by rw [cfg.hwh]
              _ = w * h⁻¹ := by group
          rw [this]
      _ = w * (h⁻¹ * y * h) := by group
  have hyhU : h⁻¹ * y * h ∉ U := by
    intro hmem
    apply hyU
    have h1 : h * (h⁻¹ * y * h) * h⁻¹ ∈ U :=
      ((Subgroup.mem_normalizer_iff.1 hs.h_norm) _).1 hmem
    have e : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rwa [e] at h1
  have h3 := Basic.mul_inv_mem_of_relIndex_two hrel2 hyh hyA hyhU hyU
  exact hyU (hs.fpf_mod_U hII hq hrec hk hY hcentral hyA.1 h3)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
