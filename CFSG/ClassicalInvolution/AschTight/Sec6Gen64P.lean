module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64O

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

theorem dihedral_inv_conj {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1) :
    (a * b)⁻¹ * b * (a * b) = a * (a * b) ^ 3 := by
  have h1 := dihedral_zpow_mul ha hb (-1)
  rw [neg_neg, zpow_one, zpow_neg_one] at h1
  have hb' : b = a * (a * b) := by rw [← mul_assoc, ha, one_mul]
  calc (a * b)⁻¹ * b * (a * b) = (a * b)⁻¹ * (a * (a * b)) * (a * b) := by rw [← hb']
    _ = ((a * b)⁻¹ * a) * (a * b) * (a * b) := by group
    _ = a * (a * b) * (a * b) * (a * b) := by rw [h1]
    _ = a * (a * b) ^ 3 := by rw [pow_three]; simp only [mul_assoc]

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_of_eq_sup_odd {H N P : Subgroup G} (hN : Odd (Nat.card N))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hPH : P ≤ H) (hP2 : IsPGroup 2 P)
    (hH : H = N ⊔ P) : IsSylow2In P H := by
  refine ⟨hPH, hP2, fun P' hP'H hP'2 hPP' => le_antisymm (fun p hp => ?_) hPP'⟩
  have hpH : p ∈ N ⊔ P := hH ▸ hP'H hp
  obtain ⟨o, ho, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPN hpH
  have hoP' : o ∈ P' := by
    have := P'.mul_mem hp (P'.inv_mem (hPP' hw))
    simpa using this
  have ho1 : o = 1 := eq_one_of_isPGroup_of_mem_odd hN ho
    (hP'2.to_le (Subgroup.zpowers_le.mpr hoP'))
  rw [ho1, one_mul]
  exact hw

variable {Ω : Set (Subgroup G)} {K J R T : Subgroup G} {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem RUV_sylow : IsSylow2In (R ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v)) (𝕏(K, J) ⊔ R) := by
  have hYN := d.c.Y_le_normalizer_X d.hK0 d.hJ0
  have hXe := (d.c.X_eq_oddCore_sup d.hK0 d.hJ0).2.2
  have hUVX : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ 𝕏(K, J) := sup_le d.U_le_X d.V_le_X
  refine isSylow2In_of_eq_sup_odd (oddCoreOf_odd_natCard 𝕏(K, J)) (sup_le ?_ ?_)
    (sup_le le_sup_right (hUVX.trans le_sup_left))
    (IsPGroup.to_sup_of_normal_right' d.c.hR.2.1 d.c.UV_isPGroup d.c.hRN) (le_antisymm ?_ ?_)
  · exact fun w hw => mem_normalizer_oddCore_of_mem_normalizer (hYN (d.c.R_le_Y hw))
  · exact fun w hw => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hUVX hw))
  · exact sup_le (hXe.le.trans (sup_le le_sup_left (le_sup_of_le_right le_sup_right)))
      (le_sup_of_le_right le_sup_left)
  · exact sup_le ((oddCoreOf_le_self _).trans le_sup_left)
      (sup_le le_sup_right (hUVX.trans le_sup_left))

theorem natCard_RUV : Nat.card ↥(R ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v)) =
    2 * Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers u) := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer d.c.hRN
  have hRUV : R ⊓ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) = Subgroup.zpowers u := by
    refine le_antisymm (le_trans ?_ d.c.R_inf_centralizer.le) (le_inf d.c.huR le_sup_left)
    refine inf_le_inf_left R (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    exact d.c.UV_comm w hw j d.c.j_mem_UV
  have h2 := card_sup_mul_card_inf_of_le_normalizer
    (AscL62.le_normalizer_of_commutes d.c.hUV)
  rw [d.c.U_inf_V, Subgroup.card_bot, mul_one, ← d.c.natCard_U_eq_V] at h2
  rw [hRUV, h2, d.c.natCard_R] at h1
  have hU0 : 0 < Nat.card (Subgroup.zpowers u) := Nat.card_pos
  have : Nat.card ↥(R ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v)) * Nat.card (Subgroup.zpowers u)
      = (2 * Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers u)) *
        Nat.card (Subgroup.zpowers u) := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hU0 this

variable [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]

theorem conjSub_T_le_XR (h3 : bar 𝕏(K, J) d.rho_mem_Y ^ 3 = 1) :
    conjSub (r * t)⁻¹ T ≤ 𝕏(K, J) ⊔ R := by
  have hYN := d.c.Y_le_normalizer_X d.hK0 d.hJ0
  have hρiY : (r * t)⁻¹ ∈ pairNormalizers K J z j := Subgroup.inv_mem _ d.rho_mem_Y
  have hsY : (r * t)⁻¹ * t * (r * t)⁻¹⁻¹ ∈ pairNormalizers K J z j :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hρiY d.t_mem_Y) (Subgroup.inv_mem _ hρiY)
  have hsX : r⁻¹ * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) ∈ 𝕏(K, J) := by
    rw [← bar_eq_bar_iff _ d.r_mem_Y hsY]
    have e : bar 𝕏(K, J) hsY = (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y)⁻¹ *
        bar 𝕏(K, J) d.t_mem_Y * (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y) := by
      rw [show bar 𝕏(K, J) hsY = (bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y)⁻¹ *
        bar 𝕏(K, J) d.t_mem_Y * ((bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.t_mem_Y)⁻¹)⁻¹ from rfl,
        inv_inv]
    rw [e, dihedral_inv_conj d.bar_r_sq d.bar_t_sq, ← d.bar_rho, h3, mul_one]
  have hRX : (r * t)⁻¹ * t * (r * t)⁻¹⁻¹ ∈ 𝕏(K, J) ⊔ R := by
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_right d.hr : r ∈ 𝕏(K, J) ⊔ R)
      (Subgroup.mem_sup_left hsX)
    rwa [mul_inv_cancel_left] at this
  intro w hw
  rw [mem_conjSub_iff] at hw
  have htN : Subgroup.zpowers t ≤ Subgroup.normalizer ((𝕏(K, J) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (hYN d.t_mem_Y)
  obtain ⟨x, hx, s, hs, he⟩ := exists_mul_of_mem_sup_of_le_normalizer htN (d.T_le hw)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hx' : (r * t)⁻¹ * x * (r * t)⁻¹⁻¹ ∈ 𝕏(K, J) :=
    (Subgroup.mem_normalizer_iff.mp (hYN hρiY) x).mp hx
  have e1 := map_zpow (MulAut.conj (r * t)⁻¹) t i
  simp only [MulAut.conj_apply] at e1
  have e : w = ((r * t)⁻¹ * x * (r * t)⁻¹⁻¹) * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) ^ i := by
    rw [← e1]
    calc w = (r * t)⁻¹ * ((r * t)⁻¹⁻¹ * w * (r * t)⁻¹) * (r * t)⁻¹⁻¹ := by group
      _ = (r * t)⁻¹ * (x * t ^ i) * (r * t)⁻¹⁻¹ := by rw [he]
      _ = ((r * t)⁻¹ * x * (r * t)⁻¹⁻¹) * ((r * t)⁻¹ * t ^ i * (r * t)⁻¹⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx') (Subgroup.zpow_mem _ hRX i)

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
