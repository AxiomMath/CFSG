module

public import CFSG.LargeExtraspecial.S11MbKeyB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G} {kb σ u₁ : G}

theorem YData.z_not_mem (Y : YData S g t τ u kb σ u₁) : S.z ∉ S.Qa u₁ := by
  intro hz
  apply Y.not_mem_QG
  have hne : (1 : G) * S.z * (1 : G)⁻¹ ≠ u₁ * S.z * u₁⁻¹ := by
    rw [one_mul, inv_one, mul_one, ← Y.conj_eq]
    intro h
    exact Y.not_mem_QG (h ▸ S.z_mem_QG)
  have h1 := S.mem_Qa_symm hne (by rw [one_mul, inv_one, mul_one]; exact hz)
  rw [S.Qa_one, ← Y.conj_eq] at h1
  exact h1

theorem YData.card_inf (hy : Hyp S g) (Y : YData S g t τ u kb σ u₁) :
    Nat.card (S.Qa u₁ ⊓ S.Qa g ⊓ S.M : Subgroup G) = 2 ^ S.width := by
  have hk := inv_mul_conj_z (S := S) u₁ g
  have hkQ : (u₁⁻¹ * g) * S.z * (u₁⁻¹ * g)⁻¹ ∈ S.QG := by
    rw [hk]
    exact (mem_Qa_iff S u₁ _).mp Y.a_mem
  have hkz : (u₁⁻¹ * g) * S.z * (u₁⁻¹ * g)⁻¹ ≠ S.z := by
    rw [hk]
    intro h
    apply Y.not_mem_QG
    have e : g * S.z * g⁻¹ = u₁ * S.z * u₁⁻¹ := by
      calc g * S.z * g⁻¹ = u₁ * (u₁⁻¹ * (g * S.z * g⁻¹) * u₁) * u₁⁻¹ := by group
        _ = u₁ * S.z * u₁⁻¹ := by rw [h]
    rw [Y.conj_eq, ← e]
    exact hy.hyp4.conj_mem
  have hzM : u₁⁻¹ * S.z * u₁ ∈ S.M := by
    rw [S.mem_M_iff]
    have h1 : σ * S.z = S.z * σ := S.z_comm Y.mem_M
    rw [Y.conj_eq] at h1
    calc u₁⁻¹ * S.z * u₁ * S.z = u₁⁻¹ * (S.z * (u₁ * S.z * u₁⁻¹)) * u₁ := by group
      _ = u₁⁻¹ * ((u₁ * S.z * u₁⁻¹) * S.z) * u₁ := by rw [h1]
      _ = S.z * (u₁⁻¹ * S.z * u₁) := by group
  have hyL : u₁⁻¹ * S.z * u₁ ∈ S.L0 (u₁⁻¹ * g) :=
    ⟨conj_mem_Qa_inv_mul (S.z_mem_Qa hy.hyp4.conj_mem hy.hyp4.conj_ne), hzM⟩
  have hyQ : u₁⁻¹ * S.z * u₁ ∉ S.QG := fun h => Y.z_not_mem ((mem_Qa_iff S u₁ S.z).mpr h)
  have h1 := hy.card_inf_centralizer hkQ hkz hyL hyQ
  rw [← map_conj_inf_centralizer (S := S) u₁ g,
    Subgroup.card_map_of_injective (MulAut.conj u₁).injective]
  exact h1

theorem map_le_Lbar (u₁ : G) :
    ((S.Qa u₁ ⊓ S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ ≤ S.Lbar g := by
  refine Subgroup.map_mono fun x hx => ?_
  rw [mem_subgroupOf] at hx ⊢
  exact ⟨(mem_inf.mp (mem_inf.mp hx).1).2, (mem_inf.mp hx).2⟩

variable (hy : Hyp S g) (K : Conf S g t τ u) (hm : finrank (ZMod 2) (Vt S g t) = 2)
  (Y : YData S g t τ u kb σ u₁)
  (hcase : ∀ w ∈ Wt S g t, (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
    (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
include hy K hm hcase

theorem YData.two_pow_le_card :
    2 ^ S.width ≤ 8 * Nat.card (((S.Qa u₁ ⊓ S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ ⊓
      (S.Lbar g ⊓ Nbar S g t) : Subgroup S.O) := by
  set X := S.Qa u₁ ⊓ S.Qa g ⊓ S.M with hX
  have h1 := card_eq_card_map_mul (S := S) (X := X) inf_le_right
  rw [card_ker_inf_eq inf_le_right, Y.card_inf hy] at h1
  have h2 : Nat.card (S.QG ⊓ X : Subgroup G) ≤ Nat.card (S.QG ⊓ S.Qa u₁ : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_left _ (inf_le_left.trans inf_le_left))
  have h3 : Nat.card (S.QG ⊓ S.Qa u₁ : Subgroup G) =
      2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u₁)) := by
    rw [card_eq_card_clSub inf_le_left fun h => Y.z_not_mem (mem_inf.mp h).2,
      S.card_submodule]
  have h4 := Y.finrank_clSub_le_two hy K hm hcase
  have h5 : Nat.card (S.QG ⊓ X : Subgroup G) ≤ 4 := by
    rw [h3] at h2
    exact h2.trans (by
      calc 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u₁)) ≤ 2 ^ 2 :=
            Nat.pow_le_pow_right (by norm_num) h4
        _ = 4 := by norm_num)
  have h6 := card_Lbar_inf_Nbar hy.hyp4 hy.cons K.lin
  rw [hm] at h6
  have h7 := hy.cons.card_Lbar
  have hN : Nat.card (S.Lbar g) ≤ 2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    rw [h7, ← h6]
    norm_num
    rw [mul_comm]
  have h8 := card_le_two_mul_card_inf (map_le_Lbar u₁) inf_le_left hN
  rw [← hX] at h8
  calc 2 ^ S.width = Nat.card ((X.subgroupOf S.M).map S.ρ) * Nat.card (S.QG ⊓ X : Subgroup G) :=
        h1
    _ ≤ Nat.card ((X.subgroupOf S.M).map S.ρ) * 4 := Nat.mul_le_mul_left _ h5
    _ ≤ 2 * Nat.card ((X.subgroupOf S.M).map S.ρ ⊓ (S.Lbar g ⊓ Nbar S g t) : Subgroup S.O) * 4 :=
        Nat.mul_le_mul_right _ h8
    _ = 8 * Nat.card ((X.subgroupOf S.M).map S.ρ ⊓ (S.Lbar g ⊓ Nbar S g t) : Subgroup S.O) := by
        ring

end CFSG.LargeExtraspecial.S11
