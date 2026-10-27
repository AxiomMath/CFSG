module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YElemBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YElemG
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Dichotomy

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

namespace YElem

variable {G : Type} [Group G] [Finite G] {L U T0 : Subgroup G} {z : G}

theorem Y_sq_core (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u)
    (hW : Nat.card (Csub U z) = 2 ^ 23) (hL : LiftData L U) {Y : Subgroup G}
    (hY : YStruct L U z Y) (hab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) :
    ∀ y ∈ Y, y * y = 1 := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have : IsAbelianSub Y := ⟨hab⟩
  let ψ : Y →* G := (phiHom hS hD).comp (Subgroup.inclusion hY.le_W)
  let Ω : Subgroup G := omegaSub Y hab
  let D : Subgroup G := (Ω.subgroupOf Y).map ψ
  have hDU : D ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact phiVal_mem hS hD (mem_Csub.1 (hY.le_W y.2)).1
  have hDinv : ∀ h ∈ Hloc L U, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    rintro h hh _ ⟨y, hy, rfl⟩
    obtain ⟨hyY, hy2⟩ := mem_omegaSub.1 (mem_subgroupOf.1 hy)
    have hhY : h * y * h⁻¹ ∈ Y := hY.H_inv h hh y hyY
    refine ⟨⟨h * y * h⁻¹, hhY⟩, mem_subgroupOf.2 (mem_omegaSub.2 ⟨hhY, ?_⟩),
      (phiVal_conj hS hD hh (hY.le_W hyY)).2⟩
    calc h * y * h⁻¹ * (h * y * h⁻¹)
        = h * (y * y) * h⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [hy2, mul_one, mul_inv_cancel]
  rcases hD.irred D hDU hDinv with hbot | htop
  · exfalso
    have hΩU : ∀ y ∈ Y, y * y = 1 → y ∈ U := by
      intro y hy hy2
      have : ψ ⟨y, hy⟩ ∈ D := ⟨⟨y, hy⟩, mem_subgroupOf.2 (mem_omegaSub.2 ⟨hy, hy2⟩), rfl⟩
      rw [hbot] at this
      exact mem_U_of_phiVal_eq_one hS hD hY hy (mem_bot.1 this)
    obtain ⟨e, s, t, heU, hinj, hsH, htH, hss, htt, hst, hse, hte⟩ := hL
    exact false_of_abelian_subgroup Y U hY.U_le (phiVal z)
      (fun y hy y' hy' => phiVal_mul hS hD (hY.le_W hy) (hY.le_W hy'))
      (fun y hy => phiVal_mem hS hD (mem_Csub.1 (hY.le_W hy)).1)
      (fun u hu => (phiVal_eq_one_iff hS).2 (z_comm_U hS hUL hu))
      (fun y hy h1 => mem_U_of_phiVal_eq_one hS hD hY hy h1)
      (fun u hu => exists_phiVal_eq hS hD hY hW hu) hD.U_sq
      (fun y hy => sq_mem_U hS hD htrans (hY.le_W hy)) hΩU hD.card_U e heU hinj s t
      (fun y hy => hY.H_inv s hsH y hy) (fun y hy => hY.H_inv t htH y hy) hss htt hst
      (fun y hy => (phiVal_conj hS hD hsH (hY.le_W hy)).2)
      (fun y hy => (phiVal_conj hS hD htH (hY.le_W hy)).2) hse hte
  · intro y hy
    have hyU : phiVal z y ∈ U := phiVal_mem hS hD (mem_Csub.1 (hY.le_W hy)).1
    have hyD : phiVal z y ∈ D := by rw [htop]; exact hyU
    obtain ⟨ω, hω, hωy⟩ := hyD
    have hω' : (ω : G) ∈ Ω := mem_subgroupOf.1 hω
    have h1 : ψ (ω⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, hωy]
      exact inv_mul_cancel (phiVal z y)
    have hmem : ((ω⁻¹ * ⟨y, hy⟩ : Y) : G) ∈ U :=
      mem_U_of_phiVal_eq_one hS hD hY (ω⁻¹ * ⟨y, hy⟩).2 h1
    have hmemΩ : ((ω⁻¹ * ⟨y, hy⟩ : Y) : G) ∈ Ω :=
      mem_omegaSub.2 ⟨(ω⁻¹ * ⟨y, hy⟩).2, hD.U_sq _ hmem⟩
    have hprod : (ω : G) * ((ω⁻¹ * ⟨y, hy⟩ : Y) : G) = y := by simp
    have := (mem_omegaSub.1 (Ω.mul_mem hω' hmemΩ)).2
    rwa [hprod] at this

end YElem

theorem Y_sq {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L U T0 : Subgroup G} {z p q u0 : G}
    (hS : Setting L z) (hD : LocalData L U T0) (hD11 : LocalData11 L U p q u0)
    (hM : ModData L U) {Y : Subgroup G} (hY : YStruct L U z Y)
    (hab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) : ∀ y ∈ Y, y * y = 1 :=
  YElem.Y_sq_core hS hD (trans_of_simple hnonab hS hD) (card_Csub hnonab hS hD hD11) hM.lift hY
    hab

end CFSG.EvenSporadicStandard.J4Std
