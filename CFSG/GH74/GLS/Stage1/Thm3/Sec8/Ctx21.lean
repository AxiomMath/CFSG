module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx20
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx19

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem g2shape_of_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2)
    (hSS : S = S1 S K₁) {m : ℕ} (hm : 1 ≤ m) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) :
    ∃ a t y : G, G2Shape S (Aof S K₁ W₂ h) a t y (m + 1) ∧ u ∈ zpowers a ∧ t⁻¹ * u * t = u * z := by
  have hk2 : 2 ≤ m + 1 := by omega
  obtain ⟨y₁, hy₁P, hy₁sq, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  obtain ⟨y₂, hy₂P, hy₂sq, hy₂inv, -⟩ := hs.exists_y₂ hII hq hrec hk
  have hyW : y₁ * y₂ ∈ Wsub S U := hs.y_mem_W hII hq hy₁P hy₂P hy₁inv hy₂inv
  have hyinv₁ := hs.y_inv_V₁ hII hy₂P hy₁inv
  have hyA : y₁ * y₂ ∉ Aof S K₁ W₂ h := hs.not_mem_A_of_inv hII hq hrec hyinv₁
  have hy2 : (y₁ * y₂) * (y₁ * y₂) = 1 := hs.y_sq hII hy₁P hy₂P hy₁sq hy₂sq
  have hWS : Wsub S U ⊓ S1 S K₁ = Wsub S U := inf_eq_left.2 (inf_le_left.trans hSS.le)
  have hrel : (Aof S K₁ W₂ h).relIndex (Wsub S U) = 2 := by
    have := hs.A_relIndex_W₀ hII hq hrec he hk2 hk hy₁P hy₁inv
    rwa [hWS] at this
  have hyinvA := hs.y_inv_A_of_S1 hII hq hrec hk hyW hyA hyinv₁ hrel
  have hy₁conj := hs.y₁_conj_u hII hq hy₁P hy₁inv
  have ht2 := hs.t_sq hII hy₁P.1 hy₁sq hy₁conj
  have hty := hs.t_comm_y (hs.P_comm hII y₁ hy₁P y₂ hy₂P) hyW
  have htA := hs.t_not_mem_A hII hq hrec hk2 hk hy₁conj
  have htyA := hs.ty_not_mem_A hII hq hrec hk2 hk hy₁conj hyW
  obtain ⟨a, haA, hao, hau⟩ := hs.exists_a hII hq hrec hk
  have hcardS : Nat.card ↥S = 4 * Nat.card ↥(Aof S K₁ W₂ h) := by
    have h1 : Nat.card ↥S = Nat.card ↥(S1 S K₁) := by rw [← hSS]
    rw [h1, hs.card_S1_e1 hII hq hrec he hk, hs.card_A hII hq hrec hk]
    ring
  have ht1 : (y₁ * (h⁻¹ * z * h))⁻¹ = y₁ * (h⁻¹ * z * h) := inv_eq_of_mul_eq_one_right ht2
  have htu : (y₁ * (h⁻¹ * z * h))⁻¹ * u * (y₁ * (h⁻¹ * z * h)) = u * z := by
    have h1 := hs.t_conj_u hy₁conj
    rw [ht1] at h1 ⊢
    exact h1
  have htS : y₁ * (h⁻¹ * z * h) ∈ S := mul_mem hy₁P.1 (hs.U_le_S hII hs.hz_inv_mem_U)
  have hyS : y₁ * y₂ ∈ S := hyW.1
  have hy1 : (y₁ * y₂)⁻¹ = y₁ * y₂ := inv_eq_of_mul_eq_one_right hy2
  have hyinv' : ∀ p ∈ Aof S K₁ W₂ h, (y₁ * y₂) * p * (y₁ * y₂) = p⁻¹ := by
    intro p hp
    have := hyinvA p hp
    rwa [hy1] at this
  refine ⟨a, y₁ * (h⁻¹ * z * h), y₁ * y₂, ?_, ?_, htu⟩
  · exact Basic.g2shape_abstract (hs.A_comm hII hq hrec) haA hao ht2 hy2 hty
      (fun p hp => hs.A_normS hII hq hrec htS hp) (fun p hp => hs.A_normS hII hq hrec hyS hp)
      hyinv' hau htu hs.z_ne (hs.card_A hII hq hrec hk) (hs.A_le_S hII hq hrec) hcardS htS hyS
      htA hyA htyA
  · rw [hau]
    exact Subgroup.npow_mem_zpowers a _

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
