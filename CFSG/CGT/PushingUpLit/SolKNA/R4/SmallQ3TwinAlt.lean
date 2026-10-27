module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinBase
public import CFSG.ClassicalInvolution.Q3.TA3Twin3Alt

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution Equiv Equiv.Perm
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.TA3.Twin3
open CFSG.OddStandard.Solomon75.AhatData
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {n : ℕ}

theorem false_of_alt_q8 (hd : TightDatum R S t) (hq : Q8Emb R t)
    (hH : TwinFr.TwinHyp (genFittingFStar Y) R S t) (h8 : 8 ≤ n) (h11 : n ≤ 11)
    (hX : GH74.GLS.IsDoubleCoverOfAlt ↥(genFittingFStar Y) n) : False := by
  set L := genFittingFStar Y
  have : L.Normal := genFittingFStar_normal Y
  obtain ⟨s, hsR, hsL, hst⟩ := exists_sq_eq_of_index_le_two_q8 hq
    (index_le_two hH.cent hX.2.1 (card_mulAut_le_of_cover hX (by omega) (by omega)))
  let C := CoverSetup.ofCover hX
  set tK : L := ⟨t, hH.mem⟩
  set sK : L := ⟨s, hsL⟩
  have hss : sK * sK = tK := Subtype.ext hst
  have htt : tK * tK = 1 := Subtype.ext (by
    have h := pow_orderOf_eq_one t
    rwa [hd.order, sq] at h)
  have htZ : tK ∉ Subgroup.center L := fun h => by
    obtain ⟨l, hl, hlt⟩ := hH.not_central
    exact hlt (congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨l, hl⟩))
  have hτ2 : C.ρ tK * C.ρ tK = 1 := by rw [← map_mul, htt, map_one]
  have hτ : IsoI (C.ρ tK) := by
    rcases support_card_of_involution h11 hτ2 (fun h => htZ (C.ρ_eq_one_iff.1 h))
      (C.sign_ρ tK) with h4 | h8'
    · exact absurd htt (C.dblI_sq_ne_one h8 ⟨hτ2, h4⟩)
    · exact ⟨hτ2, h8'⟩
  obtain ⟨ι, hι⟩ := exists_embedding h11 (by rw [← map_mul, hss]) hτ (C.sign_ρ sK)
  have hI : ∀ z : L, IsoI (C.ρ z) → z * z = 1 := fun z hz =>
    C.isoI_sq_eq_one h8 h11 (exists_e8 ι) hz
  have hcen : ∀ a b : L, C.ρ a * C.ρ b = C.ρ b * C.ρ a → ∀ g : L, g * ⁅a, b⁆ = ⁅a, b⁆ * g := by
    intro a b hab g
    have h : ⁅a, b⁆ ∈ Subgroup.center L := by
      rw [← C.ρ_eq_one_iff, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        hab]
      group
    exact Subgroup.mem_center_iff.1 h g
  obtain ⟨x, hx⟩ := C.exists_ρ_eq (isoI_via ι fpf8_x₀).sign_eq_one
  obtain ⟨u, hu⟩ := C.exists_ρ_eq (dblI_via ι u₀_facts).sign_eq_one
  set w := u⁻¹ * sK with hwdef
  have hw : C.ρ w = via ι (u₀ * γ₀) := by
    rw [hwdef, map_mul, map_inv, hu, ← hι, ← map_inv, ← map_mul, u₀_inv]
  have hτ' : C.ρ tK = via ι (γ₀ * γ₀) := by rw [← hss, map_mul, ← hι, map_mul]
  have hxx : x * x = 1 := hI x (hx ▸ isoI_via ι fpf8_x₀)
  have hxt : ⁅x, tK⁆ = 1 := by
    have hxt2 : (x * tK) * (x * tK) = 1 :=
      hI _ (by rw [map_mul, hx, hτ', ← map_mul]; exact isoI_via ι fpf8_x₀τ₀)
    rw [commutatorElement_eq_of_central (hcen x tK (by rw [hx, hτ', ← map_mul, ← map_mul,
      x₀_comm_τ₀])), hxx, htt, hxt2]
    group
  have hxw : ⁅x, w⁆ = 1 := by
    have hww : w * w = 1 := hI w (hw ▸ isoI_via ι fpf8_w₀)
    have hxw2 : (x * w) * (x * w) = 1 :=
      hI _ (by rw [map_mul, hx, hw, ← map_mul]; exact isoI_via ι fpf8_x₀w₀)
    rw [commutatorElement_eq_of_central (hcen x w (by rw [hx, hw, ← map_mul, ← map_mul,
      x₀_comm_w₀])), hxx, hww, hxw2]
    group
  have hxu : ⁅x, u⁆ = u * u := by
    have hxu2 : (x * u) * (x * u) = 1 :=
      hI _ (by rw [map_mul, hx, hu, ← map_mul]; exact isoI_via ι fpf8_x₀u₀)
    rw [commutatorElement_eq_of_central (hcen x u (by rw [hx, hu, ← map_mul, ← map_mul,
      x₀_comm_u₀])), hxx, hxu2]
    group
  have hud : DblI (C.ρ u) := hu ▸ dblI_via ι u₀_facts
  have hz := C.sq_mem_center hud.1
  have hxs : ⁅x, sK⁆ = u * u := by
    rw [show sK = u * w by rw [hwdef, mul_inv_cancel_left], commutatorElement_mul_of_eq_one hxw,
      hxu]
  exact false_of_commutator_eq hH hz (C.dblI_sq_ne_one h8 hud) (C.sq_of_mem_center hz) hsR
    (commutatorElement_eq_one_iff_mul_comm.1 hxt) hxs


end CFSG.CGT.PushingUpLit.SolKNA.R4
