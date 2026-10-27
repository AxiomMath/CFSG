module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8A

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def gElt (ιd : Perm (Fin 10) →* G) : G := ιd (swap 0 8 * swap 1 9)

@[expose] def yElt (ιd : Perm (Fin 10) →* G) : G := ιd (swap 1 8)

structure UFrame (z : G) (ι ιd : Perm (Fin 10) →* G) : Prop where
  cent : CentData z ι
  cent_d : CentData (ι (swap 0 1)) ιd
  z_eq : ιd (swap 0 1) = z
  eq : ∀ ρ : Perm (Fin 10), ρ 0 = 0 → ρ 1 = 1 → ιd ρ = ι ρ
  g_comm : ∀ ρ : Perm (Fin 8), gElt ιd * ι (liftS8 ρ) = ι (liftS8 ρ) * gElt ιd

namespace UFrame

variable {z : G} {ι ιd : Perm (Fin 10) →* G}

private theorem u_swap_comm_of_fixes {f : Perm (Fin 10)} {a b : Fin 10}
    (ha : f a = a) (hb : f b = b) : f * swap a b = swap a b * f := by
  rw [mul_swap_eq_swap_mul, ha, hb]

private theorem u_liftS8_apply_zero {ρ : Perm (Fin 8)} (h0 : ρ 0 = 0) : liftS8 ρ 0 = 0 := by
  rw [show (0 : Fin 10) = Fin.castLEEmb (by norm_num : 8 ≤ 10) (0 : Fin 8) from rfl,
    liftS8, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply, h0]

private theorem u_liftS8_apply_one {ρ : Perm (Fin 8)} (h1 : ρ 1 = 1) : liftS8 ρ 1 = 1 := by
  rw [show (1 : Fin 10) = Fin.castLEEmb (by norm_num : 8 ≤ 10) (1 : Fin 8) from rfl,
    liftS8, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply, h1]

theorem g_sq (F : UFrame z ι ιd) : gElt ιd * gElt ιd = 1 := by
  rw [gElt, ← map_mul, ← map_one ιd]
  congr 1
  decide

theorem g_z_g (F : UFrame z ι ιd) : gElt ιd * z * gElt ιd = ι τ₀ := by
  rw [gElt, ← F.z_eq, ← F.eq τ₀ (by decide) (by decide)]
  rw [← map_mul, ← map_mul]
  congr 1
  decide

theorem d8 (F : UFrame z ι ιd) : D8Rel z (gElt ιd) (z * ι τ₀) where
  z_sq := F.cent.mul_self
  g_sq := F.g_sq
  x_eq := by
    calc z * gElt ιd * z * gElt ιd = z * (gElt ιd * z * gElt ιd) := by group
      _ = z * ι τ₀ := by rw [F.g_z_g]
  x_ne := by
    intro h
    have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right F.cent.mul_self
    have hτ : ι τ₀ = z := by
      calc ι τ₀ = z⁻¹ * (z * ι τ₀) := by group
        _ = z⁻¹ * 1 := by rw [h]
        _ = z := by rw [mul_one, hz]
    exact F.cent.ne_z τ₀ hτ
  x_sq := by
    calc (z * ι τ₀) * (z * ι τ₀) = z * (ι τ₀ * z) * ι τ₀ := by group
      _ = z * (z * ι τ₀) * ι τ₀ := by rw [← F.cent.comm τ₀]
      _ = (z * z) * (ι τ₀ * ι τ₀) := by group
      _ = 1 := by rw [F.cent.mul_self, one_mul, ← map_mul, τ₀_mul_self, map_one]

theorem y_conj (F : UFrame z ι ιd) : yElt ιd * (z * ι τ₀) * (yElt ιd)⁻¹ = gElt ιd := by
  have hτ₀ : τ₀ = swap 8 9 := rfl
  have hsw : (swap (1 : Fin 10) 8)⁻¹ = swap 1 8 := swap_inv 1 8
  have hperm : swap (1 : Fin 10) 8 * (swap 0 1 * swap 8 9) * (swap (1 : Fin 10) 8)⁻¹ =
      swap 0 8 * swap 1 9 := by
    rw [hsw]; decide
  calc yElt ιd * (z * ι τ₀) * (yElt ιd)⁻¹
      = ιd (swap 1 8) * (ιd (swap 0 1) * ιd (swap 8 9)) * (ιd (swap 1 8))⁻¹ := by
        rw [yElt, ← F.z_eq, hτ₀, ← F.eq (swap 8 9) (by decide) (by decide)]
    _ = ιd (swap 1 8 * (swap 0 1 * swap 8 9) * (swap 1 8)⁻¹) := by
        simp only [← map_mul, ← map_inv]
    _ = ιd (swap 0 8 * swap 1 9) := by rw [hperm]
    _ = gElt ιd := by rw [gElt]

theorem y_comm_d (F : UFrame z ι ιd) : yElt ιd * ι (swap 0 1) = ι (swap 0 1) * yElt ιd := by
  rw [yElt]
  exact (F.cent_d.comm (swap 1 8)).symm

theorem y_comm_sigma (F : UFrame z ι ιd) {ρ : Perm (Fin 8)} (h0 : ρ 0 = 0) (h1 : ρ 1 = 1) :
    yElt ιd * ι (liftS8 ρ) = ι (liftS8 ρ) * yElt ιd := by
  have hfix0 : liftS8 ρ 0 = 0 := u_liftS8_apply_zero h0
  have hfix1 : liftS8 ρ 1 = 1 := u_liftS8_apply_one h1
  have hfix8 : liftS8 ρ 8 = 8 := liftS8_apply_eight ρ
  have hperm : liftS8 ρ * swap (1 : Fin 10) 8 = swap (1 : Fin 10) 8 * liftS8 ρ :=
    u_swap_comm_of_fixes hfix1 hfix8
  rw [yElt, ← F.eq (liftS8 ρ) hfix0 hfix1]
  rw [← map_mul, ← map_mul, hperm]

theorem z_comm_sigma (F : UFrame z ι ιd) (ρ : Perm (Fin 8)) :
    z * ι (liftS8 ρ) = ι (liftS8 ρ) * z := by
  exact F.cent.comm (liftS8 ρ)

theorem comm_D_sigma (F : UFrame z ι ιd) {q : G} (hq : q ∈ closure ({z, gElt ιd} : Set G))
    (ρ : Perm (Fin 8)) : q * ι (liftS8 ρ) = ι (liftS8 ρ) * q := by
  have hsub : ({z, gElt ιd} : Set G) ⊆ centralizer ({ι (liftS8 ρ)} : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_centralizer_singleton_iff.2 (F.z_comm_sigma ρ)
    · exact mem_centralizer_singleton_iff.2 (F.g_comm ρ)
  have hqK : q ∈ centralizer ({ι (liftS8 ρ)} : Set G) :=
    (closure_le (centralizer ({ι (liftS8 ρ)} : Set G))).mpr hsub hq
  exact mem_centralizer_singleton_iff.1 hqK

theorem eq_one_of_mem_D_of_eq_sigma (F : UFrame z ι ιd) {q : G}
    (hq : q ∈ closure ({z, gElt ιd} : Set G)) {ρ : Perm (Fin 8)} (h : q = ι (liftS8 ρ)) :
    q = 1 := by
  have hρ : ∀ ρ' : Perm (Fin 8), ρ * ρ' = ρ' * ρ := by
    intro ρ'
    have hcomm := comm_D_sigma F hq ρ'
    rw [h] at hcomm
    have h2 : ι (liftS8 ρ * liftS8 ρ') = ι (liftS8 ρ' * liftS8 ρ) := by
      rw [map_mul, map_mul]
      exact hcomm
    have h3 := F.cent.inj h2
    rw [← map_mul (liftS8), ← map_mul (liftS8)] at h3
    exact liftS8_injective h3
  have hρ1 : ρ = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) hρ
  rw [h, hρ1, map_one (liftS8), map_one ι]

theorem mul_self_eq_one_iff (F : UFrame z ι ιd) {q : G} (hq : q ∈ closure ({z, gElt ιd} : Set G))
    (ρ : Perm (Fin 8)) :
    (q * ι (liftS8 ρ)) * (q * ι (liftS8 ρ)) = 1 ↔ q * q = 1 ∧ ρ * ρ = 1 := by
  have hcomm : q * ι (liftS8 ρ) = ι (liftS8 ρ) * q := comm_D_sigma F hq ρ
  constructor
  · intro h
    have hsq : (q * q) * ι (liftS8 (ρ * ρ)) = 1 := by
      calc (q * q) * ι (liftS8 (ρ * ρ))
          = (q * q) * (ι (liftS8 ρ) * ι (liftS8 ρ)) := by
            rw [map_mul (liftS8), map_mul ι]
        _ = q * (q * ι (liftS8 ρ)) * ι (liftS8 ρ) := by group
        _ = q * (ι (liftS8 ρ) * q) * ι (liftS8 ρ) := by rw [hcomm]
        _ = (q * ι (liftS8 ρ)) * (q * ι (liftS8 ρ)) := by group
        _ = 1 := h
    have hqq : q * q = 1 := by
      have h1 : q * q = (ι (liftS8 (ρ * ρ)))⁻¹ := mul_eq_one_iff_eq_inv.mp hsq
      have h2 : q * q = ι (liftS8 ((ρ * ρ)⁻¹)) := by
        rw [h1, ← map_inv, ← map_inv]
      exact eq_one_of_mem_D_of_eq_sigma F (mul_mem hq hq) h2
    refine ⟨hqq, ?_⟩
    have hσ : ι (liftS8 (ρ * ρ)) = 1 := by simpa [hqq] using hsq
    have hlift : liftS8 (ρ * ρ) = 1 := F.cent.inj (hσ.trans (map_one ι).symm)
    exact liftS8_injective (hlift.trans (map_one (liftS8)).symm)
  · rintro ⟨hqq, hρρ⟩
    have hσ : ι (liftS8 ρ) * ι (liftS8 ρ) = 1 := by
      rw [← map_mul ι, ← map_mul (liftS8), hρρ, map_one (liftS8), map_one ι]
    calc (q * ι (liftS8 ρ)) * (q * ι (liftS8 ρ))
        = q * (ι (liftS8 ρ) * q) * ι (liftS8 ρ) := by group
      _ = q * (q * ι (liftS8 ρ)) * ι (liftS8 ρ) := by rw [hcomm.symm]
      _ = (q * q) * (ι (liftS8 ρ) * ι (liftS8 ρ)) := by group
      _ = 1 := by rw [hqq, hσ, mul_one]

theorem pairOrder_d_x₂ (F : UFrame z ι ιd) :
    pairOrder (ι (swap 0 1)) (z * ι τ₀) = N10 2 := by
  have ha : (swap (0 : Fin 10) 1 * swap 8 9) * (swap (0 : Fin 10) 1 * swap 8 9) = 1 := by
    decide
  have hcyc : Multiset.card ((swap (0 : Fin 10) 1 * swap 8 9)).cycleType = 2 := by
    have hd : Disjoint (swap (0 : Fin 10) 1) (swap 8 9) :=
      disjoint_swap_swap (by decide)
    rw [hd.cycleType_mul,
      isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (0 : Fin 10) ≠ 1)),
      isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (8 : Fin 10) ≠ 9))]
    decide
  have hmap : ιd (swap 0 1 * swap 8 9) = z * ι τ₀ := by
    calc ιd (swap 0 1 * swap 8 9) = ιd (swap 0 1) * ιd (swap 8 9) :=
          map_mul ιd (swap 0 1) (swap 8 9)
      _ = z * ιd (swap 8 9) := by rw [F.z_eq]
      _ = z * ι (swap 8 9) := by rw [F.eq (swap 8 9) (by decide) (by decide)]
      _ = z * ι τ₀ := rfl
  rw [← hmap, pairOrder, F.cent_d.card_inf_centralizer (swap 0 1 * swap 8 9),
    two_mul_card_centralizer_perm_ten ha, hcyc]

end UFrame

end CFSG.OddStandard.AltStdSec.SwapPartner
