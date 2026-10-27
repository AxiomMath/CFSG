module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BSd
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def sec8t84g3b_Z (Q U U' : Subgroup G) : Subgroup G :=
  twoRes (Q ⊓ centralizer (U' : Set G)) ⊔ U

theorem sec8t84g3b_Z_le {Q U U' K : Subgroup G}
    (h1 : ∀ y ∈ Q, y ∈ centralizer (U' : Set G) → Odd (orderOf y) → y ∈ K) (h2 : U ≤ K) :
    sec8t84g3b_Z Q U U' ≤ K := by
  refine sup_le ?_ h2
  unfold twoRes
  refine (Subgroup.closure_le K).mpr ?_
  rintro y ⟨⟨hyQ, hyC⟩, hyodd⟩
  exact h1 y hyQ hyC hyodd

theorem sec8t84g3b_conj_conj {γ : G} (hγ2 : γ * γ = 1) (x : G) :
    γ * (γ * x * γ⁻¹) * γ⁻¹ = x := by
  calc γ * (γ * x * γ⁻¹) * γ⁻¹ = (γ * γ) * x * (γ⁻¹ * γ⁻¹) := by group
    _ = x := by rw [hγ2, ← mul_inv_rev, hγ2, inv_one]; simp

theorem sec8t84g3b_Z_conj {Q U U' : Subgroup G} {γ : G} (hγ2 : γ * γ = 1)
    (hQ : ∀ x ∈ Q, γ * x * γ⁻¹ ∈ Q) (hU : ∀ u ∈ U, γ * u * γ⁻¹ ∈ U)
    (hU' : ∀ u ∈ U', γ * u * γ⁻¹ ∈ U') :
    ∀ z ∈ sec8t84g3b_Z Q U U', γ * z * γ⁻¹ ∈ sec8t84g3b_Z Q U U' := by
  have h : sec8t84g3b_Z Q U U' ≤
      (sec8t84g3b_Z Q U U').comap (MulAut.conj γ).toMonoidHom := by
    refine sec8t84g3b_Z_le (fun y hyQ hyC hodd => ?_) (fun u hu => ?_)
    · have hc : γ * y * γ⁻¹ ∈ centralizer (U' : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u' hu'
        have hu'' : γ * u' * γ⁻¹ ∈ U' := hU' u' hu'
        have h1 : (γ * u' * γ⁻¹) * y = y * (γ * u' * γ⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hyC _ hu''
        have h2 : u' * (γ * y * γ⁻¹) = (γ * y * γ⁻¹) * u' := by
          calc u' * (γ * y * γ⁻¹)
              = (γ * (γ * u' * γ⁻¹) * γ⁻¹) * (γ * y * γ⁻¹) := by
                rw [sec8t84g3b_conj_conj hγ2]
            _ = γ * ((γ * u' * γ⁻¹) * y) * γ⁻¹ := by group
            _ = γ * (y * (γ * u' * γ⁻¹)) * γ⁻¹ := by rw [h1]
            _ = (γ * y * γ⁻¹) * (γ * (γ * u' * γ⁻¹) * γ⁻¹) := by group
            _ = (γ * y * γ⁻¹) * u' := by rw [sec8t84g3b_conj_conj hγ2]
        exact h2
      have hodd' : Odd (orderOf (γ * y * γ⁻¹)) := by
        have h3 := orderOf_injective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective y
        have h4 : orderOf (γ * y * γ⁻¹) = orderOf y := h3
        rw [h4]; exact hodd
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨hQ y hyQ, hc⟩, hodd'⟩)
    · exact Subgroup.mem_sup_right (hU u hu)
  exact fun z hz => h hz

theorem sec8t84g3b_odd_of_pow {Q : Subgroup G} {y : G} {k : ℕ} (hk : Odd k)
    (h : y ^ k ∈ oddCoreIn Q) : Odd (orderOf y) := by
  have h1 : orderOf (y ^ k) ∣ Nat.card (oddCoreIn Q) := by
    have := orderOf_dvd_natCard (⟨y ^ k, h⟩ : oddCoreIn Q)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : Odd (orderOf (y ^ k)) :=
    Odd.of_dvd_nat (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn Q) h1
  have h3 : orderOf y ∣ k * orderOf (y ^ k) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact pow_orderOf_eq_one _)
  exact Odd.of_dvd_nat (hk.mul h2) h3

theorem sec8t84g3b_Q_le_E {E E0 : Subgroup G} : sec8t84g_Q E E0 ≤ normalizer (E : Set G) :=
  inf_le_left

theorem sec8t84g3b_Q_le_E0 {E E0 : Subgroup G} : sec8t84g_Q E E0 ≤ normalizer (E0 : Set G) :=
  inf_le_right

theorem sec8t84g3b_conj_W {E E0 : Subgroup G} {y : G} (hy : y ∈ sec8t84g_Q E E0) :
    ∀ x ∈ E ⊔ E0, y * x * y⁻¹ ∈ E ⊔ E0 := by
  refine sec8t84g3b_conj_sup (fun e he => ?_) (fun e he => ?_)
  · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
      (sec8t84g3b_Q_le_E hy) e).mp he)
  · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
      (sec8t84g3b_Q_le_E0 hy) e).mp he)

variable {E E0 Y Y' V V' F F' P H : Subgroup G}

theorem Sec8T84G3BSide.Z_le_Y (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) :
    sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤ Y := by
  refine sec8t84g3b_Z_le (fun y hyQ hyC hodd => ?_) S.U_le_Y
  refine S.odd_Y (sec8t84g3b_Q_le_E hyQ) hodd (fun v hv => ?_)
  exact (Subgroup.mem_centralizer_iff.mp hyC v (Subgroup.mem_sup_left hv)).symm

end CFSG.OddStandard.SmallF3.Omega
