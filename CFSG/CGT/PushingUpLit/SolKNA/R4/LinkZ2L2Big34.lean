module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big33

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.theta_center_mem_E (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (θ : ↥R₀ →* Y) (hθ : Function.Injective θ) (hθP : ∀ x, θ x ∈ (P : Subgroup Y)) :
    θ ⟨t, hs.t_mem_R₀⟩ ∈ Subgroup.closure ({t, u} : Set Y) := by
  obtain ⟨e₀, he₀⟩ := hs.exists_quat_R₀ hr
  let θ₀ : QuaternionGroup (2 ^ (r - 2)) →* Y := θ.comp e₀.symm.toMonoidHom
  have hθ₀ : Function.Injective θ₀ := hθ.comp e₀.symm.injective
  have hθ₀P : ∀ x, θ₀ x ∈ (P : Subgroup Y) := fun x => hθP _
  have hcen : θ₀ (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) =
      θ ⟨t, hs.t_mem_R₀⟩ := by
    show θ (e₀.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))) = _
    congr 1
    exact Subtype.ext he₀
  have hsq : ∀ x : QuaternionGroup (2 ^ (r - 2)),
      θ₀ x * θ₀ x ∈ edgeCent (P : Subgroup Y) t u := fun x =>
    hs.mul_self_mem_edgeCent (hθ₀P x)
  by_cases hA : θ₀ (QuaternionGroup.a 1) ∈ edgeCent (P : Subgroup Y) t u
  ·
    have hpow : (2 : ℕ) ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [show r - 1 = r - 2 + 1 by omega, pow_succ]
      ring
    have hx1 : (θ₀ (QuaternionGroup.a 1)) ^ 2 ^ (r - 1) = 1 := by
      rw [← map_pow, QuaternionGroup.a_one_pow, hpow, ZMod.natCast_self,
        show QuaternionGroup.a 0 = 1 from QuaternionGroup.one_def, map_one]
    have hx : (θ₀ (QuaternionGroup.a 1)) ^ 2 ^ (r - 2) = θ ⟨t, hs.t_mem_R₀⟩ := by
      rw [← map_pow, QuaternionGroup.a_one_pow]
      exact hcen
    have hmem := hs.mem_E_of_actsInE
      ((edgeCent (P : Subgroup Y) t u).pow_mem hA (2 ^ (r - 2)))
      (hs.actsInE_of_cyc hr hA hx1)
    rwa [hx] at hmem
  ·
    have hδ : ∃ δ : ZMod (2 * 2 ^ (r - 2)),
        θ₀ (QuaternionGroup.xa δ) ∈ edgeCent (P : Subgroup Y) t u := by
      by_cases h0 : θ₀ (QuaternionGroup.xa 0) ∈ edgeCent (P : Subgroup Y) t u
      · exact ⟨0, h0⟩
      · refine ⟨1, ?_⟩
        have hswap0 := hs.aux_swap (hθ₀P (QuaternionGroup.xa 0)) h0
        have hswap1 := hs.aux_swap (hθ₀P (QuaternionGroup.a 1)) hA
        have hmul : θ₀ (QuaternionGroup.xa 1) =
            θ₀ (QuaternionGroup.xa 0) * θ₀ (QuaternionGroup.a 1) := by
          rw [← map_mul, QuaternionGroup.xa_mul_a, zero_add]
        rw [hs.mem_edgeCent_iff]
        refine ⟨?_, ?_⟩
        · rw [hmul]
          exact (P : Subgroup Y).mul_mem (hθ₀P _) (hθ₀P _)
        · rw [hmul]
          calc (θ₀ (QuaternionGroup.xa 0) * θ₀ (QuaternionGroup.a 1)) * t *
              (θ₀ (QuaternionGroup.xa 0) * θ₀ (QuaternionGroup.a 1))⁻¹
            = θ₀ (QuaternionGroup.xa 0) * (θ₀ (QuaternionGroup.a 1) * t *
                (θ₀ (QuaternionGroup.a 1))⁻¹) * (θ₀ (QuaternionGroup.xa 0))⁻¹ := by group
          _ = θ₀ (QuaternionGroup.xa 0) * u * (θ₀ (QuaternionGroup.xa 0))⁻¹ := by
            rw [hswap1.1]
          _ = t := hswap0.2
    obtain ⟨δ, hδA⟩ := hδ
    have hn : 2 ^ (r - 2) = 2 * 2 ^ (r - 3) := by
      rw [show r - 2 = r - 3 + 1 by omega, pow_succ]
      ring
    haveI : NeZero (2 ^ (r - 3)) := ⟨by positivity⟩
    obtain ⟨φ, hφinj, hφsq, hφxa, hφc⟩ :=
      QuatAutH.exists_double_hom (n := 2 ^ (r - 3)) (n' := 2 ^ (r - 2)) hn δ
    let ψ : QuaternionGroup (2 ^ (r - 3)) →* Y := θ₀.comp φ
    have hψinj : Function.Injective ψ := hθ₀.comp hφinj
    let B : Subgroup Y := ψ.range
    have haA : ∀ j : ZMod (2 * 2 ^ (r - 3)),
        ψ (QuaternionGroup.a j) ∈ edgeCent (P : Subgroup Y) t u := by
      intro j
      obtain ⟨k, hk⟩ := hφsq j
      rw [show ψ (QuaternionGroup.a j) = θ₀ (φ (QuaternionGroup.a j)) from rfl, hk, map_mul]
      exact hs.mul_self_mem_edgeCent (hθ₀P _)
    have hBA : B ≤ edgeCent (P : Subgroup Y) t u := by
      rintro _ ⟨q, rfl⟩
      rcases q with j | j
      · exact haA j
      · rw [show ψ (QuaternionGroup.xa j) = θ₀ (φ (QuaternionGroup.xa j)) from rfl,
          hφxa j, map_mul]
        exact (edgeCent (P : Subgroup Y) t u).mul_mem hδA (haA j)
    let eB : ↥B ≃* QuaternionGroup (2 ^ (r - 3)) :=
      (MonoidHom.ofInjective hψinj).symm
    have hcenterB : ((eB.symm (QuaternionGroup.a
        ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 3)))) : ↥B) : Y) =
        θ ⟨t, hs.t_mem_R₀⟩ := by
      dsimp only [eB]
      rw [MulEquiv.symm_symm, MonoidHom.ofInjective_apply]
      show θ₀ (φ (QuaternionGroup.a _)) = _
      rw [hφc, hcen]
    have hmem := hs.mem_E_of_actsInE
      (hBA (eB.symm (QuaternionGroup.a
        ((2 ^ (r - 3) : ℕ) : ZMod (2 * 2 ^ (r - 3))))).2)
      (hs.actsInE_of_quat (m := r - 3) hr hBA (by omega) eB)
    rwa [hcenterB] at hmem

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
