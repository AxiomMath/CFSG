module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64V

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem conj_rstar_j {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G)) :
    rs * j * rs⁻¹ = z * j := by
  have hmem : rs * j * rs⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
    (Subgroup.mem_normalizer_iff.mp (hRsN hrs) j).mp d.c.j_mem_UV
  have hsq : (rs * j * rs⁻¹) * (rs * j * rs⁻¹) = 1 := by
    calc (rs * j * rs⁻¹) * (rs * j * rs⁻¹) = rs * (j * j) * rs⁻¹ := by group
      _ = 1 := by rw [d.c.hj.sq]; group
  have hrsz : rs * z * rs⁻¹ = z := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_isUniqueInvolution d.isUniqueInvolution_J' (hRs.1 hrs)))]
    group
  rcases d.c.sq_eq_one_of_mem_UV hmem hsq with h | h | h | h
  · exfalso
    apply d.c.hj.ne_one
    have := congrArg (fun w => rs⁻¹ * w * rs) h
    simpa [mul_assoc] using this
  · exfalso
    apply d.c.z_ne_j
    have h1 : rs * j * rs⁻¹ = rs * z * rs⁻¹ := by rw [h, hrsz]
    have := congrArg (fun w => rs⁻¹ * w * rs) h1
    simpa [mul_assoc] using this.symm
  · exfalso
    apply hrsj
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc rs * j = (rs * j * rs⁻¹) * rs := by group
      _ = j * rs := by rw [h]
  · exact h

theorem comm_of_twin {M N : Subgroup G} (hM : M ∈ Ω) (hN : N ∈ Ω) (hMN : M ≠ N)
    (hzM : IsUniqueInvolution M z) (hzN : IsUniqueInvolution N z) {a w : G} (ha : a ∈ M)
    (haN : a ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    (hw : w ∈ N) (hwUV : w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) : a * w * a⁻¹ = w := by
  have hc := comm_le_oddCore_of_twin d.c.hΩ hM hN hMN hzM hzN
  have h1 : ⁅a, w⁆ ∈ oddCoreOf M := (hc (Subgroup.commutator_mem_commutator ha hw)).1
  have h2 : ⁅a, w⁆ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp haN w).mp hwUV)
      (Subgroup.inv_mem _ hwUV)
  have h3 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) h1
    (d.c.UV_isPGroup.to_le (Subgroup.zpowers_le.mpr h2))
  rw [commutatorElement_def] at h3
  calc a * w * a⁻¹ = a * w * a⁻¹ * w⁻¹ * w := by group
    _ = w := by rw [h3, one_mul]

theorem rrstar_conj {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G)) :
    (r * rs) * z * (r * rs)⁻¹ = z ∧ (r * rs) * j * (r * rs)⁻¹ = j := by
  have hrsz : rs * z * rs⁻¹ = z := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_isUniqueInvolution d.isUniqueInvolution_J' (hRs.1 hrs)))]
    group
  refine ⟨?_, ?_⟩
  · calc (r * rs) * z * (r * rs)⁻¹ = r * (rs * z * rs⁻¹) * r⁻¹ := by group
      _ = z := by rw [hrsz, d.c.conj_z d.hr]
  · calc (r * rs) * j * (r * rs)⁻¹ = r * (rs * j * rs⁻¹) * r⁻¹ := by group
      _ = (r * z * r⁻¹) * (r * j * r⁻¹) := by rw [d.conj_rstar_j hRs hRsN hrs hrsj]; group
      _ = j := by rw [d.c.conj_z d.hr, d.c.conj_j_of_not_mem d.hr d.hru, ← mul_assoc,
          d.c.hz.sq, one_mul]

theorem rrstar_mem_Y {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) : r * rs ∈ pairNormalizers K J z j :=
  Subgroup.mul_mem _ d.r_mem_Y (d.Rstar_le_Y hRs hRsN hrs)

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
