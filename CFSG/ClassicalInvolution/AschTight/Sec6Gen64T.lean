module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64S

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem Rstar_inf_le_X {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    Rstar ⊓ Subgroup.centralizer ({j} : Set G) ≤ 𝕏(K, J) := by
  have hYN := d.c.Y_le_normalizer_X d.hK0 d.hJ0
  intro w hw
  obtain ⟨hwR, hwj⟩ := Subgroup.mem_inf.mp hw
  have hwK := hRs.1 hwR
  have hwz : w ∈ Subgroup.centralizer ({z} : Set G) :=
    le_centralizer_of_isUniqueInvolution d.isUniqueInvolution_J' hwK
  have hwN := d.c.normalizer_UV_le (hRsN hwR)
  have hρN := d.c.normalizer_UV_le d.rho_mem_normalizer
  have hw'J : (r * t) * w * (r * t)⁻¹ ∈ J := by
    rw [mem_conjSub_iff, inv_inv] at hwK
    exact hwK
  have hw'N : (r * t) * w * (r * t)⁻¹ ∈
      Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hρN hwN) (Subgroup.inv_mem _ hρN)
  have hw'XT : (r * t) * w * (r * t)⁻¹ ∈ 𝕏(K, J) ⊔ Subgroup.zpowers t := by
    have hZ : Subgroup.closure ({j, z} : Set G) = Subgroup.closure ({z, j} : Set G) := by
      rw [Set.pair_comm]
    have h1 : (r * t) * w * (r * t)⁻¹ ∈ J ⊓ Subgroup.normalizer
        ((Subgroup.closure ({j, z} : Set G) : Subgroup G) : Set G) := by
      rw [hZ]
      exact ⟨hw'J, hw'N⟩
    have h2 := d.c.symm.NKZ_le h1
    have hX : (K ⊓ Subgroup.normalizer (J : Set G)) ⊔ (J ⊓ Subgroup.normalizer (K : Set G)) =
        𝕏(K, J) := sup_comm _ _
    rw [hX] at h2
    exact (sup_le le_sup_left d.T_le) h2
  have hwzj : w * (z * j) * w⁻¹ = z * j := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (mem_centralizer_mul hwz hwj)
    rw [this]
    group
  have hw'z : (r * t) * w * (r * t)⁻¹ * z * ((r * t) * w * (r * t)⁻¹)⁻¹ = z := by
    calc (r * t) * w * (r * t)⁻¹ * z * ((r * t) * w * (r * t)⁻¹)⁻¹ =
          (r * t) * (w * ((r * t)⁻¹ * z * (r * t)⁻¹⁻¹) * w⁻¹) * (r * t)⁻¹ := by group
      _ = (r * t) * (z * j) * (r * t)⁻¹ := by rw [d.conj_rho_inv_z, hwzj]
      _ = z := d.conj_rho_zj
  rcases d.mem_X_or_of_mem_XT hw'XT with h | h
  · have := (Subgroup.mem_normalizer_iff.mp (hYN (Subgroup.inv_mem _ d.rho_mem_Y)) _).mp h
    have e : (r * t)⁻¹ * ((r * t) * w * (r * t)⁻¹) * (r * t)⁻¹⁻¹ = w := by group
    rwa [e] at this
  · exfalso
    have hx := Subgroup.mem_centralizer_singleton_iff.mp (d.c.X_le_centralizer_z h)
    have e1 : (r * t) * w * (r * t)⁻¹ * z * ((r * t) * w * (r * t)⁻¹)⁻¹ =
        t * ((t⁻¹ * ((r * t) * w * (r * t)⁻¹)) * z * (t⁻¹ * ((r * t) * w * (r * t)⁻¹))⁻¹) *
          t⁻¹ := by group
    have e2 : (t⁻¹ * ((r * t) * w * (r * t)⁻¹)) * z * (t⁻¹ * ((r * t) * w * (r * t)⁻¹))⁻¹ = z := by
      rw [hx]
      group
    rw [e2, d.c.conj_t_z d.ht d.htv, hw'z] at e1
    exact d.c.zj_ne_z e1.symm

theorem Rstar_inf_le_UV {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    Rstar ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  have h1 : (Rstar ⊓ Subgroup.centralizer ({j} : Set G)) ⊔
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ≤ 𝕏(K, J) :=
    sup_le (d.Rstar_inf_le_X hRs hRsN) (sup_le d.U_le_X d.V_le_X)
  have h2 : IsPGroup 2 ↥((Rstar ⊓ Subgroup.centralizer ({j} : Set G)) ⊔
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v)) :=
    IsPGroup.to_sup_of_normal_right' (hRs.2.1.to_le inf_le_left) d.c.UV_isPGroup
      (inf_le_left.trans hRsN)
  have h3 := d.UV_sylow.eq_of_le h2 h1 le_sup_right
  rw [← h3]
  exact le_sup_left

theorem Ustar_le_Rstar {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    conjSub (r * t)⁻¹ (Subgroup.zpowers v) ≤ Rstar := by
  have h2 : IsPGroup 2 ↥(Rstar ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v)) :=
    IsPGroup.to_sup_of_normal_right' hRs.2.1 d.c.UV_isPGroup hRsN
  have h3 : IsPGroup 2 ↥(Rstar ⊔ conjSub (r * t)⁻¹ (Subgroup.zpowers v)) :=
    h2.to_le (sup_le le_sup_left (d.Ustar_le_UV.trans le_sup_right))
  have h4 := hRs.eq_of_le h3 (sup_le hRs.1 (conjSub_mono d.c.hVJ)) le_sup_left
  rw [← h4]
  exact le_sup_right

theorem Rstar_inf_eq {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    Rstar ⊓ Subgroup.centralizer ({j} : Set G) = conjSub (r * t)⁻¹ (Subgroup.zpowers v) := by
  refine le_antisymm ?_
    (le_inf (d.Ustar_le_Rstar hRs hRsN) (d.Ustar_le_UV.trans d.UV_le_centralizer_j))
  rw [← d.Kstar_inf_UV]
  exact le_inf (inf_le_left.trans hRs.1) (d.Rstar_inf_le_UV hRs hRsN)

theorem Rstar_le_Y {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    Rstar ≤ pairNormalizers K J z j := fun _ hw =>
  d.Kstar_inf_normalizer_le_Y ⟨hRs.1 hw, d.c.normalizer_UV_le (hRsN hw)⟩

omit [Finite G] in
theorem Rstar0_sylow : IsSylow2In (conjSub (r * t)⁻¹ T) (conjSub (r * t)⁻¹ J) :=
  IsSylow2In.conj d.c.hT _

omit [Finite G] in
theorem Rstar0_le_normalizer : conjSub (r * t)⁻¹ T ≤ Subgroup.normalizer
    ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  intro w hw
  rw [mem_conjSub_iff] at hw
  have hρ := d.rho_mem_normalizer
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ ((Subgroup.normalizer _).inv_mem hρ) (d.c.hTN hw))
    hρ
  have e : (r * t)⁻¹ * ((r * t)⁻¹⁻¹ * w * (r * t)⁻¹) * (r * t) = w := by group
  rwa [e] at this

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
