module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64X

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

theorem conj_of_mem_centralizer_Z {G : Type} [Group G] {z j y : G} (hy : y ∈
    Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G)) :
    y * z * y⁻¹ = z ∧ y * j * y⁻¹ = j := by
  have hz := Subgroup.mem_centralizer_iff.mp hy z (Subgroup.subset_closure (by simp))
  have hj := Subgroup.mem_centralizer_iff.mp hy j (Subgroup.subset_closure (by simp))
  exact ⟨by rw [← hz]; group, by rw [← hj]; group⟩

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

variable [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal]

theorem centralizer_Z_eq (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J)
    {Rstar : Subgroup G} (hRs : IsSylow2In Rstar (conjSub (r * t)⁻¹ J))
    (hRsN : Rstar ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    {rs : G} (hrs : rs ∈ Rstar) (hrsj : rs ∉ Subgroup.centralizer ({j} : Set G)) :
    pairNormalizers K J z j ⊓ Subgroup.centralizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) =
      𝕏(K, J) ⊔ Subgroup.zpowers (r * rs) := by
  have hq := d.rrstar_mem_Y hRs hRsN hrs
  obtain ⟨hqz, hqj⟩ := d.rrstar_conj hRs hRsN hrs hrsj
  apply le_antisymm
  · intro y hy
    obtain ⟨hyY, hyc⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyz, hyj⟩ := conj_of_mem_centralizer_Z hyc
    rcases d.mem_X_or_rrstar hA hRs hRsN hrs hrsj hyY hyz hyj with h | h
    · exact Subgroup.mem_sup_left h
    · have := Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers (r * rs)) :
          r * rs ∈ 𝕏(K, J) ⊔ Subgroup.zpowers (r * rs)) (Subgroup.mem_sup_left h)
      rwa [mul_inv_cancel_left] at this
  · refine sup_le (fun x hx => Subgroup.mem_inf.mpr ⟨d.c.X_le_Y hx,
      mem_centralizer_Z (d.c.X_le_centralizer_z hx) (d.c.X_le_centralizer_j hx)⟩) ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hq, mem_centralizer_Z ?_ ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (r * rs) * z = (r * rs) * z * (r * rs)⁻¹ * (r * rs) := by group
        _ = z * (r * rs) := by rw [hqz]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (r * rs) * j = (r * rs) * j * (r * rs)⁻¹ * (r * rs) := by group
        _ = j * (r * rs) := by rw [hqj]

omit [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal] in
theorem rstar0_not_mem : (r * t)⁻¹ * t * (r * t)⁻¹⁻¹ ∉ Subgroup.centralizer ({j} : Set G) := by
  have e : ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) * j * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹)⁻¹ = z * j := by
    calc ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) * j * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹)⁻¹ =
          (r * t)⁻¹ * (t * ((r * t) * j * (r * t)⁻¹) * t⁻¹) * (r * t)⁻¹⁻¹ := by group
      _ = (r * t)⁻¹ * ((t * z * t⁻¹) * (t * j * t⁻¹)) * (r * t)⁻¹⁻¹ := by
          rw [d.c.conj_rho_j d.hr d.hru d.ht]; group
      _ = (r * t)⁻¹ * z * (r * t)⁻¹⁻¹ := by
          rw [d.c.conj_t_z d.ht d.htv, d.c.conj_t_j d.ht, mul_assoc z j j, d.c.hj.sq, mul_one]
      _ = z * j := d.conj_rho_inv_z
  intro h
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp h
  have h2 : ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) * j * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹)⁻¹ = j := by
    rw [h1]
    group
  exact d.c.zj_ne_j (e.symm.trans h2)

theorem centralizer_UV_le (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    pairNormalizers K J z j ⊓ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ≤ 𝕏(K, J) := by
  have hne := d.Kstar_ne hA
  have hrs0 : (r * t)⁻¹ * t * (r * t)⁻¹⁻¹ ∈ conjSub (r * t)⁻¹ T := conj_mem_conjSub d.ht
  intro y hy
  obtain ⟨hyY, hyc⟩ := Subgroup.mem_inf.mp hy
  have hcen : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, y * w * y⁻¹ = w := by
    intro w hw
    rw [(Subgroup.mem_centralizer_iff.mp hyc w hw).symm]
    group
  have hyz : y * z * y⁻¹ = z := hcen z d.c.z_mem_UV
  have hyj : y * j * y⁻¹ = j := hcen j d.c.j_mem_UV
  rcases d.mem_X_or_rrstar hA d.Rstar0_sylow d.Rstar0_le_normalizer hrs0 d.rstar0_not_mem hyY
    hyz hyj with h | h
  · exact h
  · exfalso
    set q := r * ((r * t)⁻¹ * t * (r * t)⁻¹⁻¹) with hq
    have hqN : q ∈ Subgroup.normalizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (d.c.hRN d.hr) (d.Rstar0_le_normalizer hrs0)
    have hyN : y ∈ Subgroup.normalizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hyc
    have hxN : q⁻¹ * y ∈ Subgroup.normalizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hqN) hyN
    have hxc := d.centralizes_of_mem_X h hxN
    apply d.rrstar_not_centralizes hne d.Rstar0_sylow d.Rstar0_le_normalizer hrs0
      d.rstar0_not_mem
    intro w hw
    have e : q * w * q⁻¹ = y * ((q⁻¹ * y)⁻¹ * w * (q⁻¹ * y)⁻¹⁻¹) * y⁻¹ := by group
    have hw' : (q⁻¹ * y)⁻¹ * w * (q⁻¹ * y)⁻¹⁻¹ = w := by
      have h1 := hxc w hw
      calc (q⁻¹ * y)⁻¹ * w * (q⁻¹ * y)⁻¹⁻¹ =
            (q⁻¹ * y)⁻¹ * ((q⁻¹ * y) * w * (q⁻¹ * y)⁻¹) * (q⁻¹ * y)⁻¹⁻¹ := by rw [h1]
        _ = w := by group
    rw [e, hw', hcen w hw]

theorem inf_eq_UV (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) {W : Subgroup G}
    (hW2 : IsPGroup 2 W) (hUVW : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ W)
    (hWc : W ≤ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    pairNormalizers K J z j ⊓ W = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  have hUVX : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ 𝕏(K, J) := sup_le d.U_le_X d.V_le_X
  apply le_antisymm
  · intro w hw
    obtain ⟨hwY, hwW⟩ := Subgroup.mem_inf.mp hw
    have hwX : w ∈ 𝕏(K, J) := d.centralizer_UV_le hA (Subgroup.mem_inf.mpr ⟨hwY, hWc hwW⟩)
    have hXW : 𝕏(K, J) ⊓ W = Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
      d.UV_sylow.eq_of_le (hW2.to_le inf_le_right) inf_le_left (le_inf hUVX hUVW)
    rw [← hXW]
    exact Subgroup.mem_inf.mpr ⟨hwX, hwW⟩
  · exact le_inf (hUVX.trans d.c.X_le_Y) hUVW

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
