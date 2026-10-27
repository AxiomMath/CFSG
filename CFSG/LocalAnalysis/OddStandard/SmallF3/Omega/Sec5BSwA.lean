module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwX0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwKer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43

theorem sw_core_tau_ne_one {Λ : Type} [Group Λ] [Finite Λ] {τ : Λ →* X₀}
    (hτ : SwCentralTwo τ) {A₁ A₂ : Subgroup Λ} {z : Λ} (S : SwSetup A₁ A₂ z) : τ z ≠ 1 := by
  classical
  intro hz
  have hzker : z ∈ τ.ker := MonoidHom.mem_ker.mpr hz
  have hzcent : z ∈ Subgroup.center Λ := hτ.ker_central hzker
  have hodd : ∀ o : Λ, Odd (orderOf o) → o ∈ A₁ ⊔ A₂ := by
    intro o ho
    exact S.odd_mem o (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp hzcent o)) ho
  have hmap_sup : A₁.map τ ⊔ A₂.map τ = (A₁ ⊔ A₂).map τ :=
    (Subgroup.map_sup A₁ A₂ τ).symm
  have hclosure : Subgroup.closure {x : X₀ | Odd (orderOf x)} ≤ A₁.map τ ⊔ A₂.map τ := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨o, ho, hox⟩ := hτ.odd_lift hx
    rw [hmap_sup]
    exact Subgroup.mem_map.mpr ⟨o, hodd o ho, hox⟩
  have htop : A₁.map τ ⊔ A₂.map τ = ⊤ := by
    have h := hclosure
    rw [sw_x0_closure_odd] at h
    exact top_le_iff.mp h
  have hcomm : ∀ u ∈ A₁.map τ, ∀ v ∈ A₂.map τ, u * v = v * u := by
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_mul, ← map_mul, S.comm a ha b hb]
  rcases sw_x0_comm_sup_top hcomm htop with h1 | h2
  · have hA1 : A₁ ≤ τ.ker := (Subgroup.map_eq_bot_iff A₁).mp h1
    have hcent : A₁ ≤ Subgroup.center Λ := hA1.trans hτ.ker_central
    obtain ⟨a, ha, b, hb, hab⟩ := S.pocket₁.noncomm
    exact hab ((Subgroup.mem_center_iff.mp (hcent ha) b).symm)
  · have hA2 : A₂ ≤ τ.ker := (Subgroup.map_eq_bot_iff A₂).mp h2
    have hcent : A₂ ≤ Subgroup.center Λ := hA2.trans hτ.ker_central
    obtain ⟨a, ha, b, hb, hab⟩ := S.pocket₂.noncomm
    exact hab ((Subgroup.mem_center_iff.mp (hcent ha) b).symm)

end CFSG.OddStandard.SmallF3.Omega
