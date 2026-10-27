module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Char

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Concl
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem s0_quasithinOmegaOneCenter_le_vOf (h : Setup28 W K S) :
    quasithinOmegaOneCenter S ≤ vOf W K S := by
  refine (Subgroup.closure_le _).2 fun z hz => ?_
  obtain ⟨hzI, hz2⟩ := hz
  have hzS : z ∈ S := (Subgroup.mem_inf.1 hzI).1
  have hzC : z ∈ Subgroup.centralizer (S : Set X) := (Subgroup.mem_inf.1 hzI).2
  have hzW : z ∈ Subgroup.centralizer (W : Set X) := Subgroup.centralizer_le h.hWS hzC
  have hzk : z ∈ kerAct W K S := s0_w_le_kerAct h (h.hC hzW)
  exact ⟨hzk, fun w hw =>
    (Subgroup.mem_centralizer_iff.1 hzC w (s0_kerAct_le_S hw)).symm, hz2⟩

theorem s0_concl28d_aux (h : Setup28 W K S)
    (hK : K ≤ Subgroup.centralizer (vOf W K S : Set X)) : Concl28d K S := by
  have hcomm : ∀ k ∈ K, ∀ y ∈ quasithinOmegaOneCenter S, k * y * k⁻¹ = y := by
    intro k hk y hy
    have hyV : y ∈ vOf W K S := s0_quasithinOmegaOneCenter_le_vOf h hy
    have := Subgroup.mem_centralizer_iff.1 (hK hk) y hyV
    rw [← this]
    group
  refine ⟨quasithinOmegaOneCenter S,
    CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97.omegaOneCenter_ne_bot h.hS (s0_S_ne_bot h),
    CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97.isCharIn_omegaOneCenter S, fun k hk => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [hcomm k hk x hx]
    exact hx
  · have h1 := hcomm k⁻¹ (K.inv_mem hk) _ hx
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rw [e] at h1
    rw [h1]
    exact hx

end Concl

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
