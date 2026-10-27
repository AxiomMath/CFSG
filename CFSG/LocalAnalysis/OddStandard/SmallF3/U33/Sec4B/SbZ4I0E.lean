module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem z4i_comm_E_mem_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {e q : G}
    (he : e ∈ ctxEcY t tau x₁ x₂ rho) (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    e * q * e⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  have hq2Q : q ^ 2 ∈ ctxQ t tau x₁ x₂ rho := pow_mem hq 2
  have hq2Y : q ^ 2 ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hz.mem_Y_iff]
    refine ⟨hq2Q, ?_⟩
    rw [pow_two, ← pow_add, show (2 : ℕ) + 2 = 4 from rfl, hz.Q_pow_four q hq]
  have heq : e * q ^ 2 * e⁻¹ = q ^ 2 := by
    have hcomm : q ^ 2 * e = e * q ^ 2 := (mem_centralizer_iff.mp he.2) _ hq2Y
    rw [← hcomm]; group
  have haQ : e * q * e⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    (mem_set_normalizer_iff.mp he.1 q).mp hq
  have hcommQ : (e * q * e⁻¹) * q⁻¹ = q⁻¹ * (e * q * e⁻¹) :=
    hz.Q_comm _ haQ _ (inv_mem hq)
  rw [hz.mem_Y_iff]
  refine ⟨mul_mem haQ (inv_mem hq), ?_⟩
  rw [Commute.mul_pow hcommQ 2, conj_pow, inv_pow, heq, mul_inv_cancel]

private theorem t_comm_Q_mem (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : t * q * t⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  obtain ⟨V', v₁, v₂, hV, hVcard, hQeq, hbV, hYeq, -⟩ := hz.data_V
  have hcl : q ∈ Subgroup.closure ((baseGrp x₁ x₂ : Set G) ∪ (V' : Set G)) := by
    rw [← Subgroup.sup_eq_closure, ← hQeq]
    exact hq
  have key : q ∈ ctxQ t tau x₁ x₂ rho ∧
      t * q * t⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    Subgroup.closure_induction
      (p := fun g _ => g ∈ ctxQ t tau x₁ x₂ rho ∧
        t * g * t⁻¹ * g⁻¹ ∈ ctxYq t tau x₁ x₂ rho)
      (fun g hg => by
        rcases hg with hg | hg
        · refine ⟨hz.base_le_Q hg, ?_⟩
          have hmem : g ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
            rw [hz.CQ_t]; exact hg
          have hcomm : t * g = g * t := (mem_centralizer_iff.mp hmem.2) t rfl
          have h1 : t * g * t⁻¹ * g⁻¹ = 1 := by rw [hcomm]; group
          rw [h1]; exact one_mem _
        · have hgY : g ∈ ctxYq t tau x₁ x₂ rho := by
            rw [hYeq]; exact Subgroup.mem_sup_right hg
          exact ⟨hz.Y_le_Q hgY,
            mul_mem (hz.z4i_NQ_Y hz.z4i_t_mem_NQ hgY) (inv_mem hgY)⟩)
      ⟨one_mem _, by
        rw [show t * 1 * t⁻¹ * 1⁻¹ = (1 : G) from by group]; exact one_mem _⟩
      (fun x y _ _ ihx ihy => by
        set wx : G := t * x * t⁻¹ * x⁻¹ with hwx
        set wy : G := t * y * t⁻¹ * y⁻¹ with hwy
        have hxw : t * x * t⁻¹ = wx * x := by rw [hwx]; group
        have hyw : t * y * t⁻¹ = wy * y := by rw [hwy]; group
        have hwxY : wx ∈ ctxYq t tau x₁ x₂ rho := by rw [hwx]; exact ihx.2
        have hwyY : wy ∈ ctxYq t tau x₁ x₂ rho := by rw [hwy]; exact ihy.2
        have hcomm : wy * x = x * wy := hz.Q_comm _ (hz.Y_le_Q hwyY) x ihx.1
        refine ⟨mul_mem ihx.1 ihy.1, ?_⟩
        have hcalc : t * (x * y) * t⁻¹ * (x * y)⁻¹ = wx * wy := by
          calc t * (x * y) * t⁻¹ * (x * y)⁻¹
              = (t * x * t⁻¹) * (t * y * t⁻¹) * (y⁻¹ * x⁻¹) := by group
            _ = (wx * x) * (wy * y) * (y⁻¹ * x⁻¹) := by rw [hxw, hyw]
            _ = wx * (x * wy) * (y * y⁻¹) * x⁻¹ := by group
            _ = wx * (wy * x) * (y * y⁻¹) * x⁻¹ := by rw [← hcomm]
            _ = wx * wy := by group
        rw [hcalc]; exact mul_mem hwxY hwyY)
      (fun x _ ihx => by
        set wx : G := t * x * t⁻¹ * x⁻¹ with hwx
        have hxw : t * x * t⁻¹ = wx * x := by rw [hwx]; group
        have hwxY : wx ∈ ctxYq t tau x₁ x₂ rho := by rw [hwx]; exact ihx.2
        have hcomm : x⁻¹ * wx⁻¹ = wx⁻¹ * x⁻¹ :=
          hz.Q_comm _ (inv_mem ihx.1) _ (inv_mem (hz.Y_le_Q hwxY))
        refine ⟨inv_mem ihx.1, ?_⟩
        have hcalc : t * x⁻¹ * t⁻¹ * (x⁻¹)⁻¹ = wx⁻¹ := by
          have hxinv : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          rw [hxinv, hxw]
          rw [show (wx * x)⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * wx⁻¹ * x from by group]
          rw [hcomm]; group
        rw [hcalc]; exact inv_mem hwxY)
      hcl
  exact key.2

theorem z4i_t_comm_mem_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : t * q * t⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
  t_comm_Q_mem hz hq

theorem z4i_comm_mem_V (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k q : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho) (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    k * q * k⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ := by
  have hkE : k ∈ ctxEcY t tau x₁ x₂ rho := hz.z4i_KI_le_E hk
  set u : G := k * q * k⁻¹ * q⁻¹ with hu
  set w : G := t * q * t⁻¹ * q⁻¹ with hw
  set c : G := k * t * k⁻¹ * t⁻¹ with hc
  have huY : u ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hu]; exact hz.z4i_comm_E_mem_Y hkE hq
  have hwY : w ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hw]; exact z4i_t_comm_mem_Y hz hq
  have hcC : c ∈ ctxCQ t tau x₁ x₂ rho := by
    rw [hc]; exact hk.2.2
  have huQ : u ∈ ctxQ t tau x₁ x₂ rho := hz.Y_le_Q huY
  have hwQ : w ∈ ctxQ t tau x₁ x₂ rho := hz.Y_le_Q hwY
  have htuY : t * u * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    hz.z4i_NQ_Y hz.z4i_t_mem_NQ huY
  have htuQ : t * u * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hz.Y_le_Q htuY
  have e1 : k * (t * q * t⁻¹) * k⁻¹ = w * (u * q) := by
    have h1 : t * q * t⁻¹ = w * q := by rw [hw]; group
    have h2 : k * q * k⁻¹ = u * q := by rw [hu]; group
    have hcw : k * w * k⁻¹ = w := by
      have hcomm : w * k = k * w := (mem_centralizer_iff.mp hkE.2) w hwY
      rw [← hcomm]; group
    calc k * (t * q * t⁻¹) * k⁻¹
        = k * (w * q) * k⁻¹ := by rw [h1]
      _ = (k * w * k⁻¹) * (k * q * k⁻¹) := by group
      _ = w * (u * q) := by rw [hcw, h2]
  have e2 : k * (t * q * t⁻¹) * k⁻¹ = (t * u * t⁻¹) * (w * q) := by
    have h1 : k * t * k⁻¹ = c * t := by rw [hc]; group
    have h2 : k * q * k⁻¹ = u * q := by rw [hu]; group
    have h3 : t * q * t⁻¹ = w * q := by rw [hw]; group
    have htq : t * (u * q) * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      rw [← h2]
      exact (mem_set_normalizer_iff.mp hz.z4i_t_mem_NQ (k * q * k⁻¹)).mp
        ((mem_set_normalizer_iff.mp hk.2.1 q).mp hq)
    have hcomm4 : (t * (u * q) * t⁻¹) * c = c * (t * (u * q) * t⁻¹) :=
      (mem_centralizer_iff.mp hcC) _ htq
    have h4 : c * (t * (u * q) * t⁻¹) * c⁻¹ = t * (u * q) * t⁻¹ := by
      rw [← hcomm4]; group
    calc k * (t * q * t⁻¹) * k⁻¹
        = (k * t * k⁻¹) * (k * q * k⁻¹) * (k * t * k⁻¹)⁻¹ := by group
      _ = (c * t) * (u * q) * (c * t)⁻¹ := by rw [h1, h2]
      _ = c * (t * (u * q) * t⁻¹) * c⁻¹ := by group
      _ = t * (u * q) * t⁻¹ := h4
      _ = (t * u * t⁻¹) * (w * q) := by rw [← h3]; group
  have heq : w * (u * q) = (t * u * t⁻¹) * (w * q) := e1.symm.trans e2
  have hcancel : w * u = (t * u * t⁻¹) * w := by
    have h1 : w * (u * q) = (w * u) * q := by group
    have h2 : (t * u * t⁻¹) * (w * q) = ((t * u * t⁻¹) * w) * q := by group
    have h := heq
    rw [h1, h2] at h
    exact mul_right_cancel h
  have htu_comm : (t * u * t⁻¹) * w = w * (t * u * t⁻¹) := hz.Q_comm _ htuQ w hwQ
  have hu_eq : u = t * u * t⁻¹ := by
    rw [htu_comm] at hcancel
    exact mul_left_cancel hcancel
  have htu_comm_t : t * u = u * t := by
    calc t * u = (t * u * t⁻¹) * t := by group
      _ = u * t := by rw [← hu_eq]
  have hu_cent : u ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact htu_comm_t
  have hmem : u ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨huY, hu_cent⟩
  rw [hz.CY_t] at hmem
  exact hmem

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
