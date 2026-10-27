module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Delta
public import CFSG.CGT.PushingUpLit.T2KR.Fus613Pres

public section

namespace CFSG.CGT.PushingUpLit.T2KR.MData

open CFSG.CGT.PushingUpLit.T2K

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

theorem vec_mul_self (w : Fin 2 → Fq n) : H.vec w * H.vec w = 1 := by
  have h2 : (2 : Fq n) = 0 := CFSG.CGT.PushingUpLit.T2KR.P613.two_eq_zero
  rw [← H.vec_add, ← H.vec_zero]
  congr 1
  have : (2 : Fq n) • w = 0 := by rw [h2, zero_smul]
  linear_combination (norm := module) this

theorem vec_comm (w w' : Fin 2 → Fq n) : H.vec w * H.vec w' = H.vec w' * H.vec w := by
  rw [← H.vec_add, ← H.vec_add, add_comm]

end CFSG.CGT.PushingUpLit.T2KR.MData

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}
  {H : MData G L M n} {T' : Subgroup G} {x r b : G} {e₁ e₂ : Fin 2 → Fq n} {ω : Fq n}

section Rel

variable (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω)

include c bs in
theorem Cfg.rel {u : G} (huL : u ∈ L) (hu2 : u * u = 1) (hru : r * u = u * r)
    (hutv : IsTv H e₁ e₂ u ω) (hbu : b * u * b⁻¹ = r * u) :
    Model613.Struct613Rel (H.vec e₁) (H.vec (ω • e₁)) (H.vec e₂) (H.vec (ω • e₂)) x r u b := by
  have hω := bs.ω_eq
  have hω2 : ω * ω = ω + 1 := by linear_combination root_sq hω
  have hrM : r ∈ M := H.le c.r_L
  have huM : u ∈ M := H.le huL
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right c.b_sq
  have hcomm : ∀ w w' : Fin 2 → Fq n, H.vec w * H.vec w' = H.vec w' * H.vec w := H.vec_comm
  have hxcomm : ∀ w : Fin 2 → Fq n, x * H.vec w = H.vec w * x := fun w =>
    H.Q_comm x c.x_Q (H.vec w) (H.blockU_le_QM (H.vec_mem w))
  have hrx : r * x * r⁻¹ = x := by
    calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [← c.xr]
      _ = x := by group
  have hbx : b * x * b⁻¹ = x := by
    calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [← c.xb]
      _ = x := by group
  have hrtv : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  refine
    { sq₀ := H.vec_mul_self _
      sq₁ := H.vec_mul_self _
      sq₂ := H.vec_mul_self _
      sq₃ := H.vec_mul_self _
      c₀₁ := hcomm _ _
      c₀₂ := hcomm _ _
      c₀₃ := hcomm _ _
      c₁₂ := hcomm _ _
      c₁₃ := hcomm _ _
      c₂₃ := hcomm _ _
      xi_sq := c.x_sq
      xi₀ := hxcomm _
      xi₁ := hxcomm _
      xi₂ := hxcomm _
      xi₃ := hxcomm _
      rho_sq := c.r_sq
      u_sq := hu2
      beta_sq := c.b_sq
      rho_u := hru
      rho_beta := c.rb
      beta_u := hbu
      rho₀ := ?_
      rho₁ := ?_
      rho₂ := ?_
      rho₃ := ?_
      rho_xi := hrx
      u₀ := ?_
      u₁ := ?_
      u₂ := ?_
      u₃ := ?_
      u_xi := c.u_conj_x bs huL hu2 hru hutv hbu
      beta₀ := ?_
      beta₁ := ?_
      beta₂ := ?_
      beta₃ := ?_
      beta_xi := hbx }
  · rw [H.conj_vec hrM, bs.r1]
  · rw [H.conj_vec hrM, H.act_smul_L c.r_L, bs.r1]
  · rw [H.conj_vec hrM, bs.r2, H.vec_add]
  · rw [H.conj_vec hrM, H.act_smul_L c.r_L, bs.r2, smul_add, H.vec_add]
  · rw [H.conj_vec huM, hutv.fix]
  · rw [H.conj_vec huM, H.act_smul_L huL, hutv.fix]
  · rw [H.conj_vec huM, hutv.shift, H.vec_add]
  · rw [H.conj_vec huM, H.act_smul_L huL, hutv.shift, smul_add, smul_smul, hω2, ← H.vec_add,
      ← H.vec_add]
    congr 1
    module
  · rw [H.conj_vec c.b_M, bs.b1]
  · rw [H.conj_vec c.b_M, bs.b_semi, bs.b1, ← H.vec_add]
    congr 1
    have : ω ^ 2 = 1 + ω := by linear_combination root_sq hω
    rw [this]
    module
  · rw [H.conj_vec c.b_M, bs.b2]
  · rw [H.conj_vec c.b_M, bs.b_semi, bs.b2, ← H.vec_add]
    congr 1
    have : ω ^ 2 = 1 + ω := by linear_combination root_sq hω
    rw [this]
    module

end Rel

end CFSG.CGT.PushingUpLit.T2KR.P613
