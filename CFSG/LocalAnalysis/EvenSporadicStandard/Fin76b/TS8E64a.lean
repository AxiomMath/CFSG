module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Pi

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

theorem rho1_B (b : ↥B) : c.rho1 ⟨(b : G), c.B_le_N1 b.2⟩ = c.kappa b :=
  congrArg Prod.fst (c.rho_B b)

theorem theta_conj_B (b : ↥B) (w : ↥c.W1) :
    c.thetaHom ⟨(b : G) * w * (b : G)⁻¹, c.N1_W1 (c.B_le_N1 b.2) w.2⟩ =
      c.kappa b (c.thetaHom w) := by
  have h := c.rho1_theta ⟨(b : G), c.B_le_N1 b.2⟩ w
  rw [c.rho1_B] at h
  exact h.symm

theorem theta_mul' {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    (w * w') * (z * (w * w') * z⁻¹) = (w * (z * w * z⁻¹)) * (w' * (z * w' * z⁻¹)) :=
  c.h.theta_mul c.hα c.hF c.hM c.hp hw hw'

theorem theta_eq_iff' {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    w * (z * w * z⁻¹) = w' * (z * w' * z⁻¹) ↔ w' = w ∨ w' = w * t :=
  c.h.theta_eq_iff c.hα c.hF c.hM c.hp hw hw'

theorem theta_conj_B' {b : G} (hb : b ∈ B) (w : G) :
    (b * w * b⁻¹) * (z * (b * w * b⁻¹) * z⁻¹) = b * (w * (z * w * z⁻¹)) * b⁻¹ :=
  theta_conj_of_comm (c.h.BS b hb z c.h.zS) w

theorem B_comm_z {b : G} (hb : b ∈ B) : b * z = z * b := c.h.BS b hb z c.h.zS

theorem B_comm_alpha {b : G} (hb : b ∈ B) : b * α = α * b := c.h.BS b hb α c.hα.mem

theorem W1_comm {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := c.cl
  exact h w hw w' hw'

theorem W1_sq {w : G} (hw : w ∈ c.W1) : w * w = 1 ∨ w * w = α :=
  c.h.sq_W1 c.hF c.hM c.hα c.cl w hw

theorem mem_Zs_of_W1_W2 {w : G} (h1 : w ∈ c.W1) (h2 : w ∈ c.W2) : w ∈ c.Zs :=
  c.h.W1_inf_W2 c.hα h1 h2

theorem z_conj_alpha : z * α * z⁻¹ = α * t := c.h.z_conj_alpha c.hα

theorem z_conj_t : z * t * z⁻¹ = t := c.h.z_conj_t

theorem t_comm_Qs {q : G} (hq : q ∈ c.Qs) : t * q = q * t :=
  c.Zs_comm_Qs c.t_mem_Zs hq

section KleinKappa

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)}

theorem klein_kappa {b₁ b₂ : G} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h11 : b₁ * b₁ = 1)
    (h22 : b₂ * b₂ = 1) (h12 : b₁ * b₂ = b₂ * b₁) (h1 : b₁ ≠ 1) (h2 : b₂ ≠ 1) (h3 : b₁ ≠ b₂) :
    BInv E π (c.kappa ⟨b₁, hb₁⟩) ∧ BInv E π (c.kappa ⟨b₂, hb₂⟩) ∧
      c.kappa ⟨b₁, hb₁⟩ * c.kappa ⟨b₂, hb₂⟩ = c.kappa ⟨b₂, hb₂⟩ * c.kappa ⟨b₁, hb₁⟩ ∧
      c.kappa ⟨b₁, hb₁⟩ ≠ c.kappa ⟨b₂, hb₂⟩ ∧
      c.kappa ⟨b₁, hb₁⟩ * c.kappa ⟨b₂, hb₂⟩ ∉ innAutE E := by
  have hsq : ∀ (b : G) (hb : b ∈ B), b * b = 1 → c.kappa ⟨b, hb⟩ * c.kappa ⟨b, hb⟩ = 1 := by
    intro b hb hbb
    rw [← map_mul, ← map_one c.kappa]
    congr 1
    exact Subtype.ext hbb
  have hinn : ∀ (b : G) (hb : b ∈ B), b ≠ 1 → c.kappa ⟨b, hb⟩ ∉ innAutE E := by
    intro b hb hb1 hin
    exact hb1 (congrArg Subtype.val (c.eq_one_of_kappa_mem_inn (b := ⟨b, hb⟩) hin))
  refine ⟨⟨hsq b₁ hb₁ h11, c.pi_kappa_mem ⟨b₁, hb₁⟩, hinn b₁ hb₁ h1⟩,
    ⟨hsq b₂ hb₂ h22, c.pi_kappa_mem ⟨b₂, hb₂⟩, hinn b₂ hb₂ h2⟩, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h12
  · intro h
    exact h3 (congrArg Subtype.val (c.kappa_injective h))
  · intro hin
    rw [← map_mul] at hin
    have := congrArg Subtype.val (c.eq_one_of_kappa_mem_inn (b := ⟨b₁, hb₁⟩ * ⟨b₂, hb₂⟩) hin)
    have h4 : b₁ * b₂ = 1 := this
    apply h3
    calc b₁ = b₁ * (b₂ * b₂) := by rw [h22, mul_one]
      _ = (b₁ * b₂) * b₂ := by group
      _ = b₂ := by rw [h4, one_mul]

end KleinKappa

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
