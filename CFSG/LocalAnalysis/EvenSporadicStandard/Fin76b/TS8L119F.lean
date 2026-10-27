module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Case
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

include c

theorem N1_comm_alpha {g : G} (hg : g ∈ c.N1) : g * α = α * g := by
  obtain ⟨-, h2⟩ := c.mem_N1.1 hg
  calc g * α = (g * α * g⁻¹) * g := by group
    _ = α * g := by rw [h2]

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)}

theorem pi_conj_eq_one (hπ : EPi E π) (e : ↥E) : π (MulAut.conj e) = 1 :=
  (hπ.ker _).2 ⟨e, rfl⟩

theorem decomp {m : G} (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G))
    (hmN1 : m ∈ c.N1) :
    ∃ q ∈ c.Qs, ∃ b ∈ B, m = q * b ∨ m = q * b * σ := by
  obtain ⟨f, hf, b, hb, hfb⟩ := c.h.M_eq_FB c.hM c.hα c.hσ hm
  have hbN : b ∈ c.N1 := c.B_le_N1 hb
  have hσN : σ ∈ c.N1 := c.sigma_mem_N1
  have hfN : f ∈ c.N1 := by
    rcases hfb with h1 | h1
    · have e : f = m * b⁻¹ := by
        rw [h1]
        group
      rw [e]
      exact mul_mem hmN1 (inv_mem hbN)
    · have e : f = m * σ⁻¹ * b⁻¹ := by
        rw [h1]
        group
      rw [e]
      exact mul_mem (mul_mem hmN1 (inv_mem hσN)) (inv_mem hbN)
  have hfQ : f ∈ c.Qs := c.mem_Qs.2 ⟨hf, c.N1_comm_alpha hfN⟩
  exact ⟨f, hfQ, b, hb, hfb⟩

theorem pi_qb {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π) {q b : G} (hq : q ∈ c.Qs)
    (hb : b ∈ B) (hm : q * b ∈ c.N1) :
    π (c.rho ⟨q * b, hm⟩).1 = π (c.kappa ⟨b, hb⟩) ∧
      π (c.rho ⟨q * b, hm⟩).2 = π (c.kappa ⟨b, hb⟩) := by
  obtain ⟨e₁, e₂, hq'⟩ := c.rho_Qs_mem hq
  have hsplit : c.rho ⟨q * b, hm⟩ = c.rho ⟨q, c.Qs_le_N1 hq⟩ * c.rho ⟨b, c.B_le_N1 hb⟩ := by
    rw [← map_mul]
    rfl
  have hb' : c.rho ⟨b, c.B_le_N1 hb⟩ = (c.kappa ⟨b, hb⟩, c.kappa ⟨b, hb⟩) := c.rho_B ⟨b, hb⟩
  rw [hsplit, hb', hq']
  constructor
  · show π (MulAut.conj e₁ * c.kappa ⟨b, hb⟩) = _
    rw [map_mul, pi_conj_eq_one c hπ, one_mul]
  · show π (MulAut.conj e₂ * c.kappa ⟨b, hb⟩) = _
    rw [map_mul, pi_conj_eq_one c hπ, one_mul]

theorem pi_qbσ {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π) {q b : G}
    (hq : q ∈ c.Qs) (hb : b ∈ B) (hm : q * b * σ ∈ c.N1) :
    π (c.rho ⟨q * b * σ, hm⟩).1 = π (c.kappa ⟨b, hb⟩) * π (convN ⟨σ, c.hσ.norm_E⟩) ∧
      π (c.rho ⟨q * b * σ, hm⟩).2 = π (c.kappa ⟨b, hb⟩) * π (convN ⟨σ, c.hσ.norm_E⟩) := by
  obtain ⟨e₁, e₂, hq'⟩ := c.rho_Qs_mem hq
  have hsplit : c.rho ⟨q * b * σ, hm⟩ = c.rho ⟨q, c.Qs_le_N1 hq⟩ * c.rho ⟨b, c.B_le_N1 hb⟩ *
      c.rho ⟨σ, c.sigma_mem_N1⟩ := by
    rw [← map_mul, ← map_mul]
    rfl
  have hb' : c.rho ⟨b, c.B_le_N1 hb⟩ = (c.kappa ⟨b, hb⟩, c.kappa ⟨b, hb⟩) := c.rho_B ⟨b, hb⟩
  rw [hsplit, hb', hq', c.rho_sigma]
  constructor
  · show π (MulAut.conj e₁ * c.kappa ⟨b, hb⟩ * convN ⟨σ, c.hσ.norm_E⟩) = _
    rw [map_mul, map_mul, pi_conj_eq_one c hπ, one_mul]
  · show π (MulAut.conj e₂ * c.kappa ⟨b, hb⟩ * convN ⟨σ, c.hσ.norm_E⟩) = _
    rw [map_mul, map_mul, pi_conj_eq_one c hπ, one_mul]

theorem pi_eq_of_mem_M (hπ : EPi E π) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) (hmN1 : m ∈ c.N1) :
    π (c.rho ⟨m, hmN1⟩).1 = π (c.rho ⟨m, hmN1⟩).2 := by
  obtain ⟨q, hq, b, hb, h1 | h1⟩ := c.decomp hm hmN1
  · subst h1
    obtain ⟨h₁, h₂⟩ := c.pi_qb hπ hq hb hmN1
    rw [h₁, h₂]
  · subst h1
    obtain ⟨h₁, h₂⟩ := c.pi_qbσ hπ hq hb hmN1
    rw [h₁, h₂]

theorem mem_Qs_of_inn (hπ : EPi E π) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) (hmN1 : m ∈ c.N1)
    (hinn : (c.rho ⟨m, hmN1⟩).1 ∈ innAutE E) : m ∈ c.Qs := by
  obtain ⟨q, hq, b, hb, h1 | h1⟩ := c.decomp hm hmN1
  · subst h1
    obtain ⟨h₁, -⟩ := c.pi_qb hπ hq hb hmN1
    have h2 : π (c.kappa ⟨b, hb⟩) = 1 := by
      rw [← h₁]
      exact (hπ.ker _).2 hinn
    have hb1 : (⟨b, hb⟩ : ↥B) = 1 := c.eq_one_of_kappa_mem_inn ((hπ.ker _).1 h2)
    have hb2 : b = 1 := by simpa using congrArg Subtype.val hb1
    rw [hb2, mul_one]
    exact hq
  · subst h1
    exfalso
    obtain ⟨h₁, -⟩ := c.pi_qbσ hπ hq hb hmN1
    have h2 : π (c.kappa ⟨b, hb⟩) * π (convN ⟨σ, c.hσ.norm_E⟩) = 1 := by
      rw [← h₁]
      exact (hπ.ker _).2 hinn
    have h3 : π (convN ⟨σ, c.hσ.norm_E⟩) = (π (c.kappa ⟨b, hb⟩))⁻¹ :=
      eq_inv_of_mul_eq_one_right h2
    apply c.pi_sigma_odd hπ
    rw [h3]
    exact inv_mem (c.pi_kappa_mem ⟨b, hb⟩)

theorem mem_Zs_of_rho_one {q : G} (hq : q ∈ c.Qs) (hρ : c.rho ⟨q, c.Qs_le_N1 hq⟩ = 1) :
    q ∈ c.Zs := by
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
  have hzt : z * t * z⁻¹ = t := c.h.z_conj_t
  have hzt' : z⁻¹ * t * z = t := by
    calc z⁻¹ * t * z = z⁻¹ * (z * t * z⁻¹) * z := by rw [hzt]
      _ = t := by group
  have hρ1 : c.rho1 ⟨q, c.Qs_le_N1 hq⟩ = 1 := by
    have h1 := congrArg Prod.fst hρ
    rw [c.rho_fst] at h1
    exact h1
  have hρ2 : c.rho1 (c.zconjN1 ⟨q, c.Qs_le_N1 hq⟩) = 1 := by
    have h1 := congrArg Prod.snd hρ
    rw [c.rho_snd] at h1
    exact h1
  have hW1 : ∀ w ∈ c.W1, q * w * q⁻¹ = w ∨ q * w * q⁻¹ = w * t := by
    intro w hw
    have key2 : c.thetaHom ⟨w, hw⟩ = c.thetaHom (c.conjW1 ⟨q, c.Qs_le_N1 hq⟩ ⟨w, hw⟩) := by
      rw [← c.rho1_theta ⟨q, c.Qs_le_N1 hq⟩ ⟨w, hw⟩, hρ1]
      rfl
    exact (c.thetaHom_eq_iff).1 key2
  have hW2 : ∀ w ∈ c.W2, q * w * q⁻¹ = w ∨ q * w * q⁻¹ = w * t := by
    intro w hw
    have hv : z * w * z⁻¹ ∈ c.W1 := c.z_conj_W2 hw
    have key2 : c.thetaHom ⟨z * w * z⁻¹, hv⟩ =
        c.thetaHom (c.conjW1 (c.zconjN1 ⟨q, c.Qs_le_N1 hq⟩) ⟨z * w * z⁻¹, hv⟩) := by
      rw [← c.rho1_theta (c.zconjN1 ⟨q, c.Qs_le_N1 hq⟩) ⟨z * w * z⁻¹, hv⟩, hρ2]
      rfl
    have e1 : ((c.conjW1 (c.zconjN1 ⟨q, c.Qs_le_N1 hq⟩) ⟨z * w * z⁻¹, hv⟩ : ↥c.W1) : G) =
        z * (q * w * q⁻¹) * z⁻¹ := by
      show z * q * z⁻¹ * (z * w * z⁻¹) * (z * q * z⁻¹)⁻¹ = _
      group
    rcases (c.thetaHom_eq_iff).1 key2 with e | e
    · rw [e1] at e
      dsimp only at e
      left
      calc q * w * q⁻¹ = z⁻¹ * (z * (q * w * q⁻¹) * z⁻¹) * z := by group
        _ = z⁻¹ * (z * w * z⁻¹) * z := by rw [e]
        _ = w := by group
    · rw [e1] at e
      dsimp only at e
      right
      calc q * w * q⁻¹ = z⁻¹ * (z * (q * w * q⁻¹) * z⁻¹) * z := by group
        _ = z⁻¹ * (z * w * z⁻¹ * t) * z := by rw [e]
        _ = w * t := by
          calc z⁻¹ * (z * w * z⁻¹ * t) * z = w * (z⁻¹ * t * z) := by group
            _ = w * t := by rw [hzt']
  have hct : ∀ w ∈ c.Qs, w * t * w⁻¹ = t := fun w hw => by
    rw [← c.Zs_comm_Qs c.t_mem_Zs hw]
    group
  have hcomm : ∀ q' ∈ c.Qs, q * q' * q⁻¹ * q'⁻¹ = 1 ∨ q * q' * q⁻¹ * q'⁻¹ = t := by
    intro q' hq'
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq_prod hq'
    have hw₁Q : w₁ ∈ c.Qs := c.W1_le_Qs hw₁
    have hw₂Q : w₂ ∈ c.Qs := c.W2_le_Qs hw₂
    rcases hW1 w₁ hw₁ with h1 | h1 <;> rcases hW2 w₂ hw₂ with h2 | h2
    · left
      calc q * (w₁ * w₂) * q⁻¹ * (w₁ * w₂)⁻¹ = (q * w₁ * q⁻¹) * (q * w₂ * q⁻¹) * (w₁ * w₂)⁻¹ := by
            group
        _ = 1 := by rw [h1, h2]; group
    · right
      calc q * (w₁ * w₂) * q⁻¹ * (w₁ * w₂)⁻¹ = (q * w₁ * q⁻¹) * (q * w₂ * q⁻¹) * (w₁ * w₂)⁻¹ := by
            group
        _ = t := by
          rw [h1, h2]
          calc w₁ * (w₂ * t) * (w₁ * w₂)⁻¹ = w₁ * ((w₂ * t) * w₂⁻¹) * w₁⁻¹ := by group
            _ = w₁ * t * w₁⁻¹ := by rw [hct w₂ hw₂Q]
            _ = t := hct w₁ hw₁Q
    · right
      calc q * (w₁ * w₂) * q⁻¹ * (w₁ * w₂)⁻¹ = (q * w₁ * q⁻¹) * (q * w₂ * q⁻¹) * (w₁ * w₂)⁻¹ := by
            group
        _ = t := by
          rw [h1, h2]
          calc w₁ * t * w₂ * (w₁ * w₂)⁻¹ = w₁ * (t * w₂) * w₂⁻¹ * w₁⁻¹ := by group
            _ = w₁ * (w₂ * t) * w₂⁻¹ * w₁⁻¹ := by
                rw [← c.Zs_comm_Qs c.t_mem_Zs hw₂Q]
            _ = w₁ * (w₂ * t * w₂⁻¹) * w₁⁻¹ := by group
            _ = w₁ * t * w₁⁻¹ := by rw [hct w₂ hw₂Q]
            _ = t := hct w₁ hw₁Q
    · left
      calc q * (w₁ * w₂) * q⁻¹ * (w₁ * w₂)⁻¹ = (q * w₁ * q⁻¹) * (q * w₂ * q⁻¹) * (w₁ * w₂)⁻¹ := by
            group
        _ = 1 := by
          rw [h1, h2]
          calc w₁ * t * (w₂ * t) * (w₁ * w₂)⁻¹ = w₁ * (t * w₂) * t * w₂⁻¹ * w₁⁻¹ := by group
            _ = w₁ * (w₂ * t) * t * w₂⁻¹ * w₁⁻¹ := by
                rw [← c.Zs_comm_Qs c.t_mem_Zs hw₂Q]
            _ = w₁ * w₂ * (t * t) * w₂⁻¹ * w₁⁻¹ := by group
            _ = w₁ * w₂ * w₂⁻¹ * w₁⁻¹ := by rw [c.h.t_sq, mul_one]
            _ = 1 := by group
  exact c.h.mem_Zg_of_cmt_t c.hα c.hF c.hM c.hp hq hcomm

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
