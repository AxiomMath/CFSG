module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6o
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


@[expose] def ctxD (ω x₁ x₂ : G) : Subgroup G := closure {ω, (x₁ * x₂) ^ 2}

@[expose] def ctxSp (t tau x₁ x₂ lam v : G) : Subgroup G :=
  (ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) ⊔ zpowers v

theorem conj_comm_of_cent {q x m : G} (hxq : q * x = x * q) (hmq : m * q = q * m) :
    q * (m * x * m⁻¹) * q⁻¹ = m * x * m⁻¹ := by
  have h1 : q * m * q⁻¹ = m := by rw [hmq.symm]; group
  have h2 : q * x * q⁻¹ = x := by rw [hxq]; group
  have h3 : q * m⁻¹ * q⁻¹ = m⁻¹ := by
    have hminv : q * m⁻¹ = m⁻¹ * q := by
      calc q * m⁻¹ = m⁻¹ * (m * q) * m⁻¹ := by group
        _ = m⁻¹ * (q * m) * m⁻¹ := by rw [hmq]
        _ = m⁻¹ * q := by group
    rw [hminv]; group
  calc q * (m * x * m⁻¹) * q⁻¹
      = (q * m * q⁻¹) * (q * x * q⁻¹) * (q * m⁻¹ * q⁻¹) := by group
    _ = m * x * m⁻¹ := by rw [h1, h2, h3]

section D

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) {ω : G} (hω : ω = tau ∨ ω = t * tau)
include hc hω

theorem mem_ctxD_iff (u : G) : u ∈ ctxD ω x₁ x₂ ↔
    u = 1 ∨ u = ω ∨ u = (x₁ * x₂) ^ 2 ∨ u = ω * (x₁ * x₂) ^ 2 := by
  unfold ctxD
  exact mem_closure_pair_iff (omega_mul_self hc hω) (z_mul_self hc)
    (omega_comm_V hc hω ((x₁ * x₂) ^ 2) (subset_closure (by simp))) u

theorem D_le_N : ctxD ω x₁ x₂ ≤ ctxN ω x₁ x₂ := by
  unfold ctxD ctxN
  apply Subgroup.closure_mono
  intro u hu
  rcases hu with rfl | rfl <;> simp

theorem D_elemAbelian : CFSG.Open.IsElemAbelian 2 (ctxD ω x₁ x₂) := by
  unfold ctxD
  exact elemAbelian_closure_pair (omega_mul_self hc hω) (z_mul_self hc)
    (omega_comm_V hc hω ((x₁ * x₂) ^ 2) (subset_closure (by simp)))

theorem card_D : Nat.card (ctxD ω x₁ x₂) = 4 := by
  unfold ctxD
  refine card_closure_pair (omega_mul_self hc hω) (z_mul_self hc) ?_ ?_ ?_ ?_
  · exact omega_comm_V hc hω ((x₁ * x₂) ^ 2) (subset_closure (by simp))
  · intro h
    exact omega_not_mem_V hc hω (by rw [h]; exact one_mem _)
  · exact z_ne_one hc
  · intro h
    exact omega_not_mem_V hc hω (by rw [h]; exact subset_closure (by simp))

end D

section Classes

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau) {ω : G} (hω : ω = tau ∨ ω = t * tau)
include hc hω

theorem D_tG : ∀ g : G, ∀ d ∈ ctxD ω x₁ x₂, g * t * g⁻¹ ≠ d := by
  rcases hω with rfl | rfl
  · intro g d hd
    exact hc.tG_N g d (D_le_N hc.toCtx4Q (Or.inl rfl) hd)
  · intro g d hd
    exact hc.tG_tN g d (D_le_N hc.toCtx4Q (Or.inr rfl) hd)

theorem D_le_U : ctxD ω x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := by
  unfold ctxD
  rw [closure_le]
  intro u hu
  rcases hu with rfl | rfl
  · rcases hω with rfl | rfl
    · exact mem_sup_left hc.toCtx4Q.tau_mem_O
    · exact mem_sup_left (mul_mem hc.toCtx4Q.t_mem_O hc.toCtx4Q.tau_mem_O)
  · exact mem_sup_left (hc.toCtx4Q.Q_le_O (hc.toCtx4Q.V_le_Q (subset_closure (by simp))))

theorem D_le_CU : ctxD ω x₁ x₂ ≤ ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) := by
  refine le_inf (D_le_U hc hω) ?_
  unfold ctxD
  rw [closure_le]
  intro u hu
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  rcases hu with rfl | rfl
  · exact q_comm_omega hc.toCtx4Q hω
  · exact mul_inv_eq_iff_eq_mul.mp (q_conj_z hc.toCtx4Q)

end Classes

section Conj

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) {ω : G} (hω : ω = tau ∨ ω = t * tau)
include hc hω

theorem conj_omega_of_cent {m : G} (hm : m ∈ ctxM t tau x₁ x₂)
    (hmq : m * (t * lam) = (t * lam) * m) :
    m * ω * m⁻¹ = ω ∨ m * ω * m⁻¹ = ω * (x₁ * x₂) ^ 2 := by
  have hclass : conjIn (ctxM t tau x₁ x₂) ω = ω • (fourGrp x₁ x₂ : Set G) := by
    rcases hω with rfl | rfl
    · exact hc.tauM
    · exact hc.ttauM
  have hmem : m * ω * m⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) ω := ⟨m, hm, rfl⟩
  rw [hclass, Set.mem_smul_set] at hmem
  obtain ⟨a, ha, haeq⟩ := hmem
  have haeq' : m * ω * m⁻¹ = ω * a := by
    rw [smul_eq_mul] at haeq
    exact haeq.symm
  have hωq : (t * lam) * ω = ω * (t * lam) := q_comm_omega hc hω
  have hqa : (t * lam) * a * (t * lam)⁻¹ = a := by
    have h1 : (t * lam) * (ω * a) * (t * lam)⁻¹ = ω * a := by
      rw [← haeq']; exact conj_comm_of_cent hωq hmq
    have h2 : (t * lam) * (ω * a) * (t * lam)⁻¹ =
        ω * ((t * lam) * a * (t * lam)⁻¹) := by
      calc (t * lam) * (ω * a) * (t * lam)⁻¹
          = ((t * lam) * ω) * a * (t * lam)⁻¹ := by group
        _ = (ω * (t * lam)) * a * (t * lam)⁻¹ := by rw [hωq]
        _ = ω * ((t * lam) * a * (t * lam)⁻¹) := by group
    rw [h2] at h1
    exact mul_left_cancel h1
  rcases CV_q hc ha hqa with h | h
  · left; rw [haeq', h, mul_one]
  · right; rw [haeq', h]

theorem conj_z_of_cent {m : G} (hm : m ∈ ctxM t tau x₁ x₂)
    (hmq : m * (t * lam) = (t * lam) * m) : m * (x₁ * x₂) ^ 2 * m⁻¹ = (x₁ * x₂) ^ 2 := by
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hb : m * (x₁ * x₂) ^ 2 * m⁻¹ ∈ fourGrp x₁ x₂ :=
    hc.normal_V.2 m hm ((x₁ * x₂) ^ 2) hzV
  have hqz : (t * lam) * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * (t * lam) :=
    mul_inv_eq_iff_eq_mul.mp (q_conj_z hc)
  have hbq : (t * lam) * (m * (x₁ * x₂) ^ 2 * m⁻¹) * (t * lam)⁻¹ =
      m * (x₁ * x₂) ^ 2 * m⁻¹ := conj_comm_of_cent hqz hmq
  rcases CV_q hc hb hbq with h | h
  · exfalso
    apply z_ne_one hc
    calc (x₁ * x₂) ^ 2 = m⁻¹ * (m * (x₁ * x₂) ^ 2 * m⁻¹) * m := by group
      _ = m⁻¹ * 1 * m := by rw [h]
      _ = 1 := by group
  · exact h

theorem mem_normalizer_D_of_cent {m : G} (hm : m ∈ ctxM t tau x₁ x₂)
    (hmq : m * (t * lam) = (t * lam) * m) :
    ∀ d ∈ ctxD ω x₁ x₂, m * d * m⁻¹ ∈ ctxD ω x₁ x₂ := by
  have hω' := conj_omega_of_cent hc hω hm hmq
  have hz' := conj_z_of_cent hc hω hm hmq
  intro d hd
  have hd' := (mem_ctxD_iff hc hω d).mp hd
  apply (mem_ctxD_iff hc hω (m * d * m⁻¹)).mpr
  rcases hd' with rfl | rfl | rfl | rfl
  · left; group
  · rcases hω' with h | h
    · right; left; exact h
    · right; right; right; exact h
  · right; right; left; exact hz'
  · have hmul : m * (ω * (x₁ * x₂) ^ 2) * m⁻¹ =
        (m * ω * m⁻¹) * (m * (x₁ * x₂) ^ 2 * m⁻¹) := by group
    rw [hmul]
    rcases hω' with h | h <;> rw [h, hz']
    · right; right; right; rfl
    · right; left; rw [mul_assoc, z_mul_self hc, mul_one]

end Conj

end CFSG.OddStandard.SmallF3.HarrisU33.L34
