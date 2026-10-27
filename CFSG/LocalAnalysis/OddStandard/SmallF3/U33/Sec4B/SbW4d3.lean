module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_conj_conj {x y u r : G} (hr : r * x = x * r) (h : u * x * u⁻¹ = y) :
    (r * u * r⁻¹) * x * (r * u * r⁻¹)⁻¹ = r * y * r⁻¹ := by
  have hr' : r⁻¹ * x * r = x := by
    calc r⁻¹ * x * r = r⁻¹ * (x * r) := by group
      _ = r⁻¹ * (r * x) := by rw [hr]
      _ = x := by group
  calc (r * u * r⁻¹) * x * (r * u * r⁻¹)⁻¹ = r * (u * (r⁻¹ * x * r) * u⁻¹) * r⁻¹ := by group
    _ = r * (u * x * u⁻¹) * r⁻¹ := by rw [hr']
    _ = r * y * r⁻¹ := by rw [h]

theorem w4_conj_mul {p b r : G} (hr : r * p = p * r) : r * (p * b) * r⁻¹ = p * (r * b * r⁻¹) := by
  calc r * (p * b) * r⁻¹ = (r * p) * b * r⁻¹ := by group
    _ = (p * r) * b * r⁻¹ := by rw [hr]
    _ = p * (r * b * r⁻¹) := by group

theorem w4_inv_comm {r x : G} (h : r * x = x * r) : r⁻¹ * x = x * r⁻¹ := by
  calc r⁻¹ * x = r⁻¹ * (x * r) * r⁻¹ := by group
    _ = r⁻¹ * (r * x) * r⁻¹ := by rw [h]
    _ = x * r⁻¹ := by group

theorem w4_step {g a b r : G} (hrt : r * t = t * r) (hrτ : r * tau = tau * r)
    (hgt : g * t * g⁻¹ = t * a) (hgτ : g * tau * g⁻¹ = t * tau * b) :
    (r * g * r⁻¹) * t * (r * g * r⁻¹)⁻¹ = t * (r * a * r⁻¹) ∧
      (r * g * r⁻¹) * tau * (r * g * r⁻¹)⁻¹ = t * tau * (r * b * r⁻¹) := by
  have hrtτ : r * (t * tau) = (t * tau) * r := by
    calc r * (t * tau) = (r * t) * tau := by group
      _ = (t * r) * tau := by rw [hrt]
      _ = t * (r * tau) := by group
      _ = t * (tau * r) := by rw [hrτ]
      _ = (t * tau) * r := by group
  refine ⟨?_, ?_⟩
  · rw [w4_conj_conj hrt hgt, w4_conj_mul hrt]
  · rw [w4_conj_conj hrτ hgτ, w4_conj_mul hrtτ]

theorem w4_triple_t {g g₁ g₂ a a₁ a₂ : G} (hgt : g * t * g⁻¹ = t * a)
    (hg₁t : g₁ * t * g₁⁻¹ = t * a₁) (hg₂t : g₂ * t * g₂⁻¹ = t * a₂)
    (hg₁a₂ : g₁ * a₂ * g₁⁻¹ = a₂) (hga₁ : g * a₁ * g⁻¹ = a₁) (hga₂ : g * a₂ * g⁻¹ = a₂) :
    (g * g₁ * g₂) * t * (g * g₁ * g₂)⁻¹ = t * (a * a₁ * a₂) := by
  calc (g * g₁ * g₂) * t * (g * g₁ * g₂)⁻¹
      = g * (g₁ * (g₂ * t * g₂⁻¹) * g₁⁻¹) * g⁻¹ := by group
    _ = g * (g₁ * (t * a₂) * g₁⁻¹) * g⁻¹ := by rw [hg₂t]
    _ = g * ((g₁ * t * g₁⁻¹) * (g₁ * a₂ * g₁⁻¹)) * g⁻¹ := by group
    _ = g * ((t * a₁) * a₂) * g⁻¹ := by rw [hg₁t, hg₁a₂]
    _ = (g * t * g⁻¹) * (g * a₁ * g⁻¹) * (g * a₂ * g⁻¹) := by group
    _ = (t * a) * a₁ * a₂ := by rw [hgt, hga₁, hga₂]
    _ = t * (a * a₁ * a₂) := by group

theorem w4_triple_tau {g g₁ g₂ a₁ b b₁ b₂ : G} (hgτ : g * tau * g⁻¹ = t * tau * b)
    (hg₁t : g₁ * t * g₁⁻¹ = t * a₁) (hg₁τ : g₁ * tau * g₁⁻¹ = t * tau * b₁)
    (hg₂τ : g₂ * tau * g₂⁻¹ = t * tau * b₂) (hg₁b₂ : g₁ * b₂ * g₁⁻¹ = b₂)
    (hga₁ : g * a₁ * g⁻¹ = a₁) (hgb₁ : g * b₁ * g⁻¹ = b₁) (hgb₂ : g * b₂ * g⁻¹ = b₂)
    (ht2 : t * t = 1) (ha₁t : a₁ * t = t * a₁) (ha₁τ : a₁ * tau = tau * a₁) :
    (g * g₁ * g₂) * tau * (g * g₁ * g₂)⁻¹ = t * tau * (b * a₁ * b₁ * b₂) := by
  have hmid : (t * a₁) * (t * tau * b₁) * b₂ = tau * (a₁ * b₁ * b₂) := by
    calc (t * a₁) * (t * tau * b₁) * b₂ = t * (a₁ * t) * tau * b₁ * b₂ := by group
      _ = t * (t * a₁) * tau * b₁ * b₂ := by rw [ha₁t]
      _ = (t * t) * a₁ * tau * b₁ * b₂ := by group
      _ = a₁ * tau * b₁ * b₂ := by rw [ht2, one_mul]
      _ = tau * a₁ * b₁ * b₂ := by rw [ha₁τ]
      _ = tau * (a₁ * b₁ * b₂) := by group
  calc (g * g₁ * g₂) * tau * (g * g₁ * g₂)⁻¹
      = g * (g₁ * (g₂ * tau * g₂⁻¹) * g₁⁻¹) * g⁻¹ := by group
    _ = g * (g₁ * (t * tau * b₂) * g₁⁻¹) * g⁻¹ := by rw [hg₂τ]
    _ = g * ((g₁ * t * g₁⁻¹) * (g₁ * tau * g₁⁻¹) * (g₁ * b₂ * g₁⁻¹)) * g⁻¹ := by group
    _ = g * ((t * a₁) * (t * tau * b₁) * b₂) * g⁻¹ := by rw [hg₁t, hg₁τ, hg₁b₂]
    _ = g * (tau * (a₁ * b₁ * b₂)) * g⁻¹ := by rw [hmid]
    _ = (g * tau * g⁻¹) * (g * a₁ * g⁻¹) * (g * b₁ * g⁻¹) * (g * b₂ * g⁻¹) := by group
    _ = (t * tau * b) * a₁ * b₁ * b₂ := by rw [hgτ, hga₁, hgb₁, hgb₂]
    _ = t * tau * (b * a₁ * b₁ * b₂) := by group

theorem w4_O_conj_tau
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxO t tau x₁ x₂) : g * tau * g⁻¹ ∈ tau • (fourGrp x₁ x₂ : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hc0 : Ctx0 t L S x₁ x₂ lam rho := hc4.toCtx0
  have hca : W4Ctxa t L S x₁ x₂ lam rho tau := hc.toW4Ctxa
  have hgM : g ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hg
  rcases w4_conj_tau_cases hca hgM with h | h
  · exact h
  exfalso
  obtain ⟨b, hb, hbe⟩ := Set.mem_smul_set.mp h
  obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp (w4_conj_t_mem hc.toW4Ctx0 hgM)
  simp only [smul_eq_mul] at hbe hae
  have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc4).2.2.2.2.1
  have hρM' : rho⁻¹ ∈ ctxM t tau x₁ x₂ := inv_mem hρM
  have hρt := w4_rho_t hc4
  have hρτ := w4_rho_tau hc4
  have s1 := w4_step hρt hρτ hae.symm hbe.symm
  have s2 := w4_step (w4_inv_comm hρt) (w4_inv_comm hρτ) hae.symm hbe.symm
  have hnO := (p0_normal_O t tau x₁ x₂).2
  have hg₁O := hnO rho hρM g hg
  have hg₂O := hnO rho⁻¹ hρM' g hg
  have hnV := hc.normal_V.2
  have ha₁ := hnV rho hρM a ha
  have ha₂ := hnV rho⁻¹ hρM' a ha
  have hb₁ := hnV rho hρM b hb
  have hb₂ := hnV rho⁻¹ hρM' b hb
  have hT := w4_triple_t hae.symm s1.1 s2.1 (w4_O_cent_V hc hg₁O ha₂) (w4_O_cent_V hc hg ha₁)
    (w4_O_cent_V hc hg ha₂)
  have hτ := w4_triple_tau hbe.symm s1.1 s1.2 s2.2 (w4_O_cent_V hc hg₁O hb₂)
    (w4_O_cent_V hc hg ha₁) (w4_O_cent_V hc hg hb₁) (w4_O_cent_V hc hg hb₂)
    (S4A.t_mul_self hc4.hyp) (w4_t_comm_V hc4 ha₁).symm (w4_tau_comm_V hc4 ha₁).symm
  have hna : a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho⁻¹⁻¹) = 1 := by
    rw [inv_inv]; exact w4_rho_norm hca ha
  have hnb : b * (rho * b * rho⁻¹) * (rho⁻¹ * b * rho⁻¹⁻¹) = 1 := by
    rw [inv_inv]; exact w4_rho_norm hca hb
  have hfin : b * (rho * a * rho⁻¹) * (rho * b * rho⁻¹) * (rho⁻¹ * b * rho⁻¹⁻¹) =
      rho * a * rho⁻¹ := by
    calc b * (rho * a * rho⁻¹) * (rho * b * rho⁻¹) * (rho⁻¹ * b * rho⁻¹⁻¹)
        = (rho * a * rho⁻¹) * (b * (rho * b * rho⁻¹) * (rho⁻¹ * b * rho⁻¹⁻¹)) := by
          rw [w4_V_comm hc0 hb ha₁]; group
      _ = rho * a * rho⁻¹ := by rw [hnb, mul_one]
  rw [hna, mul_one] at hT
  rw [hfin] at hτ
  have hhO : g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹) ∈ ctxO t tau x₁ x₂ :=
    mul_mem (mul_mem hg hg₁O) hg₂O
  have hhC : g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹) ∈ centralizer ({t} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹)) * t
        = ((g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹)) * t *
            (g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹))⁻¹) *
          (g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹)) := by group
      _ = t * (g * (rho * g * rho⁻¹) * (rho⁻¹ * g * rho⁻¹⁻¹)) := by rw [hT]
  have hhK := w4_CMt_le_Ktau hca ⟨p0_O_le_M t tau x₁ x₂ hhO, hhC⟩
  obtain ⟨v, hv, hve⟩ := Set.mem_smul_set.mp hhK.2
  simp only [smul_eq_mul] at hve
  rw [hτ] at hve
  have hvt : v = t * (rho * a * rho⁻¹) := by
    refine mul_left_cancel (a := tau) ?_
    calc tau * v = t * tau * (rho * a * rho⁻¹) := hve
      _ = (tau * t) * (rho * a * rho⁻¹) := by rw [w4_t_comm_tau hc4]
      _ = tau * (t * (rho * a * rho⁻¹)) := by group
  have htV : t ∈ fourGrp x₁ x₂ := by
    have : t = v * (rho * a * rho⁻¹)⁻¹ := by rw [hvt]; group
    rw [this]
    exact mul_mem hv (inv_mem ha₁)
  exact l12_t_not_mem_N hc4 ((p0_V_le_N_le_X t tau x₁ x₂).1 htV)

theorem w4_O_le_Ktau
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ ≤ w4Ktau tau x₁ x₂ := fun g hg =>
  ⟨w4_mem_normalizer_V hc.normal_V (p0_O_le_M t tau x₁ x₂ hg), w4_O_conj_tau hc hg⟩

theorem w4_M_le_Ktau
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ≤ w4Ktau tau x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨-, -, -, -, hρM, hlamM⟩ := p0_gens_mem_M hc4
  rw [hc.M_eq]
  refine sup_le (w4_O_le_Ktau hc.toW4Ctxb) ?_
  rw [Subgroup.closure_le]
  intro x hx
  rcases (by simpa using hx) with rfl | rfl
  · exact w4_mem_Ktau_of_comm (w4_mem_normalizer_V hc.normal_V hρM) hc4.tau_rho.symm
  · exact w4_mem_Ktau_of_comm (w4_mem_normalizer_V hc.normal_V hlamM) hc4.tau_lam.symm

theorem w4_conj_tau_mem
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) : g * tau * g⁻¹ ∈ tau • (fourGrp x₁ x₂ : Set G) :=
  (w4_M_le_Ktau hc hg).2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
