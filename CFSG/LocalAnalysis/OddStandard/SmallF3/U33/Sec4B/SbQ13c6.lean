module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13c_transport (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) {g : G}
    (hD : ∀ x : G, x ∈ 𝒮 ⊓ centralizer ({t * lam} : Set G) ↔ g⁻¹ * x * g ∈ S) :
    ∀ v ∈ fourGrp x₁ x₂,
      g * v * g⁻¹ ∈ ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G) := by
  classical
  let E₀ : Subgroup G := ctxN tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G)
  let E' : Subgroup G := E₀.map (MulAut.conj g⁻¹).toMonoidHom
  have hE'le : E' ≤ S := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
    have hnN : n ∈ ctxN tau x₁ x₂ := (Subgroup.mem_inf.mp hn).1
    have hnC : n ∈ centralizer ({t * lam} : Set G) := (Subgroup.mem_inf.mp hn).2
    have hnD : n ∈ 𝒮 ⊓ centralizer ({t * lam} : Set G) :=
      ⟨hU (q13b_O_le_U h (q13b_N_le_O h hnN)), hnC⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using (hD n).mp hnD
  have hE'norm : ∀ s ∈ S, ∀ e ∈ E', s * e * s⁻¹ ∈ E' := by
    intro s hs e he
    rcases Subgroup.mem_map.mp he with ⟨n, hn, rfl⟩
    have hnN : n ∈ ctxN tau x₁ x₂ := (Subgroup.mem_inf.mp hn).1
    have hnC : n ∈ centralizer ({t * lam} : Set G) := (Subgroup.mem_inf.mp hn).2
    set d : G := g * s * g⁻¹ with hd
    have hdD : d ∈ 𝒮 ⊓ centralizer ({t * lam} : Set G) := by
      refine (hD d).mpr ?_
      have hgd : g⁻¹ * d * g = s := by rw [hd]; group
      rwa [hgd]
    have hdS : d ∈ 𝒮 := (Subgroup.mem_inf.mp hdD).1
    have hdnN : d * n * d⁻¹ ∈ ctxN tau x₁ x₂ :=
      (hB 𝒮 h𝒮 hU).N_normal.2 d hdS n hnN
    have hdC : d * (t * lam) = (t * lam) * d :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdD).2
    have hnC' : n * (t * lam) = (t * lam) * n :=
      Subgroup.mem_centralizer_singleton_iff.mp hnC
    have hdCinv : d⁻¹ * (t * lam) = (t * lam) * d⁻¹ := by
      calc d⁻¹ * (t * lam) = d⁻¹ * ((t * lam) * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * (t * lam)) * d⁻¹ := by rw [← hdC]
        _ = (t * lam) * d⁻¹ := by group
    have hdnC : d * n * d⁻¹ ∈ centralizer ({t * lam} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (d * n * d⁻¹) * (t * lam) = d * n * (d⁻¹ * (t * lam)) := by group
        _ = d * n * ((t * lam) * d⁻¹) := by rw [hdCinv]
        _ = d * (n * (t * lam)) * d⁻¹ := by group
        _ = d * ((t * lam) * n) * d⁻¹ := by rw [hnC']
        _ = d * (t * lam) * n * d⁻¹ := by group
        _ = (t * lam) * d * n * d⁻¹ := by rw [hdC]
        _ = (t * lam) * (d * n * d⁻¹) := by group
    have hdnE0 : d * n * d⁻¹ ∈ E₀ := Subgroup.mem_inf.mpr ⟨hdnN, hdnC⟩
    refine Subgroup.mem_map.mpr ⟨d * n * d⁻¹, hdnE0, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hd]
    group
  have hE'card : Nat.card E' = 4 := by
    rw [Subgroup.card_map_of_injective (K := E₀)
      (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
    exact q13c_card_N_cent h
  have hE'elem : CFSG.Open.IsElemAbelian 2 E' :=
    (q13c_N_cent_elem h).map (MulAut.conj g⁻¹).toMonoidHom
  have hE'conj : ∀ g' : G, ∀ v ∈ E', g' * t * g'⁻¹ ≠ v := by
    intro g' v hv heq
    rcases Subgroup.mem_map.mp hv with ⟨n, hn, rfl⟩
    have hconj : (g * g') * t * (g * g')⁻¹ = n := by
      have h1 : (g * g') * t * (g * g')⁻¹ = g * (g' * t * g'⁻¹) * g⁻¹ := by group
      rw [h1, heq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact (hB 𝒮 h𝒮 hU).tG_N (g * g') (by rw [hconj]; exact (Subgroup.mem_inf.mp hn).1)
  have hE'eq : E' = fourGrp x₁ x₂ :=
    (h.c11.l45 E' ⟨hE'le, hE'norm⟩ hE'elem hE'card hE'conj).1
  intro v hv
  have hvE' : v ∈ E' := by rw [hE'eq]; exact hv
  rcases Subgroup.mem_map.mp hvE' with ⟨n, hn, hnv⟩
  have hvn : g * v * g⁻¹ = n := by
    rw [← hnv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hvn]
  exact hn

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
