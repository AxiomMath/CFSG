module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cop
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem k18_comm_Xi_R (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ ctxXi t tau x₁ x₂ rho, ∀ r ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G),
      g * r * g⁻¹ * r⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hQK : ∀ k ∈ ctxK t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      k * q * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun k hk q hq => hc.normal_Q_K.2 k hk q hq
  have hNK : ∀ k ∈ ctxK t tau x₁ x₂ rho,
      ∀ n ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G),
      k * n * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) := by
    intro k hk n hn
    have hk' : k ∈ Subgroup.normalizer
        (((ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) : Subgroup G) : Set G) := by
      simpa only [ctxK] using hk
    exact (Subgroup.mem_normalizer_iff.mp hk' n).mp hn
  have hXK : closure ({t, tau} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (l17_mem_K hc).1
    · exact (l17_mem_K hc).2.1
  have hnormXQ : ∀ k ∈ closure ({t, tau} : Set G), ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      k * q * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun k hk q hq => hc.normal_Q_K.2 k (hXK hk) q hq
  have hNprod : ∀ n ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G),
      ∃ q ∈ ctxQ t tau x₁ x₂ rho, ∃ x ∈ closure ({t, tau} : Set G), n = q * x :=
    fun n hn => (mem_sup_iff_of_normalizes hnormXQ).mp hn
  have hXcent : closure ({t, tau} : Set G) ≤ centralizer ({rho} : Set G) := by
    rw [← hc.CR_rho]; exact inf_le_right
  have hρX : ∀ x ∈ closure ({t, tau} : Set G), rho * x = x * rho :=
    fun x hx => (Subgroup.mem_centralizer_iff.mp (hXcent hx)) rho (by simp)
  have hmain := comm_mem_of_sup_centralized (K := ctxK t tau x₁ x₂ rho)
    (N := ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G))
    (Q := ctxQ t tau x₁ x₂ rho) (X := closure ({t, tau} : Set G))
    hρK hQK hNK hNprod hρX
  intro g hg r hr
  exact hmain g (Subgroup.commutator_mono (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁)
    (x₂ := x₂) (rho := rho)).1 le_rfl hg) r hr

theorem k18A_comm_Xi_C (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ g ∈ ctxXi t tau x₁ x₂ rho, ∀ r ∈ ctxCY t tau x₁ x₂ rho,
      g * r * g⁻¹ * r⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hc13 := hc.toCtx13
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc13).2.2.2.2
  have hQK : ∀ k ∈ ctxK t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      k * q * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc13.normal_Q_K.2
  have hNK : ∀ k ∈ ctxK t tau x₁ x₂ rho, ∀ n ∈ ctxCY t tau x₁ x₂ rho,
      k * n * k⁻¹ ∈ ctxCY t tau x₁ x₂ rho := (l18_C_normal hc13).2
  have hXK : closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (l17_mem_K hc13).2.1
    · exact (l17_mem_K hc13).2.2.1
  have hnormXQ : ∀ k ∈ closure ({tau, om} : Set G), ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      k * q * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun k hk q hq => hc13.normal_Q_K.2 k (hXK hk) q hq
  have hNprod : ∀ n ∈ ctxCY t tau x₁ x₂ rho,
      ∃ q ∈ ctxQ t tau x₁ x₂ rho, ∃ x ∈ closure ({tau, om} : Set G), n = q * x := by
    intro n hn
    rw [k18A_C_eq hc] at hn
    exact (mem_sup_iff_of_normalizes hnormXQ).mp hn
  have hXcent : closure ({tau, om} : Set G) ≤ centralizer ({rho} : Set G) := by
    rw [← l18_C_cap_cent_rho hc13]; exact inf_le_right
  have hρX : ∀ x ∈ closure ({tau, om} : Set G), rho * x = x * rho :=
    fun x hx => (Subgroup.mem_centralizer_iff.mp (hXcent hx)) rho (by simp)
  have hmain := comm_mem_of_sup_centralized (K := ctxK t tau x₁ x₂ rho)
    (N := ctxCY t tau x₁ x₂ rho)
    (Q := ctxQ t tau x₁ x₂ rho) (X := closure ({tau, om} : Set G))
    hρK hQK hNK hNprod hρX
  intro g hg r hr
  exact hmain g (Subgroup.commutator_mono (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁)
    (x₂ := x₂) (rho := rho)).1 le_rfl hg) r hr

theorem k18_Xi_norm_B (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ ctxXi t tau x₁ x₂ rho, ∀ b ∈ baseGrp x₁ x₂, g * b * g⁻¹ ∈ baseGrp x₁ x₂ := by
  intro g hg b hb
  have hB : baseGrp x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
    ((l12_a hc.toCtx11).2.2.1).symm
  have hgK : g ∈ ctxK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1
      (l18_Xi_le_OK hc hg)
  have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp (hB ▸ hb)).1
  have hbcent : b ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp (hB ▸ hb)).2
  set b' : G := g * b * g⁻¹ with hb'def
  set q : G := g * t * g⁻¹ * t⁻¹ with hqdef
  have hb'Q : b' ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hb'def]
    exact hc.normal_Q_K.2 g hgK b hbQ
  have hqQ : q ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hqdef]
    exact k18_comm_Xi_R hc g hg t
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hqeq : g * t * g⁻¹ = q * t := by
    rw [hqdef]; group
  have hbt : t * b = b * t := (Subgroup.mem_centralizer_iff.mp hbcent) t rfl
  have hconj : b' * (g * t * g⁻¹) = (g * t * g⁻¹) * b' := by
    rw [hb'def]
    calc (g * b * g⁻¹) * (g * t * g⁻¹) = g * (b * t) * g⁻¹ := by group
      _ = g * (t * b) * g⁻¹ := by rw [hbt]
      _ = (g * t * g⁻¹) * (g * b * g⁻¹) := by group
  rw [hqeq] at hconj
  have hb'q : b' * q = q * b' := IsZ4Z4E4.comm hc.q_iso hb'Q hqQ
  have hfin : b' * t = t * b' := by
    have h1 : b' * q * t = q * t * b' := by
      calc b' * q * t = b' * (q * t) := by group
        _ = (q * t) * b' := hconj
        _ = q * t * b' := by group
    rw [hb'q] at h1
    have h2 : q * (b' * t) = q * (t * b') := by
      calc q * (b' * t) = q * b' * t := by group
        _ = q * t * b' := h1
        _ = q * (t * b') := by group
    exact mul_left_cancel h2
  have hb'cent : b' ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hfin.symm
  rw [hB]
  exact Subgroup.mem_inf.mpr ⟨hb'Q, hb'cent⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
