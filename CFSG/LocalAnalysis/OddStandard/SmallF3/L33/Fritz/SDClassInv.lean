module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDKern

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

theorem eq_t_of_actX_eq_one {i : X} (hi : i ∈ centralizer ({t} : Set X)) (hi1 : i ≠ 1)
    (h : ctx.actX i = 1) : i = t :=
  ((ctx.actX_eq_one_iff hi).mp h).resolve_left hi1

theorem conj_z_of_inner {i : X} (hi : i ∈ centralizer ({t} : Set X)) (hi2 : i ^ 2 = 1)
    (hin : ∃ a : ↥L, ∀ u : ↥L, ctx.actX i u = a * u * a⁻¹) (h1 : ctx.actX i ≠ 1) :
    ∃ g ∈ centralizer ({t} : Set X), g * i * g⁻¹ = ctx.S.z ∨ g * i * g⁻¹ = t * ctx.S.z := by
  obtain ⟨a, ha⟩ := hin
  have hact : ctx.actX i = MulAut.conj a :=
    MulEquiv.ext fun u => by
      simp only [MulAut.conj_apply]
      exact ha u
  have ha2 : a ^ 2 = 1 := ctx.conj_injective (by
    rw [map_pow, map_one, ← hact, pow_two, ← ctx.actX_mul hi hi, ← pow_two, hi2,
      ctx.actX_one])
  have ha1 : a ≠ 1 := by
    intro h
    exact h1 (by rw [hact, h, map_one])
  have hu2 : (ctx.M.F.x ^ 4 : ↥L) ^ 2 = 1 := by
    rw [← pow_mul, show (4 : ℕ) * 2 = 8 from rfl, ctx.M.F.x_pow_eight]
  have hu1 : (ctx.M.F.x ^ 4 : ↥L) ≠ 1 := ctx.M.F.x_pow_four_ne_one
  obtain ⟨l, hl⟩ := isConj_iff.mp (ctx.M.involutions_conj ha2 ha1 hu2 hu1)
  have hg : (l : X) ∈ centralizer ({t} : Set X) := ctx.L_le_centralizer l.2
  have haC : (a : X) ∈ centralizer ({t} : Set X) := ctx.L_le_centralizer a.2
  have hmem : i * (a : X)⁻¹ ∈ centralizer ({t} : Set X) := mul_mem hi (inv_mem haC)
  have hacti : ctx.actX i = ctx.actX (a : X) := by rw [hact, ctx.actX_of_mem_L a]
  have hone : ctx.actX (i * (a : X)⁻¹) = 1 := by
    rw [ctx.actX_mul hi (inv_mem haC), ctx.actX_inv haC, hacti]
    exact mul_inv_cancel _
  rcases (ctx.actX_eq_one_iff hmem).mp hone with hone1 | honet
  · refine ⟨(l : X), hg, Or.inl ?_⟩
    have hi_eq : i = (a : X) := mul_inv_eq_one.mp hone1
    rw [hi_eq]
    change ((l * a * l⁻¹ : ↥L) : X) = ctx.S.z
    rw [hl, ctx.z_eq]
  · refine ⟨(l : X), hg, Or.inr ?_⟩
    have hi_eq : i = t * (a : X) := mul_inv_eq_iff_eq_mul.mp honet
    have hcomm : (l : X) * t = t * (l : X) := mem_centralizer_singleton_iff.mp hg
    rw [hi_eq]
    calc (l : X) * (t * (a : X)) * (l : X)⁻¹
        = (l : X) * t * (a : X) * (l : X)⁻¹ := by group
      _ = t * (l : X) * (a : X) * (l : X)⁻¹ := by rw [hcomm]
      _ = t * ((l : X) * (a : X) * (l : X)⁻¹) := by group
      _ = t * ctx.S.z := by
          congr 1
          change ((l * a * l⁻¹ : ↥L) : X) = ctx.S.z
          rw [hl, ctx.z_eq]

theorem conj_k_of_outer {i : X} (hi : i ∈ centralizer ({t} : Set X)) (hi2 : i ^ 2 = 1)
    (hout : ¬ ∃ a : ↥L, ∀ u : ↥L, ctx.actX i u = a * u * a⁻¹) :
    ∃ g ∈ centralizer ({t} : Set X), g * i * g⁻¹ = ctx.C.k ∨ g * i * g⁻¹ = t * ctx.C.k := by
  have hi2' : (ctx.actX i) ^ 2 = 1 := by
    rw [pow_two, ← ctx.actX_mul hi hi, ← pow_two, hi2, ctx.actX_one]
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (ctx.M.outer_involutions_conj hi2' hout ctx.M.F.k_sq ctx.M.F.k_outer)
  obtain ⟨g, hg, hgc⟩ := ctx.exists_actX_eq c
  rw [← hgc] at hc
  have hgi : g * i * g⁻¹ ∈ centralizer ({t} : Set X) :=
    mul_mem (mul_mem hg hi) (inv_mem hg)
  have hk : ctx.C.k ∈ centralizer ({t} : Set X) := ctx.k_mem_centralizer
  have hact : ctx.actX (g * i * g⁻¹) = ctx.actX ctx.C.k := by
    rw [ctx.actX_mul (mul_mem hg hi) (inv_mem hg), ctx.actX_mul hg hi, ctx.actX_inv hg,
      hc, ctx.actX_k]
  have hmem : (g * i * g⁻¹) * (ctx.C.k)⁻¹ ∈ centralizer ({t} : Set X) :=
    mul_mem hgi (inv_mem hk)
  have hone : ctx.actX ((g * i * g⁻¹) * (ctx.C.k)⁻¹) = 1 := by
    rw [ctx.actX_mul hgi (inv_mem hk), ctx.actX_inv hk, hact]
    exact mul_inv_cancel _
  rcases (ctx.actX_eq_one_iff hmem).mp hone with h1 | h1
  · exact ⟨g, hg, Or.inl (mul_inv_eq_one.mp h1)⟩
  · exact ⟨g, hg, Or.inr (mul_inv_eq_iff_eq_mul.mp h1)⟩

theorem inv_classes : ∀ i ∈ centralizer ({t} : Set X), i ^ 2 = 1 → i ≠ 1 →
    ∃ g ∈ centralizer ({t} : Set X), g * i * g⁻¹ = t ∨ g * i * g⁻¹ = ctx.S.x₀ ^ 2 ∨
      g * i * g⁻¹ = t * ctx.S.x₀ ^ 2 ∨ g * i * g⁻¹ = ctx.C.k ∨ g * i * g⁻¹ = t * ctx.C.k := by
  intro i hi hi2 hi1
  by_cases h1 : ctx.actX i = 1
  · refine ⟨1, one_mem _, Or.inl ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact ctx.eq_t_of_actX_eq_one hi hi1 h1
  by_cases hin : ∃ a : ↥L, ∀ u : ↥L, ctx.actX i u = a * u * a⁻¹
  · obtain ⟨g, hg, h⟩ := ctx.conj_z_of_inner hi hi2 hin h1
    refine ⟨g, hg, ?_⟩
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨g, hg, h⟩ := ctx.conj_k_of_outer hi hi2 hin
    refine ⟨g, hg, ?_⟩
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
