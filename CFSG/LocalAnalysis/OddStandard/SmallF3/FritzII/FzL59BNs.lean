module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BCl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}

theorem fzl59b_not_conj_s (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hcent : 2 ^ 8 ≤ Nat.card ↥(T₃ ⊓ centralizer ({s} : Set G))) : ¬ IsConj t s := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  let K : Subgroup G := T₃ ⊓ centralizer ({s} : Set G)
  have hKp : IsPGroup 2 K := h.sylow.1.to_le inf_le_left
  have hconj : ∀ q : G, (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
    intro q
    simp [MulAut.conj_apply]
  have hQH : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ invCent t := by
    rintro _ ⟨q, hq, rfl⟩
    have hqs : s * q = q * s := Subgroup.mem_centralizer_iff.mp hq.2 s (Set.mem_singleton s)
    rw [fzl59b_mem_invCent, hconj]
    have ht : t = g⁻¹ * s * g := by rw [← hg]; group
    calc g⁻¹ * q * g * t = g⁻¹ * (q * s) * g := by rw [ht]; group
      _ = g⁻¹ * (s * q) * g := by rw [hqs]
      _ = t * (g⁻¹ * q * g) := by rw [ht]; group
  have hQp : IsPGroup 2 (K.map (MulAut.conj g⁻¹).toMonoidHom) := hKp.map _
  obtain ⟨k, -, hk⟩ := S4A.exists_conj_le_of_isPGroup hQH hQp h.ctx.le_invCent
    h.ctx.isPGroup h.ctx.relIndex_odd
  have hle : K.map (MulAut.conj (k * g⁻¹)).toMonoidHom ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    have e : (MulAut.conj (k * g⁻¹)).toMonoidHom q = k * (g⁻¹ * q * g) * k⁻¹ := by
      show (k * g⁻¹) * q * (k * g⁻¹)⁻¹ = _
      group
    rw [e]
    exact hk _ ⟨q, hq, hconj q⟩
  have hcard : Nat.card (K.map (MulAut.conj (k * g⁻¹)).toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective (fun x y hxy => (MulAut.conj (k * g⁻¹)).injective hxy)
  have h1 : Nat.card K ≤ Nat.card S := hcard ▸ Subgroup.card_le_of_le hle
  rw [h.ctx.card_S, h.card_two] at h1
  have h2 : 2 ^ 8 ≤ 2 ^ 6 * 2 := hcent.trans h1
  norm_num at h2

end CFSG.OddStandard.SmallF3.FritzII
