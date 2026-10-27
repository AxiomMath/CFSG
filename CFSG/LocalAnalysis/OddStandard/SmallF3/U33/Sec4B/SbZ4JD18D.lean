module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD18C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD17B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

structure ZJEndInputs (T : H → Prop) (Q V Mc : Subgroup H) (t τ l : H) : Prop
    extends ZJClass T Q t τ l where
  no_abelian : ZJNoAb (l * t)
  e16 : ∀ F : Subgroup H, F ≤ zjVh Mc t τ l → (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) →
    (∀ a ∈ F, a * a = 1) → Nat.card F = 16 → {u : H | u ∈ F ∧ T u}.ncard ≤ 4
  gold : ∃ β ∈ Mc ⊔ closure ({τ, l} : Set H), T β ∧
    Nat.card ↥(zjVh Mc t τ l ⊓ centralizer ({β} : Set H)) = 128
  d17 : ∀ m ∈ Mc, T (m * τ) →
    Nat.card ↥(zjVh Mc t τ l ⊓ centralizer ({m * τ} : Set H)) = 128 →
    17 ≤ {x : H | x ∈ zjVh Mc t τ l ⊓ centralizer ({m * τ} : Set H) ⊓ centralizer (V : Set H) ∧
      x * x = 1}.ncard

private lemma comm_eq_sq {G : Type*} [Group G] {a b : G}
    (hβ : a * b * (a * b) = 1) (hb : b * b = 1) :
    a * b * a⁻¹ * b⁻¹ = a * a := by
  have h2 : b * a * b = a⁻¹ := by
    calc b * a * b = a⁻¹ * (a * b * (a * b)) := by group
      _ = a⁻¹ := by rw [hβ]; group
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc a * b * a⁻¹ * b⁻¹ = a * b * (b * a * b) * b := by rw [h2.symm, hbi]
    _ = a * (b * b) * a * (b * b) := by group
    _ = a * a := by rw [hb]; group

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem zj_end (hb : ZJBound t) {T : H → Prop} (hT : ZJEndInputs T Q V Mc t τ l) : False := by
  obtain ⟨β, hβV, hTβ, hcard⟩ := hT.gold
  have hβ2 : β * β = 1 := (hT.invol β hTβ).1
  obtain ⟨m, hm, hform⟩ := (h.mem_Vq_iff hMh hMc).mp hβV
  rcases hform with h1 | h2 | h3 | h4
  · subst β
    by_cases hmQ : m ∈ Q
    · exact hT.not_Q m hmQ hTβ
    · exact h.no_T_invol_Mc hMh hMc hT.toZJClass hT.e16 hm hmQ hβ2 hTβ
  · subst β
    by_cases hmQ : m ∈ Q
    · exact hT.not_Qtau m hmQ hTβ
    · rcases h.Mc_sq_dichotomy hMh hMc with hA | hB
      · have hcommV : m * τ * m⁻¹ * τ⁻¹ ∈ V := by
          rw [comm_eq_sq hβ2 h.tau_sq]
          exact hA m hm
        exact hmQ ((h.Mc_comm_tau_mem_V_iff hMh hMc hb hm).mp hcommV)
      · by_cases hx : ∃ x ∈ Mc, x ∉ Q ∧ x * x ∈ Q ⊓ centralizer ({t * τ} : Set H)
        · obtain ⟨x, hxMc, hxQ, hxC⟩ := hx
          exact h.not_sq_mem_Cq hMh hMc hb hT.no_abelian hB hm hmQ hβ2 hxMc hxQ hxC
        · have hK : ∀ x ∈ Mc, x ∉ Q → x * x ∉ Q ⊓ centralizer ({t * τ} : Set H) := by
            intro x hxMc hxQ hxC
            exact hx ⟨x, hxMc, hxQ, hxC⟩
          have hle := h.card_inv_D_le hMh hMc hb hB hK hT.toZJClass hm hmQ hβ2 hTβ
          have hge := hT.d17 m hm hTβ hcard
          omega
  · subst β
    set m' : H := l * m * l⁻¹ with hm'def
    have hm' : m' ∈ Mc := by rw [hm'def]; exact h.Mc_conj_l hMh hMc hm
    have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right h.l_sq
    have hs_eq : m * l = l * m' := by
      rw [hm'def]
      rw [show l * (l * m * l⁻¹) = (l * l) * m * l⁻¹ by group, h.l_sq, one_mul, hli]
    have hs2 : l * m' * (l * m') = 1 := by rw [← hs_eq]; exact hβ2
    obtain ⟨w, _hw, hweq⟩ := (h.Mc_fusion_l hMh hMc).1 m' hm' hs2
    exact hT.not_l (by
      have h1 := hT.conj (m * l) w⁻¹ hTβ
      rwa [show w⁻¹ * (m * l) * w⁻¹⁻¹ = l by rw [hs_eq, hweq]; group] at h1)
  · subst β
    set m' : H := (l * τ) * m * (l * τ)⁻¹ with hm'def
    have hm' : m' ∈ Mc := by
      rw [hm'def, show (l * τ) * m * (l * τ)⁻¹ = l * (τ * m * τ⁻¹) * l⁻¹ by group]
      exact h.Mc_conj_l hMh hMc (h.Mc_conj_tau hMh hMc hm)
    have hltau_sq : (l * τ) * (l * τ) = 1 := by
      have hcl : Commute l τ := h.tau_l.symm
      have h1 := hcl.mul_pow 2
      simp only [pow_two] at h1
      rw [h1, h.l_sq, h.tau_sq, mul_one]
    have hs_eq : m * (τ * l) = (l * τ) * m' := by
      rw [hm'def, h.tau_l]
      rw [show (l * τ) * ((l * τ) * m * (l * τ)⁻¹) = m * (l * τ) by
        rw [show (l * τ) * ((l * τ) * m * (l * τ)⁻¹)
            = ((l * τ) * (l * τ)) * m * (l * τ)⁻¹ by group,
          hltau_sq, one_mul, inv_eq_of_mul_eq_one_right hltau_sq]]
    have hs2 : l * τ * m' * (l * τ * m') = 1 := by rw [← hs_eq]; exact hβ2
    obtain ⟨w, _hw, hweq⟩ := (h.Mc_fusion_ltau hMh hMc).1 m' hm' hs2
    exact hT.not_ltau (by
      have h1 := hT.conj (m * (τ * l)) w⁻¹ hTβ
      rwa [show w⁻¹ * (m * (τ * l)) * w⁻¹⁻¹ = l * τ by rw [hs_eq, hweq]; group] at h1)

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
