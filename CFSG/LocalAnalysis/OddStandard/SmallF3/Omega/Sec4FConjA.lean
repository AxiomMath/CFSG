module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FKone
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FK1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FPairType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.conjA_disjoint (h : Sec4FSetup t L S z A B φ) {P : Subgroup G}
    (hPM : P ≤ normalizer (A : Set G)) {g : G} (hg : CFSG.conjugate A g ≤ P)
    (hne : CFSG.conjugate A g ≠ A) {e : G} (he : e ∈ CFSG.conjugate A g)
    (het : ∃ k : G, e = k⁻¹ * t * k) : e ∉ A := by
  intro heA
  obtain ⟨a, ha⟩ := h.exists_pt_of_conj het heA
  have hgeA : g * e * g⁻¹ ∈ A := (mem_conjugate_iff A g e).mp he
  have hgeconj : ∃ k : G, g * e * g⁻¹ = k⁻¹ * t * k := by
    obtain ⟨k, hk⟩ := het
    exact ⟨k * g⁻¹, by rw [hk]; group⟩
  obtain ⟨c₀, hc₀⟩ := h.exists_pt_of_conj hgeconj hgeA
  have hex : ∃ c : Option (Fin 7), g⁻¹ * sec4MPt t φ c * g ∉ A := by
    by_contra hcon
    have hcon' : ∀ c : Option (Fin 7), g⁻¹ * sec4MPt t φ c * g ∈ A := by
      intro c
      by_contra hc
      exact hcon ⟨c, hc⟩
    have hA' : CFSG.conjugate A g =
        Subgroup.closure (Set.range (fun c : Option (Fin 7) => g⁻¹ * sec4MPt t φ c * g)) := by
      have hfun : (fun x : Option (Fin 7) =>
            (MulAut.conj g⁻¹).toMonoidHom (sec4MPt t φ x)) =
          (fun c : Option (Fin 7) => g⁻¹ * sec4MPt t φ c * g) := by
        funext c
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [h.A_eq_closure, CFSG.conjugate, MonoidHom.map_closure, ← Set.range_comp', hfun]
    have hle : CFSG.conjugate A g ≤ A := by
      rw [hA']
      exact (Subgroup.closure_le A).mpr (by rintro x ⟨c, rfl⟩; exact hcon' c)
    have hcard : Nat.card A ≤ Nat.card (CFSG.conjugate A g) := by
      simpa only [CFSG.conjugate] using
        (Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj g⁻¹).toMonoidHom)
          (MulAut.conj g⁻¹).injective).ge
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard)
  obtain ⟨c, hc⟩ := hex
  have he_eq : e = g⁻¹ * sec4MPt t φ c₀ * g := by
    rw [← hc₀]; group
  have hcc : c ≠ c₀ := by
    intro hce
    apply hc
    rw [hce, he_eq.symm]
    exact heA
  have he'A' : g⁻¹ * sec4MPt t φ c * g ∈ CFSG.conjugate A g :=
    (mem_conjugate_iff A g _).mpr (by
      rw [show g * (g⁻¹ * sec4MPt t φ c * g) * g⁻¹ = sec4MPt t φ c by group]
      exact sec4MPt_mem_A h.data c)
  have he'N : g⁻¹ * sec4MPt t φ c * g ∈ normalizer (A : Set G) := hPM (hg he'A')
  have he'conj : ∃ k : G, g⁻¹ * sec4MPt t φ c * g = k⁻¹ * t * k := by
    obtain ⟨k, hk⟩ := (conj_iff_mem_conjClassIn_top (t := t)).mpr (h.pt_mem_conj c)
    exact ⟨k * g, by rw [hk]; group⟩
  rcases h.kcases he'conj he'N with ⟨p, hp⟩ | ⟨a₁, b₁, hab, hσ⟩
  · exact hc (by rw [hp]; exact sec4MPt_mem_A h.data p)
  have hee' : e * (g⁻¹ * sec4MPt t φ c * g) = (g⁻¹ * sec4MPt t φ c * g) * e := by
    calc e * (g⁻¹ * sec4MPt t φ c * g)
        = (g⁻¹ * sec4MPt t φ c₀ * g) * (g⁻¹ * sec4MPt t φ c * g) := by rw [he_eq]
      _ = g⁻¹ * (sec4MPt t φ c₀ * sec4MPt t φ c) * g := by group
      _ = g⁻¹ * (sec4MPt t φ c * sec4MPt t φ c₀) * g := by
            rw [h.A_comm (sec4MPt_mem_A h.data c₀) (sec4MPt_mem_A h.data c)]
      _ = (g⁻¹ * sec4MPt t φ c * g) * (g⁻¹ * sec4MPt t φ c₀ * g) := by group
      _ = (g⁻¹ * sec4MPt t φ c * g) * e := by rw [← he_eq]
  have he'_fix : (g⁻¹ * sec4MPt t φ c * g) * sec4MPt t φ a *
      (g⁻¹ * sec4MPt t φ c * g)⁻¹ = sec4MPt t φ a := by
    rw [← ha, ← hee']
    group
  have hswapfix : Equiv.swap a₁ b₁ a = a := by
    apply h.pt_injective
    rw [← hσ a, he'_fix]
  have hra : a ≠ a₁ := by
    intro haa
    have h1 : Equiv.swap a₁ b₁ a = b₁ := by rw [haa, Equiv.swap_apply_left]
    rw [h1] at hswapfix
    exact hab (hswapfix.trans haa).symm
  have hrb : a ≠ b₁ := by
    intro hab'
    have h1 : Equiv.swap a₁ b₁ a = a₁ := by rw [hab', Equiv.swap_apply_right]
    rw [h1] at hswapfix
    exact hab (hswapfix.trans hab')
  obtain ⟨m, ν, _, hν, hν0, _, _, h6plus⟩ := h.k1_outer he'conj he'N hab hσ hra hrb
  have hmt : m * t * m⁻¹ = e := by
    have h1 := hν none
    rw [h.pt_none, hν0, ← ha] at h1
    exact h1
  have hmem : m⁻¹ * e * m = t := by
    rw [← hmt]; group
  have hk : (g * m)⁻¹ * sec4MPt t φ c₀ * (g * m) = t := by
    rw [← hc₀]
    calc (g * m)⁻¹ * (g * e * g⁻¹) * (g * m) = m⁻¹ * e * m := by group
      _ = t := hmem
  have h6minus : InducesTypeSome L (m⁻¹ * (g⁻¹ * sec4MPt t φ c * g) * m) 7 1 6 (-1) := by
    have hpt := h.pair_type hcc hk
    rwa [show (g * m)⁻¹ * sec4MPt t φ c * (g * m) =
      m⁻¹ * (g⁻¹ * sec4MPt t φ c * g) * m by group] at hpt
  have hcontra :=
    sec4F_type_excl h.omega7 (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) h6plus h6minus
  exact absurd hcontra.2 (by decide)

end CFSG.OddStandard.SmallF3.Omega
