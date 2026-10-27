module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeTransfer

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem normalizer_E_le_centralizer [Finite G] :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ centralizer ({t} : Set G) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  by_contra hgt
  obtain ⟨v, hv⟩ := hS.conj_t_eq hg
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hgt
    rw [hS.rad.ψ_zero, mul_one] at hv
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hv]
  have hvZ : v ∈ Zset t Q ψ := ⟨g, hg, hv⟩
  by_cases hN : ∃ w ∈ Zset t Q ψ, qfV ε w = 1
  · obtain ⟨w, hwZ, hw⟩ := hN
    have hallN : ∀ u, qfV ε u = 1 → u ∈ Zset t Q ψ := fun u hu =>
      hS.mem_Zset_of (ne_zero_of_qfV_eq_one hw) (ne_zero_of_qfV_eq_one hu) (hw.trans hu.symm) hwZ
    by_cases hSg : ∃ s ∈ Zset t Q ψ, s ≠ 0 ∧ qfV ε s = 0
    · obtain ⟨s, hsZ, hs0, hs⟩ := hSg
      refine hS.false_of_Zset_univ fun u => ?_
      by_cases hu : u = 0
      · exact hu ▸ hS.zero_mem_Zset
      · rcases qfV_cases ε u with h | h
        · exact hS.mem_Zset_of hs0 hu (hs.trans h.symm) hsZ
        · exact hallN u h
    · refine hS.false_of_Zset_nonsing fun u => ⟨fun hu => ?_, fun hu => ?_⟩
      · by_cases h0 : u = 0
        · exact Or.inl h0
        · rcases qfV_cases ε u with h | h
          · exact absurd ⟨u, hu, h0, h⟩ hSg
          · exact Or.inr h
      · rcases hu with rfl | h
        · exact hS.zero_mem_Zset
        · exact hallN u h
  · have hvs : qfV ε v = 0 := (qfV_cases ε v).resolve_right fun h => hN ⟨v, hvZ, h⟩
    refine hS.false_of_Zset_zeroSet fun u => ⟨fun hu => ?_, fun hu => ?_⟩
    · exact (qfV_cases ε u).resolve_right fun h => hN ⟨u, hu, h⟩
    · by_cases h0 : u = 0
      · exact h0 ▸ hS.zero_mem_Zset
      · exact hS.mem_Zset_of hv0 h0 (hvs.trans hu.symm) hvZ

theorem false_of_setting [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) : False := by
  obtain ⟨n, hnN, hnt, hna⟩ := hS.exists_conj_eq_mul hG hnab
  set E : Subgroup G := Q ⊔ zpowers t with hEdef
  set E' : Subgroup G := E.map (MulAut.conj n).toMonoidHom with hE'def
  have hmemE' : ∀ {x : G}, x ∈ E' ↔ ∃ e ∈ E, n * e * n⁻¹ = x := by
    intro x
    simp only [hE'def, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hE'TH : ∀ x ∈ E', x ∈ U ⊔ zpowers c := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hmemE'.1 hx
    exact (mem_normalizer_iff.1 hnN e).1 (hS.E_le_TH he)
  have hE'K : ∀ x ∈ E', x ∈ U ⊔ zpowers t := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hmemE'.1 hx
    refine hS.mem_K_of_mul_self (hE'TH _ hx) ?_
    calc n * e * n⁻¹ * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
      _ = 1 := by rw [hS.E_mul_self he]; group
  have htE' : t ∈ E' := by
    refine hmemE'.2 ⟨t * a, mul_mem t_mem_E (mem_sup_left hS.rad.a_mem_Q), ?_⟩
    calc n * (t * a) * n⁻¹ = (n * t * n⁻¹) * (n * a * n⁻¹) := by group
      _ = t * a * a := by rw [hnt, hna]
      _ = t := by rw [mul_assoc, hS.rad.Q_mul_self hS.rad.a_mem_Q, mul_one]
  set A' : Subgroup G := E' ⊓ U with hA'def
  have hrel : A'.relIndex E' = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨t, htE', fun b hb => ?_⟩
    have htU : ∀ u ∈ U, u * t ∉ U := fun u hu h =>
      hS.shape.not_mem (hS.U_le_L (by simpa using mul_mem (inv_mem hu) h))
    obtain ⟨u, hu, h | h⟩ := (hS.shape.mem_sup_iff hS.U_le_L).1 (hE'K b hb)
    · rw [h] at hb ⊢
      exact Or.inr ⟨Subgroup.mem_inf.2 ⟨hb, hu⟩, fun h' => htU u hu (Subgroup.mem_inf.1 h').2⟩
    · rw [h] at hb ⊢
      refine Or.inl ⟨Subgroup.mem_inf.2 ⟨mul_mem hb htE', ?_⟩,
        fun h' => htU u hu (Subgroup.mem_inf.1 h').2⟩
      rw [mul_assoc, hS.shape.mul_self, mul_one]
      exact hu
  have hcardE' : Nat.card E' = 128 := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj n).injective, hS.card_E]
  have hcardA' : Nat.card A' = 64 := by
    have h := Subgroup.relIndex_mul_card (H := A') (K := E')
    rw [hrel, inf_of_le_left (show A' ≤ E' from inf_le_left), hcardE'] at h
    omega
  have hA'norm : ∀ u ∈ U, ∀ x ∈ A', u * x * u⁻¹ ∈ A' := by
    intro u hu x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, mul_mem (mul_mem hu hx.2) (inv_mem hu)⟩
    obtain ⟨e, he, hex⟩ := hmemE'.1 hx.1
    rw [← hex]
    have hu' : n⁻¹ * u * n ∈ U ⊔ zpowers c := by
      have := (mem_normalizer_iff.1 (inv_mem hnN) u).1 (mem_sup_left hu)
      simpa using this
    have he' := (mem_normalizer_iff.1 (hS.TH_le_normalizer_E hu') e).1 he
    refine hmemE'.2 ⟨_, he', ?_⟩
    group
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := hmemE'.1 hx.1
    obtain ⟨f, hf, rfl⟩ := hmemE'.1 hy.1
    calc n * e * n⁻¹ * (n * f * n⁻¹) = n * (e * f) * n⁻¹ := by group
      _ = n * (f * e) * n⁻¹ := by rw [hS.E_comm he hf]
      _ = n * f * n⁻¹ * (n * e * n⁻¹) := by group
  have hA'sq : ∀ x ∈ A', x * x = 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hmemE'.1 hx.1
    calc n * e * n⁻¹ * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
      _ = 1 := by rw [hS.E_mul_self he]; group
  obtain ⟨l, hlL, hlA, hla⟩ :=
    hS.rad.S5 A' inf_le_right hA'norm hA'comm hA'sq hcardA'
  have hlt : l * t = t * l := hS.shape.commute_of_mem hlL
  have hlE' : ∀ x ∈ E', l * x * l⁻¹ ∈ E' := by
    intro x hx
    obtain ⟨u, hu, h | h⟩ := (hS.shape.mem_sup_iff hS.U_le_L).1 (hE'K x hx)
    · rw [h] at hx ⊢
      exact (hlA u ⟨hx, hu⟩).1
    · have huE' : u ∈ E' := by
        have := mul_mem hx htE'
        rwa [h, mul_assoc, hS.shape.mul_self, mul_one] at this
      rw [h, show l * (u * t) * l⁻¹ = (l * u * l⁻¹) * (l * t * l⁻¹) by group, hlt,
        mul_inv_cancel_right]
      exact mul_mem (hlA u ⟨huE', hu⟩).1 htE'
  have hmE : n⁻¹ * l * n ∈ normalizer (E : Set G) := by
    refine mem_normalizer_of_conj_mem fun e he => ?_
    obtain ⟨f, hf, hfe⟩ := hmemE'.1 (hlE' _ (hmemE'.2 ⟨e, he, rfl⟩))
    have h : n⁻¹ * l * n * e * (n⁻¹ * l * n)⁻¹ = f := by
      calc n⁻¹ * l * n * e * (n⁻¹ * l * n)⁻¹ = n⁻¹ * (l * (n * e * n⁻¹) * l⁻¹) * n := by group
        _ = n⁻¹ * (n * f * n⁻¹) * n := by rw [hfe]
        _ = f := by group
    rw [h]
    exact hf
  have hct := mem_centralizer_singleton_iff.1 (hS.normalizer_E_le_centralizer hmE)
  have hlta : l * (t * a) = t * a * l := by
    rw [← hnt]
    calc l * (n * t * n⁻¹) = n * ((n⁻¹ * l * n) * t) * n⁻¹ := by group
      _ = n * (t * (n⁻¹ * l * n)) * n⁻¹ := by rw [hct]
      _ = n * t * n⁻¹ * l := by group
  apply hla
  have hla' : l * a = a * l := by
    apply mul_left_cancel (a := t)
    calc t * (l * a) = (t * l) * a := by group
      _ = (l * t) * a := by rw [hlt]
      _ = l * (t * a) := by group
      _ = t * a * l := hlta
      _ = t * (a * l) := by group
  rw [hla', mul_inv_cancel_right]

end Setting

theorem false_of_shapeCPrime [Finite G]
    {ε : Eps} {t c a : G} {L U Q P : Subgroup G} {ψ : V6 → G}
    {p : Fin 6 → G} {v₀ : ℕ} (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hS : ShapeCPrime t L c) (hR : RadicalData ε L U Q P a ψ p)
    (hC : CPrimeData ε t U Q P ψ c v₀) : False :=
  (Setting.mk hS hR hC).false_of_setting hG hnab

end CFSG.EvenSmallLie.OmegaEight.CPrime
