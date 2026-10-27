module

public import CFSG.LocalAnalysis.Asc75.Swap
public import CFSG.Adapters.Involutions
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

section Helpers

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_involution {u x : G} (hu : u * u = 1)
    (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, hu2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, hu2, one_zpow, one_mul]

theorem isElemAbelian_of_le' {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem exists_card_four [Finite G] {A : Subgroup G} (h : 2 ≤ CFSG.Open.pRank 2 A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨E₀, hE₀A, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two A
  have hdvd : 2 ^ 2 ∣ Nat.card E₀ := by rw [hcard]; exact pow_dvd_pow 2 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E₀) 2 hdvd
  refine ⟨K.map E₀.subtype, (Subgroup.map_subtype_le K).trans hE₀A, ?_, ?_⟩
  · exact isElemAbelian_of_le' hE₀ (Subgroup.map_subtype_le K)
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]
    norm_num

theorem odd_card_oddCore' (G : Type*) [Group G] [Finite G] : Odd (Nat.card (CFSG.oddCore G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : CFSG.oddCore G = CFSG.pPrimeCore 2 G :=
    (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm
  rw [e]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

end Helpers

section CentralDiag

variable {G : Type} [Group G] [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.central_diag_conj (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1) (ha₁2 : a₁ * a₁ = 1)
    (ha₂2 : a₂ * a₂ = 1) (hcen : ∀ g : G, g * (a₁ * a₂) = (a₁ * a₂) * g) {g : G}
    (hg : g⁻¹ * a₁ * g ∈ S) : g⁻¹ * a₁ * g = a₁ ∨ g⁻¹ * a₁ * g = a₂ := by
  have hint : ∀ x, x ∈ A₁ → x ∈ A₂ → x = 1 := fun x hx1 hx2 => by
    have : x ∈ A₁ ⊓ A₂ := ⟨hx1, hx2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  have hc12 : a₁ * a₂ = a₂ * a₁ := h.comm a₁ ha₁ a₂ ha₂
  have hinv1 : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁2
  have hinv2 : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right ha₂2
  set u : G := a₁ * a₂ with hu
  have hua₁ : u * a₁ = a₂ := by
    rw [hu]
    calc a₁ * a₂ * a₁ = a₁ * (a₂ * a₁) := by group
      _ = a₁ * (a₁ * a₂) := by rw [← hc12]
      _ = (a₁ * a₁) * a₂ := by group
      _ = a₂ := by rw [ha₁2, one_mul]
  have huS : u ∈ S := S.mul_mem (h.le₁ ha₁) (h.le₂ ha₂)
  have hgu : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [← hcen g]
      _ = u := by group
  set x : G := g⁻¹ * a₁ * g with hx
  have hxU : x ∈ uSet A₁ A₂ := h.closed_G hdisj (Or.inl ha₁) hg
  have hux_eq : g⁻¹ * a₂ * g = u * x := by
    calc g⁻¹ * a₂ * g = g⁻¹ * (u * a₁) * g := by rw [hua₁]
      _ = (g⁻¹ * u * g) * (g⁻¹ * a₁ * g) := by group
      _ = u * x := by rw [hgu]
  have huxS : g⁻¹ * a₂ * g ∈ S := by rw [hux_eq]; exact S.mul_mem huS hg
  have huxU : u * x ∈ uSet A₁ A₂ := by
    rw [← hux_eq]
    exact h.closed_G hdisj (Or.inr ha₂) huxS
  rcases hxU with hxA | hxA
  · have hxc : x * a₂ = a₂ * x := h.comm x hxA a₂ ha₂
    have hmul : u * x = (a₁ * x) * a₂ := by
      rw [hu]
      calc a₁ * a₂ * x = a₁ * (a₂ * x) := by group
        _ = a₁ * (x * a₂) := by rw [← hxc]
        _ = a₁ * x * a₂ := by group
    rcases huxU with hm | hm
    · exfalso
      have h1 : (a₁ * x)⁻¹ * (u * x) ∈ A₁ := A₁.mul_mem (A₁.inv_mem (A₁.mul_mem ha₁ hxA)) hm
      rw [hmul, inv_mul_cancel_left] at h1
      exact ha₂1 (hint a₂ h1 ha₂)
    · have h2 : (u * x) * a₂⁻¹ ∈ A₂ := A₂.mul_mem hm (A₂.inv_mem ha₂)
      rw [hmul, mul_inv_cancel_right] at h2
      have h3 : a₁ * x = 1 := hint _ (A₁.mul_mem ha₁ hxA) h2
      left
      calc x = a₁⁻¹ * (a₁ * x) := by group
        _ = a₁ := by rw [h3, mul_one, hinv1]
  · have hxc : a₁ * x = x * a₁ := (h.comm a₁ ha₁ x hxA)
    have hmul : u * x = a₁ * (a₂ * x) := by rw [hu]; group
    rcases huxU with hm | hm
    · have h2 : a₁⁻¹ * (u * x) ∈ A₁ := A₁.mul_mem (A₁.inv_mem ha₁) hm
      rw [hmul, inv_mul_cancel_left] at h2
      have h3 : a₂ * x = 1 := hint _ h2 (A₂.mul_mem ha₂ hxA)
      right
      calc x = a₂⁻¹ * (a₂ * x) := by group
        _ = a₂ := by rw [h3, mul_one, hinv2]
    · exfalso
      have h1 : (u * x) * (a₂ * x)⁻¹ ∈ A₂ := A₂.mul_mem hm (A₂.inv_mem (A₂.mul_mem ha₂ hxA))
      rw [hmul, mul_inv_cancel_right] at h1
      exact ha₁1 (hint a₁ ha₁ h1)

theorem Hyp.eq_top_of_central_diag (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1) (ha₁2 : a₁ * a₁ = 1)
    (ha₂2 : a₂ * a₂ = 1) (hcen : ∀ g : G, g * (a₁ * a₂) = (a₁ * a₂) * g) : H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSigma : ∀ {g : G}, g⁻¹ * a₁ * g ∈ S → g⁻¹ * a₁ * g = a₁ ∨ g⁻¹ * a₁ * g = a₂ :=
    fun {g} hg => h.central_diag_conj hdisj ha₁ ha₂ ha₁1 ha₂1 ha₁2 ha₂2 hcen hg
  have hint : ∀ x, x ∈ A₁ → x ∈ A₂ → x = 1 := fun x hx1 hx2 => by
    have : x ∈ A₁ ⊓ A₂ := ⟨hx1, hx2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  have hc12 : a₁ * a₂ = a₂ * a₁ := h.comm a₁ ha₁ a₂ ha₂
  have hinv1 : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁2
  have hinv2 : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right ha₂2
  have hfa₁ : FixedOnlyElt H a₁ := h.fixedOnlyElt hdisj (Or.inl ha₁) ha₁1
  obtain ⟨u, hu⟩ : ∃ u : G, u = a₁ * a₂ := ⟨_, rfl⟩
  rw [← hu] at hcen
  have hu2 : u * u = 1 := by
    rw [hu]
    calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [hc12]
      _ = (a₁ * a₁) * (a₂ * a₂) := by group
      _ = 1 := by rw [ha₁2, ha₂2, one_mul]
  have huA : u ∉ A₁ := by
    intro hu'
    have h1 : a₁⁻¹ * u ∈ A₁ := A₁.mul_mem (A₁.inv_mem ha₁) hu'
    rw [hu, inv_mul_cancel_left] at h1
    exact ha₂1 (hint a₂ h1 ha₂)
  have hau : a₁ * u = a₂ := by
    rw [hu]
    calc a₁ * (a₁ * a₂) = (a₁ * a₁) * a₂ := by group
      _ = a₂ := by rw [ha₁2, one_mul]
  have huS : u ∈ S := by rw [hu]; exact S.mul_mem (h.le₁ ha₁) (h.le₂ ha₂)
  have huH : u ∈ H := h.S_le_H huS
  have hN : (Subgroup.zpowers u).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g u := hcen g
    have e : g * u ^ k * g⁻¹ = u ^ k := by
      calc g * u ^ k * g⁻¹ = (g * u ^ k) * g⁻¹ := rfl
        _ = (u ^ k * g) * g⁻¹ := by rw [(hc.zpow_right k).eq]
        _ = u ^ k := by group
    rw [e]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  let N : Subgroup G := Subgroup.zpowers u
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπeq : ∀ x y : G, π x = π y ↔ x⁻¹ * y ∈ N := fun x y => QuotientGroup.eq
  have hπone : ∀ x : G, π x = 1 ↔ x ∈ N := fun x => QuotientGroup.eq_one_iff x
  have hNeq : ∀ x ∈ N, x = 1 ∨ x = u := fun x hx =>
    eq_one_or_eq_of_mem_zpowers_involution hu2 hx
  have huN : u ∈ N := Subgroup.mem_zpowers u
  have hπu : π u = 1 := (hπone u).2 huN
  have hπa₂ : π a₂ = π a₁ := by rw [← hau, map_mul, hπu, mul_one]
  have hconj_mem : ∀ g : G, π (g⁻¹ * a₁ * g) = π a₁ → g ∈ H := by
    intro g hg
    have h1 : a₁⁻¹ * (g⁻¹ * a₁ * g) ∈ N := (hπeq _ _).1 hg.symm
    rcases hNeq _ h1 with h2 | h2
    · have : g⁻¹ * a₁ * g = a₁ := by
        calc g⁻¹ * a₁ * g = a₁ * (a₁⁻¹ * (g⁻¹ * a₁ * g)) := by group
          _ = a₁ := by rw [h2, mul_one]
      exact hfa₁.mem_of_conj_eq this
    · have : g⁻¹ * a₁ * g = a₂ := by
        calc g⁻¹ * a₁ * g = a₁ * (a₁⁻¹ * (g⁻¹ * a₁ * g)) := by group
          _ = a₁ * u := by rw [h2]
          _ = a₂ := hau
      exact hfa₁.2 g (by rw [this]; exact h.le_H₂ ha₂)
  let Sbar : Sylow 2 (G ⧸ N) := h.sylowG.mapSurjective hπ
  have hSbar : (Sbar : Subgroup (G ⧸ N)) = S.map π := Sylow.coe_mapSurjective hπ h.sylowG
  have hwS : π a₁ ∈ (Sbar : Subgroup (G ⧸ N)) := by
    rw [hSbar]; exact Subgroup.mem_map_of_mem _ (h.le₁ ha₁)
  have hw1 : π a₁ ≠ 1 := by
    intro e
    rcases hNeq a₁ ((hπone a₁).1 e) with h1 | h1
    · exact ha₁1 h1
    · exact huA (h1 ▸ ha₁)
  have hw2 : π a₁ * π a₁ = 1 := by rw [← map_mul, ha₁2, map_one]
  have hword : orderOf (π a₁) = 2 := orderOf_eq_two_of_mul_self_eq_one hw2 hw1
  let z : (Sbar : Subgroup (G ⧸ N)) := ⟨π a₁, hwS⟩
  have hzord : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hword
  have hzZ : z ∈ Subgroup.center (Sbar : Subgroup (G ⧸ N)) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hs : (s : G ⧸ N) ∈ S.map π := by rw [← hSbar]; exact s.2
    obtain ⟨s₀, hs₀, hs₀eq⟩ := hs
    apply Subtype.ext
    show (s : G ⧸ N) * π a₁ = π a₁ * (s : G ⧸ N)
    rw [← hs₀eq]
    have hS' : s₀⁻¹ * a₁ * s₀ ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs₀) (h.le₁ ha₁)) hs₀
    have hpi : π (s₀⁻¹ * a₁ * s₀) = π a₁ := by
      rcases hSigma hS' with e | e
      · rw [e]
      · rw [e, hπa₂]
    rw [map_mul, map_mul, map_inv] at hpi
    calc π s₀ * π a₁ = π s₀ * ((π s₀)⁻¹ * π a₁ * π s₀) := by rw [hpi]
      _ = π a₁ * π s₀ := by group
  have hwc : ∀ gb : G ⧸ N, gb⁻¹ * (z : G ⧸ N) * gb ∈ (Sbar : Subgroup (G ⧸ N)) →
      gb⁻¹ * (z : G ⧸ N) * gb = z := by
    intro gb hg
    obtain ⟨g, rfl⟩ := hπ gb
    have hgS : (π g)⁻¹ * π a₁ * π g ∈ S.map π := by rw [← hSbar]; exact hg
    obtain ⟨s, hs, hseq⟩ := hgS
    have hseq' : π s = π (g⁻¹ * a₁ * g) := by rw [hseq, map_mul, map_mul, map_inv]
    have h1 : s⁻¹ * (g⁻¹ * a₁ * g) ∈ N := (hπeq _ _).1 hseq'
    have h2 : g⁻¹ * a₁ * g ∈ S := by
      have e : g⁻¹ * a₁ * g = s * (s⁻¹ * (g⁻¹ * a₁ * g)) := by group
      rw [e]
      refine S.mul_mem hs ?_
      rcases hNeq _ h1 with e' | e'
      · rw [e']; exact S.one_mem
      · rw [e']; exact huS
    have hpi : π (g⁻¹ * a₁ * g) = π a₁ := by
      rcases hSigma h2 with e | e
      · rw [e]
      · rw [e, hπa₂]
    show (π g)⁻¹ * π a₁ * π g = π a₁
    calc (π g)⁻¹ * π a₁ * π g = π (g⁻¹ * a₁ * g) := by rw [map_mul, map_mul, map_inv]
      _ = π a₁ := hpi
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar Sbar z hzZ hzord hwc
  obtain ⟨E, hEA, hE, hEcard⟩ := exists_card_four (A := A₁) (by have := h.rank₁; omega)
  have hEinj : Function.Injective (π.comp E.subtype) := by
    intro x y hxy
    have h1 : (x : G)⁻¹ * (y : G) ∈ N := (hπeq _ _).1 hxy
    rcases hNeq _ h1 with e | e
    · exact Subtype.ext (inv_mul_eq_one.1 e)
    · exfalso
      apply huA
      have h2 : (x : G)⁻¹ * (y : G) ∈ A₁ := A₁.mul_mem (A₁.inv_mem (hEA x.2)) (hEA y.2)
      rwa [e] at h2
  have hEbarcard : Nat.card (E.map π) = 2 ^ 2 := by
    have e : E.map π = (π.comp E.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e, ← Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv, hEcard]
    norm_num
  have hcompl : ¬ 2 ∣ Nat.card (CFSG.oddCore (G ⧸ N)) := fun hd =>
    (Nat.not_even_iff_odd.2 (odd_card_oddCore' (G ⧸ N))) (even_iff_two_dvd.2 hd)
  have hnorm : E.map π ≤
      Subgroup.normalizer ((CFSG.oddCore (G ⧸ N) : Subgroup (G ⧸ N)) : Set _) := by
    intro x _
    rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (CFSG.oddCore (G ⧸ N)).Normal)]
    trivial
  have hO_le : CFSG.oddCore (G ⧸ N) ≤ H.map π := by
    refine le_of_forall_inf_centralizer_le'
      (isElementaryAbelian_of_isElemAbelian' (CFSG.SectionRank.isElemAbelian_map hE π))
      (by rw [hEbarcard]) hcompl hnorm ?_
    intro b hb hb1 x hx
    obtain ⟨-, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨e, heE, hem⟩ := Subgroup.mem_map.1 hb
    have he1 : e ≠ 1 := fun e1 => hb1 (by rw [← hem, e1, map_one])
    obtain ⟨g, rfl⟩ := hπ x
    refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
    have hcomm : π g * π e = π e * π g := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hxC
      rwa [← hem] at this
    have hconj : π (g⁻¹ * e * g) = π e := by
      rw [map_mul, map_mul, map_inv]
      calc (π g)⁻¹ * π e * π g = (π g)⁻¹ * (π e * π g) := by group
        _ = (π g)⁻¹ * (π g * π e) := by rw [← hcomm]
        _ = π e := by group
    have h1 : e⁻¹ * (g⁻¹ * e * g) ∈ N := (hπeq _ _).1 hconj.symm
    have heA : e ∈ A₁ := hEA heE
    have heU : e ∈ uSet A₁ A₂ := Or.inl heA
    rcases hNeq _ h1 with h2 | h2
    · have : g⁻¹ * e * g = e := by
        calc g⁻¹ * e * g = e * (e⁻¹ * (g⁻¹ * e * g)) := by group
          _ = e := by rw [h2, mul_one]
      exact h.mem_of_conj_eq heU he1 this
    · have h3 : g⁻¹ * e * g = e * u := by
        calc g⁻¹ * e * g = e * (e⁻¹ * (g⁻¹ * e * g)) := by group
          _ = e * u := by rw [h2]
      have h4 : e * u ∈ uSet A₁ A₂ := by
        have hS : g⁻¹ * e * g ∈ S := by rw [h3]; exact S.mul_mem (h.le₁ heA) huS
        have := h.closed_G hdisj heU hS
        rwa [h3] at this
      have h7 : e * u = (e * a₁) * a₂ := by rw [hu]; group
      have hea : e = a₁ := by
        rcases h4 with h5 | h5
        · exfalso
          have h6 : (e * a₁)⁻¹ * (e * u) ∈ A₁ :=
            A₁.mul_mem (A₁.inv_mem (A₁.mul_mem heA ha₁)) h5
          rw [h7, inv_mul_cancel_left] at h6
          exact ha₂1 (hint a₂ h6 ha₂)
        · have h6 : (e * u) * a₂⁻¹ ∈ A₂ := A₂.mul_mem h5 (A₂.inv_mem ha₂)
          rw [h7, mul_inv_cancel_right] at h6
          have h8 : e * a₁ = 1 := hint _ (A₁.mul_mem heA ha₁) h6
          calc e = (e * a₁) * a₁⁻¹ := by group
            _ = a₁ := by rw [h8, one_mul, hinv1]
      rw [hea] at h3
      have h9 : g⁻¹ * a₁ * g = a₂ := by rw [h3, hau]
      exact hfa₁.2 g (by rw [h9]; exact h.le_H₂ ha₂)
  have hpre : ∀ k : G, π k ∈ CFSG.oddCore (G ⧸ N) → k ∈ H := by
    intro k hk
    obtain ⟨h₀, hh₀, hh₀eq⟩ := Subgroup.mem_map.1 (hO_le hk)
    have h1 : h₀⁻¹ * k ∈ N := (hπeq _ _).1 hh₀eq
    have e : k = h₀ * (h₀⁻¹ * k) := by group
    rw [e]
    refine H.mul_mem hh₀ ?_
    rcases hNeq _ h1 with e' | e'
    · rw [e']; exact H.one_mem
    · rw [e']; exact huH
  rw [eq_top_iff]
  intro g _
  obtain ⟨c, hc, k, hk, hgck⟩ := hfac (π g)
  obtain ⟨c₀, rfl⟩ := hπ c
  obtain ⟨k₀, rfl⟩ := hπ k
  have h1 : (c₀ * k₀)⁻¹ * g ∈ N := (hπeq _ _).1 (by rw [map_mul]; exact hgck.symm)
  have hc₀ : c₀ ∈ H := by
    apply hconj_mem
    have hcz : π c₀ * π a₁ = π a₁ * π c₀ := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [map_mul, map_mul, map_inv]
    calc (π c₀)⁻¹ * π a₁ * π c₀ = (π c₀)⁻¹ * (π a₁ * π c₀) := by group
      _ = (π c₀)⁻¹ * (π c₀ * π a₁) := by rw [hcz]
      _ = π a₁ := by group
  have hk₀ : k₀ ∈ H := hpre k₀ hk
  have e : g = (c₀ * k₀) * ((c₀ * k₀)⁻¹ * g) := by group
  rw [e]
  refine H.mul_mem (H.mul_mem hc₀ hk₀) ?_
  rcases hNeq _ h1 with e' | e'
  · rw [e']; exact H.one_mem
  · rw [e']; exact huH

end CentralDiag

end CFSG.Asc75
