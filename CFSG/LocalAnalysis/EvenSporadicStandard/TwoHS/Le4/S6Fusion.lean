module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Struct

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : G}

namespace FourHyp

theorem pow_four (H : FourHyp G L f) : f ^ 4 = 1 := by
  rw [← H.order]; exact pow_orderOf_eq_one f

theorem orderOf_sq (H : FourHyp G L f) : orderOf (f ^ 2) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul]; exact H.pow_four
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [H.order] at this
    omega

theorem mem_cent (H : FourHyp G L f) : f ∈ centralizer (L : Set G) := H.cent ▸ mem_zpowers f

theorem sq_eq_of_orderOf_eq_four (H : FourHyp G L f) {c : G} (hc : c ∈ centralizer (L : Set G))
    (hc4 : orderOf c = 4) : c * c = f ^ 2 := by
  have hc44 : c ^ 4 = 1 := by rw [← hc4]; exact pow_orderOf_eq_one c
  have hcc4 : c * c * (c * c) = 1 := by
    rw [← hc44, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  have hcc1 : c * c ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one (show c ^ 2 = 1 by rwa [sq])
    rw [hc4] at this
    omega
  exact (H.eq_one_or_eq_sq (mul_mem hc hc) hcc4).resolve_left hcc1

theorem eq_one_or_eq_sq_of_mem {a : G} (H : FourHyp G L f) (haL : a ∈ L)
    (haC : a ∈ centralizer (L : Set G)) : a = 1 ∨ a = f ^ 2 := by
  have hmem : a ∈ (center L).map L.subtype := by
    rw [map_center_eq_inf_centralizer]; exact ⟨haL, haC⟩
  rw [H.zent] at hmem
  exact eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_sq hmem

theorem sq_mem (H : FourHyp G L f) : f ^ 2 ∈ L := by
  obtain ⟨τ, -, hτ⟩ := H.exists_center_gen
  rw [← hτ]; exact τ.2

theorem exists_inverting (H : FourHyp G L f) {s g' c : G} (hs : IsTight L s)
    (hcC : c ∈ centralizer (L : Set G)) (hsc : g' * c * g'⁻¹ = s) :
    ∃ y : G, y * y = 1 ∧ y * f * y⁻¹ = f⁻¹ ∧ (∃ h : G, y = h * f ^ 2 * h⁻¹) ∧
      ∃ h : G, s ^ 2 = h * f ^ 2 * h⁻¹ := by
  obtain ⟨u, x, p, ŵ, c_s, hu, huu, hucen, hcsC, hcsc, hsw, hxdef, hxx, hxs⟩ := H.tight_core hs
  have hc4 : orderOf c = 4 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj g') c]
    simp only [MulAut.conj_apply]
    rw [hsc]; exact hs.order
  have hcc : c * c = f ^ 2 := H.sq_eq_of_orderOf_eq_four hcC hc4
  have hczf : zpowers c = zpowers f := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 (H.cent ▸ hcC)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hc4, H.order]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hczf ▸ mem_zpowers f : f ∈ zpowers c)
  have hxG : (x : G) * (x : G) = 1 := by
    have := congrArg Subtype.val hxx
    simpa using this
  have hs2 : s ^ 2 = g' * f ^ 2 * g'⁻¹ := by
    rw [← hsc, ← hcc, sq]; group
  have hxpu : (x : G) = (p : G) * (u : G) * (p : G)⁻¹ := by
    have := congrArg Subtype.val hxdef
    simpa using this
  refine ⟨g'⁻¹ * (x : G) * g', ?_, ?_, ⟨g'⁻¹ * (p : G) * g', ?_⟩, ⟨g', hs2⟩⟩
  · calc g'⁻¹ * (x : G) * g' * (g'⁻¹ * (x : G) * g') = g'⁻¹ * ((x : G) * (x : G)) * g' := by
          group
      _ = 1 := by rw [hxG]; group
  · have hyc : g'⁻¹ * (x : G) * g' * c * (g'⁻¹ * (x : G) * g')⁻¹ = c⁻¹ := by
      calc g'⁻¹ * (x : G) * g' * c * (g'⁻¹ * (x : G) * g')⁻¹
          = g'⁻¹ * ((x : G) * (g' * c * g'⁻¹) * (x : G)⁻¹) * g' := by group
        _ = g'⁻¹ * ((x : G) * s * (x : G)⁻¹) * g' := by rw [hsc]
        _ = g'⁻¹ * s⁻¹ * g' := by rw [hxs]
        _ = c⁻¹ := by rw [← hsc]; group
    rw [← hk, ← conj_zpow, hyc, inv_zpow]
  · rw [hxpu, hu, hs2]; group

theorem isTight_conj (H : FourHyp G L f) {s : G} (g : G)
    (hg : s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹)
    (hs2L : ∃ u : L, (u : G) = s ^ 2 ∧ u ∉ center L) : IsTight L (g * f * g⁻¹) := by
  obtain ⟨u, hu, hucen⟩ := hs2L
  have hfC := H.mem_cent
  have hfu : f * s ^ 2 = s ^ 2 * f := by
    rw [← hu]; exact (mem_centralizer_iff.1 hfC u u.2).symm
  have hff : f * f ^ 2 = f ^ 2 * f := by group
  have hfz : f * (s ^ 2 * f ^ 2) = (s ^ 2 * f ^ 2) * f := by
    calc f * (s ^ 2 * f ^ 2) = (f * s ^ 2) * f ^ 2 := by group
      _ = s ^ 2 * (f * f ^ 2) := by rw [hfu]; group
      _ = s ^ 2 * (f ^ 2 * f) := by rw [hff]
      _ = (s ^ 2 * f ^ 2) * f := by group
  have hf2eq : f ^ 2 = g⁻¹ * (s ^ 2 * f ^ 2) * g := by rw [hg]; group
  have hft : (g⁻¹ * f * g) * f ^ 2 = f ^ 2 * (g⁻¹ * f * g) := by
    calc g⁻¹ * f * g * f ^ 2 = g⁻¹ * f * (g * f ^ 2 * g⁻¹) * g := by group
      _ = g⁻¹ * f * (s ^ 2 * f ^ 2) * g := by rw [← hg]
      _ = g⁻¹ * ((s ^ 2 * f ^ 2) * f) * g := by rw [← hfz]; group
      _ = (g⁻¹ * (s ^ 2 * f ^ 2) * g) * (g⁻¹ * f * g) := by group
      _ = f ^ 2 * (g⁻¹ * f * g) := by rw [← hf2eq]
  have hftN : g⁻¹ * f * g ∈ normalizer (L : Set G) :=
    H.norm ▸ mem_centralizer_singleton_iff.2 hft
  have hsq := H.std.sq_mem_sup_centralizer H.out hftN
  obtain ⟨l, hl, c', hc', hlc⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hsq
  have hfl : f * (l * c') = (l * c') * f := by
    have h1 : l * f = f * l := mem_centralizer_iff.1 hfC l hl
    have h2 : f * c' = c' * f := by
      rw [H.cent] at hc'
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc'
      exact (Commute.self_zpow f i).eq
    calc f * (l * c') = (f * l) * c' := by group
      _ = (l * f) * c' := by rw [h1]
      _ = l * (f * c') := by group
      _ = l * (c' * f) := by rw [h2]
      _ = (l * c') * f := by group
  have hsqeq : (g⁻¹ * f * g) ^ 2 = g⁻¹ * f ^ 2 * g := by rw [sq, sq]; group
  have hf2C : f ^ 2 ∈ centralizer (L : Set G) := H.cent ▸ Subgroup.pow_mem _ (mem_zpowers f) 2
  have hcomm : (g * f * g⁻¹) * f ^ 2 = f ^ 2 * (g * f * g⁻¹) := by
    have h1 : f ^ 2 = g * (l * c') * g⁻¹ := by
      calc f ^ 2 = g * (g⁻¹ * f ^ 2 * g) * g⁻¹ := by group
        _ = g * (l * c') * g⁻¹ := by rw [← hsqeq, hlc]
    calc g * f * g⁻¹ * f ^ 2 = g * f * g⁻¹ * (g * (l * c') * g⁻¹) := by rw [← h1]
      _ = g * (f * (l * c')) * g⁻¹ := by group
      _ = g * ((l * c') * f) * g⁻¹ := by rw [hfl]
      _ = g * (l * c') * g⁻¹ * (g * f * g⁻¹) := by group
      _ = f ^ 2 * (g * f * g⁻¹) := by rw [← h1]
  have hmemN : g * f * g⁻¹ ∈ normalizer (L : Set G) :=
    H.norm ▸ mem_centralizer_singleton_iff.2 hcomm
  have hord : orderOf (g * f * g⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g) f
    rw [MulAut.conj_apply] at h1
    rw [h1]; exact H.order
  have hzmC : ¬ (s ^ 2 * f ^ 2 ∈ centralizer (L : Set G)) := by
    intro hz
    have hs2C : s ^ 2 ∈ centralizer (L : Set G) := by
      have : s ^ 2 = (s ^ 2 * f ^ 2) * (f ^ 2)⁻¹ := by group
      rw [this]
      exact mul_mem hz (inv_mem hf2C)
    apply hucen
    have hmem : (u : G) ∈ (center L).map L.subtype := by
      rw [map_center_eq_inf_centralizer]; exact ⟨u.2, by rw [hu]; exact hs2C⟩
    obtain ⟨u₀, hu₀, hu₀e⟩ := hmem
    have : u₀ = u := Subtype.ext hu₀e
    rwa [this] at hu₀
  have hsqC : (g * f * g⁻¹) * (g * f * g⁻¹) = s ^ 2 * f ^ 2 := by
    calc (g * f * g⁻¹) * (g * f * g⁻¹) = g * (f * f) * g⁻¹ := by group
      _ = g * f ^ 2 * g⁻¹ := by rw [sq]
      _ = s ^ 2 * f ^ 2 := hg.symm
  have hinter : ∀ y ∈ zpowers (g * f * g⁻¹), y ∈ centralizer (L : Set G) → y = 1 := by
    intro y hy hyC
    rcases zpowers_cases hord hy with h1 | h1 | h1 | h1
    · exact h1
    · exfalso; apply hzmC; rw [← hsqC]; rw [h1] at hyC; exact mul_mem hyC hyC
    · exfalso; apply hzmC; rw [← hsqC]; rw [h1] at hyC
      have hl : g * f * g⁻¹ ∈ centralizer (L : Set G) := by simpa using inv_mem hyC
      exact mul_mem hl hl
    · exfalso; apply hzmC; rw [h1, hsqC] at hyC; exact hyC
  have hcent : ∀ x : G, x * (g * f * g⁻¹) ^ 2 = (g * f * g⁻¹) ^ 2 * x →
      x * (g * f * g⁻¹) * x⁻¹ ∈ zpowers (g * f * g⁻¹) := by
    intro x hx
    have hsq' : (g * f * g⁻¹) ^ 2 = g * f ^ 2 * g⁻¹ := by rw [sq, sq]; group
    rw [hsq'] at hx
    have hx0 : (g⁻¹ * x * g) * f ^ 2 = f ^ 2 * (g⁻¹ * x * g) := by
      calc g⁻¹ * x * g * f ^ 2 = g⁻¹ * (x * (g * f ^ 2 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * f ^ 2 * g⁻¹) * x) * g := by rw [hx]
        _ = f ^ 2 * (g⁻¹ * x * g) := by group
    have hx0N : g⁻¹ * x * g ∈ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) :=
      H.std.centralizer_le_normalizer_centralizer hf2C H.orderOf_sq
        (mem_centralizer_singleton_iff.2 hx0)
    have hfmem : (g⁻¹ * x * g) * f * (g⁻¹ * x * g)⁻¹ ∈ centralizer (L : Set G) :=
      (mem_normalizer_iff.1 hx0N f).1 H.mem_cent
    rw [H.cent] at hfmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hfmem
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    calc (g * f * g⁻¹) ^ k = g * f ^ k * g⁻¹ := by rw [conj_zpow]
      _ = g * ((g⁻¹ * x * g) * f * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by rw [hk]
      _ = x * (g * f * g⁻¹) * x⁻¹ := by group
  exact ⟨hord, hmemN, hinter, hcent⟩

theorem not_conj_sq_mul (H : FourHyp G L f) {s : G} (hs : IsTight L s) :
    ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹ := by
  rintro ⟨g, hg⟩
  obtain ⟨u, x, p, ŵ, c, hu, huu, hucen, hcC, hcc, hsc, -, -, -⟩ := H.tight_core hs
  have hft := H.isTight_conj g hg ⟨u, hu, hucen⟩
  have hf2f2 : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact H.pow_four
  have hf2C : f ^ 2 ∈ centralizer (L : Set G) := H.cent ▸ Subgroup.pow_mem _ (mem_zpowers f) 2
  have hs44 : s ^ 4 = 1 := by rw [← hs.order]; exact pow_orderOf_eq_one s
  have hs2s2 : s ^ 2 * s ^ 2 = 1 := by rw [← pow_add]; exact hs44
  have hfm2 : (g * f * g⁻¹) * (g * f * g⁻¹) = s ^ 2 * f ^ 2 := by
    calc (g * f * g⁻¹) * (g * f * g⁻¹) = g * (f * f) * g⁻¹ := by group
      _ = g * f ^ 2 * g⁻¹ := by rw [sq]
      _ = s ^ 2 * f ^ 2 := hg.symm
  obtain ⟨c₂, hc₂C, hcase⟩ := H.tight_comparison hs hft (Or.inr (by rw [sq, hfm2]))
  have hcm : Commute (ŵ : G) c := mem_centralizer_iff.1 hcC ŵ ŵ.2
  obtain ⟨σ, ŵσ, cσ, hŵσ, hcσ, hcσcσ, hσ, hσσ, hfmσ⟩ : ∃ σ ŵσ cσ : G, ŵσ ∈ L ∧
      cσ ∈ centralizer (L : Set G) ∧ cσ * cσ = f ^ 2 ∧ σ = ŵσ * cσ ∧ σ * σ = s ^ 2 ∧
      g * f * g⁻¹ = c₂ * σ := by
    rcases hcase with h | h
    · exact ⟨s, ŵ, c, ŵ.2, hcC, hcc, hsc, by rw [← sq], h⟩
    · refine ⟨s⁻¹, (ŵ : G)⁻¹, c⁻¹, inv_mem ŵ.2, inv_mem hcC, ?_, ?_, ?_, h⟩
      · calc c⁻¹ * c⁻¹ = (c * c)⁻¹ := by group
          _ = (f ^ 2)⁻¹ := by rw [hcc]
          _ = f ^ 2 := inv_eq_of_mul_eq_one_right hf2f2
      · rw [hsc, mul_inv_rev]; exact hcm.inv_inv.eq.symm
      · calc s⁻¹ * s⁻¹ = (s * s)⁻¹ := by group
          _ = s ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs2s2)
  have hσLC : σ ∈ L ⊔ centralizer (L : Set G) := by
    rw [hσ]; exact Subgroup.mul_mem_sup hŵσ hcσ
  have hc₂σ : c₂ * σ = σ * c₂ := H.commute_of_mem_centralizer_of_mem_sup hc₂C hσLC
  have hfu : (s ^ 2) * f ^ 2 = f ^ 2 * s ^ 2 := by
    rw [← hu]; exact mem_centralizer_iff.1 hf2C u u.2
  have hc₂c₂ : c₂ * c₂ = f ^ 2 := by
    apply mul_right_cancel (b := s ^ 2)
    rw [← hfu, ← hfm2, hfmσ]
    calc c₂ * c₂ * s ^ 2 = c₂ * c₂ * (σ * σ) := by rw [hσσ]
      _ = c₂ * (c₂ * σ) * σ := by group
      _ = c₂ * (σ * c₂) * σ := by rw [hc₂σ]
      _ = c₂ * σ * (c₂ * σ) := by group
  have hcomm₂ : c₂ * cσ = cσ * c₂ := by
    rw [H.cent] at hc₂C hcσ
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc₂C
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hcσ
    exact (Commute.zpow_zpow_self f i j).eq
  have hdd : (c₂ * cσ) * (c₂ * cσ) = 1 := by
    calc (c₂ * cσ) * (c₂ * cσ) = (c₂ * c₂) * (cσ * cσ) := by
          calc (c₂ * cσ) * (c₂ * cσ) = c₂ * (cσ * c₂) * cσ := by group
            _ = c₂ * (c₂ * cσ) * cσ := by rw [hcomm₂]
            _ = (c₂ * c₂) * (cσ * cσ) := by group
      _ = 1 := by rw [hc₂c₂, hcσcσ]; exact hf2f2
  have hdL : c₂ * cσ ∈ L := by
    rcases H.eq_one_or_eq_sq (mul_mem hc₂C hcσ) hdd with h | h
    · rw [h]; exact L.one_mem
    · rw [h]; exact H.sq_mem
  have hfmL : g * f * g⁻¹ ∈ L := by
    have : g * f * g⁻¹ = ŵσ * (c₂ * cσ) := by
      rw [hfmσ, hσ]
      have h1 : ŵσ * c₂ = c₂ * ŵσ := mem_centralizer_iff.1 hc₂C ŵσ hŵσ
      calc c₂ * (ŵσ * cσ) = (c₂ * ŵσ) * cσ := by group
        _ = (ŵσ * c₂) * cσ := by rw [h1]
        _ = ŵσ * (c₂ * cσ) := by group
    rw [this]; exact L.mul_mem hŵσ hdL
  obtain ⟨u', x', p', ŵ', c', -, -, -, hc'C, hc'c', hfmc', -, -, -⟩ := H.tight_core hft
  have hc'L : c' ∈ L := by
    have : c' = (ŵ' : G)⁻¹ * (g * f * g⁻¹) := by rw [hfmc']; group
    rw [this]; exact L.mul_mem (L.inv_mem ŵ'.2) hfmL
  rcases H.eq_one_or_eq_sq_of_mem hc'L hc'C with h | h
  · rw [h, mul_one] at hc'c'
    have := congrArg orderOf hc'c'
    rw [orderOf_one, H.orderOf_sq] at this
    omega
  · rw [h] at hc'c'
    have h2 : f ^ 2 = 1 := by
      calc f ^ 2 = f ^ 2 * f ^ 2 * (f ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc'c'] ; group
    have := congrArg orderOf h2
    rw [orderOf_one, H.orderOf_sq] at this
    omega

theorem centralizer_sq_eq_sup (H : FourHyp G L f) {y : G} (hyf : y * f * y⁻¹ = f⁻¹) :
    y ∉ L ⊔ zpowers f ∧ centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y := by
  have hf2C : f ^ 2 ∈ centralizer (L : Set G) := H.cent ▸ Subgroup.pow_mem _ (mem_zpowers f) 2
  have hyN : y ∈ centralizer ({f ^ 2} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : y * f ^ 2 * y⁻¹ = f ^ 2 := by
      rw [show y * f ^ 2 * y⁻¹ = (y * f * y⁻¹) ^ 2 by rw [sq, sq]; group, hyf]
      have h2 : f⁻¹ ^ 2 = f ^ 2 := by
        rw [inv_pow]
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact H.pow_four)
      exact h2
    calc y * f ^ 2 = (y * f ^ 2 * y⁻¹) * y := by group
      _ = f ^ 2 * y := by rw [h1]
  have hynot : y ∉ L ⊔ zpowers f := by
    intro hy
    rw [← H.cent] at hy
    have hcomm := H.commute_of_mem_centralizer_of_mem_sup H.mem_cent hy
    have h1 : f * y = y * f := hcomm
    have h2 : f⁻¹ = f := by
      calc f⁻¹ = y * f * y⁻¹ := hyf.symm
        _ = f * y * y⁻¹ := by rw [h1]
        _ = f := by group
    have h3 : f * f = 1 := by
      calc f * f = f * f⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel f
    have := orderOf_dvd_of_pow_eq_one (show f ^ 2 = 1 by rwa [sq])
    rw [H.order] at this
    omega
  refine ⟨hynot, ?_⟩
  have hLN : L ≤ centralizer ({f ^ 2} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hf2C l hl)
  have hfN : zpowers f ≤ centralizer ({f ^ 2} : Set G) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]
    group
  have hMN : L ⊔ zpowers f ≤ centralizer ({f ^ 2} : Set G) := sup_le hLN hfN
  have hKN : (L ⊔ zpowers f) ⊔ zpowers y ≤ centralizer ({f ^ 2} : Set G) :=
    sup_le hMN (zpowers_le.2 hyN)
  have hdvd : (L ⊔ zpowers f).relIndex (centralizer ({f ^ 2} : Set G)) ∣ 2 := by
    have h1 : (L ⊔ centralizer (L : Set G)).relIndex (centralizer ({f ^ 2} : Set G)) ∣ 2 :=
      (H.std.relIndex_sup_centralizer_dvd hf2C H.orderOf_sq).trans H.out
    rwa [H.cent] at h1
  have hMK : L ⊔ zpowers f ≤ (L ⊔ zpowers f) ⊔ zpowers y := le_sup_left
  have hrel := Subgroup.relIndex_mul_relIndex (L ⊔ zpowers f) ((L ⊔ zpowers f) ⊔ zpowers y)
    (centralizer ({f ^ 2} : Set G)) hMK hKN
  have hne : (L ⊔ zpowers f).relIndex ((L ⊔ zpowers f) ⊔ zpowers y) ≠ 1 := by
    intro h1
    exact hynot (Subgroup.relIndex_eq_one.1 h1 (mem_sup_right (mem_zpowers y)))
  have h2 : ((L ⊔ zpowers f) ⊔ zpowers y).relIndex (centralizer ({f ^ 2} : Set G)) = 1 := by
    set a := (L ⊔ zpowers f).relIndex ((L ⊔ zpowers f) ⊔ zpowers y) with ha
    set b := ((L ⊔ zpowers f) ⊔ zpowers y).relIndex (centralizer ({f ^ 2} : Set G)) with hb
    set c := (L ⊔ zpowers f).relIndex (centralizer ({f ^ 2} : Set G)) with hc
    have hadvd : a ∣ 2 := (Dvd.intro b hrel).trans hdvd
    have ha2 : a = 2 := ((Nat.dvd_prime Nat.prime_two).1 hadvd).resolve_left hne
    have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    have hcle : c ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    rw [ha2] at hrel
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h2) hKN

theorem exists_phase_one (H : FourHyp G L f) (hFG : CFSG.EvenSmallLie.FoursGroupCondition L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : Nat.card S = 4) :
    ∃ s y : G, IsTight L s ∧ y * y = 1 ∧ y * f * y⁻¹ = f⁻¹ ∧ y ∉ L ⊔ zpowers f ∧
      centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y ∧
      (∃ h : G, y = h * f ^ 2 * h⁻¹) ∧ (∃ h : G, s ^ 2 = h * f ^ 2 * h⁻¹) ∧
      (¬ ∃ h : G, s ^ 2 * f ^ 2 = h * f ^ 2 * h⁻¹) ∧
      ∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L := by
  obtain ⟨g', c, s, hcC, hsc, hs4, hsN, hsC, hsT⟩ := H.std.exists_tight_four hFG S hS
  have hs : IsTight L s := ⟨hs4, hsN, hsC, hsT⟩
  obtain ⟨y, hyy, hyf, hy, hs2⟩ := H.exists_inverting hs hcC hsc
  obtain ⟨hynot, hN⟩ := H.centralizer_sq_eq_sup hyf
  obtain ⟨u, -, -, -, -, hu, huu, hucen, -⟩ := H.tight_core hs
  exact ⟨s, y, hs, hyy, hyf, hynot, hN, hy, hs2, H.not_conj_sq_mul hs, u, hu, huu, hucen⟩

end FourHyp

end CFSG.EvenSporadicStandard.TwoHS
