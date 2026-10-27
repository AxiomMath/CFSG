module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Layer0

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSmallLie
open CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_tight_cyclic (h : StdHyp G L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S) (hS4 : 4 ≤ Nat.card S) {g' : G}
    (hg' : g' ∉ normalizer (L : Set G)) {T : Subgroup G}
    (hTg : T ≤ (centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom)
    (hTN : T ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T) (hTcard : Nat.card T = Nat.card S) :
    ∃ (s : G) (n : ℕ), 2 ≤ n ∧ Nat.card S = 2 ^ n ∧ orderOf s = 2 ^ n ∧ s ∈ T ∧ IsCyclic T ∧
      s ∈ normalizer (L : Set G) ∧ (∀ y ∈ T, y ∈ centralizer (L : Set G) → y = 1) ∧
      ∀ x : G, x * s ^ 2 ^ (n - 1) = s ^ 2 ^ (n - 1) * x → ∀ y ∈ T, x * y * x⁻¹ ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hodd, hNC, -⟩ := h.standard
  have hgC : g' ∉ normalizer ((centralizer (L : Set G)) : Set G) := by rwa [hNC]
  have hTC : ∀ y ∈ T, y ∈ (centralizer (L : Set G)) → y = 1 := by
    intro y hyT hyC
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨y, hyT⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hyC, hTg hyT⟩ :
      y ∈ (centralizer (L : Set G)) ⊓ (centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom)
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr (hodd g' hgC))
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hTcyc : IsCyclic T := (isCyclic_and_card_le_of_le_conj S hS hTg hT).1
  obtain ⟨⟨s, hsT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hsord : orderOf s = Nat.card S := by
    have h' := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk, hTcard] at h'
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h4 : 4 ≤ 2 ^ n := hn ▸ hS4
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsn : orderOf s = 2 ^ n := by rw [hsord, hn]
  have hsC' : s ∈ (normalizer (L : Set G)) := hTN hsT
  set t₁ : G := s ^ 2 ^ (n - 1) with ht₁def
  have ht₁T : t₁ ∈ T := Subgroup.pow_mem _ hsT _
  have ht₁2 : orderOf t₁ = 2 := orderOf_pow_two_pow_pred (by omega) hsn
  have ht₁1 : t₁ * t₁ = 1 := by rw [← sq, ← ht₁2, pow_orderOf_eq_one]
  obtain ⟨c_t, hc_tC, hct⟩ := Subgroup.mem_map.mp (hTg ht₁T)
  have hct' : g' * c_t * g'⁻¹ = t₁ := by simpa [MulAut.conj_apply] using hct
  have hct2 : orderOf c_t = 2 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj g') c_t]
    simp only [MulAut.conj_apply]
    rw [hct', ht₁2]
  obtain ⟨S', hS'cyc, hcS'⟩ := h.exists_cyclic_sylow_mem hc_tC hct2
  have hE : (centralizer (L : Set G)) ⊓ centralizer ({c_t} : Set G) =
      (S' : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
    h.centralizer_inf_centralizer_eq_map_sylow hc_tC hct2 S' hS'cyc hcS'
  have hS'card : Nat.card ((S' : Subgroup (centralizer (L : Set G))).map
      (centralizer (L : Set G)).subtype) = Nat.card S := by
    rw [Subgroup.card_map_of_injective (centralizer (L : Set G)).subtype_injective]
    exact Nat.card_congr (Sylow.equiv S' S).toEquiv
  set T₀ : Subgroup G := T.map (MulAut.conj g'⁻¹).toMonoidHom with hT₀def
  have hT₀le : T₀ ≤ (centralizer (L : Set G)) ⊓ centralizer ({c_t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hwC, hw⟩ := Subgroup.mem_map.mp (hTg hy)
    have hw' : g' * w * g'⁻¹ = y := by simpa using hw
    have hyw : (MulAut.conj g'⁻¹).toMonoidHom y = w := by
      show g'⁻¹ * y * g'⁻¹⁻¹ = w
      rw [inv_inv, ← hw']; group
    rw [hyw]
    refine Subgroup.mem_inf.mpr ⟨hwC, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm : t₁ * y = y * t₁ := mul_comm_of_mem_isCyclic hTcyc ht₁T hy
    have hcteq : c_t = g'⁻¹ * t₁ * g' := by rw [← hct']; group
    have hwy : w = g'⁻¹ * y * g' := by rw [← hw']; group
    rw [hcteq, hwy]
    calc g'⁻¹ * y * g' * (g'⁻¹ * t₁ * g') = g'⁻¹ * (y * t₁) * g' := by group
      _ = g'⁻¹ * (t₁ * y) * g' := by rw [hcomm]
      _ = g'⁻¹ * t₁ * g' * (g'⁻¹ * y * g') := by group
  have hT₀card : Nat.card T₀ = Nat.card S := by
    rw [hT₀def, Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective, hTcard]
  have hT₀eq : T₀ = (centralizer (L : Set G)) ⊓ centralizer ({c_t} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hT₀le (by rw [hE, hS'card, hT₀card])
  have hnormT : ∀ x : G, x * t₁ = t₁ * x → ∀ y ∈ T, x * y * x⁻¹ ∈ T := by
    intro x hx y hy
    set x₀ : G := g'⁻¹ * x * g' with hx₀
    have hx₀c : x₀ * c_t = c_t * x₀ := by
      have e1 : x * (g' * c_t * g'⁻¹) = (g' * c_t * g'⁻¹) * x := by rw [hct']; exact hx
      calc x₀ * c_t = g'⁻¹ * (x * (g' * c_t * g'⁻¹)) * g' := by rw [hx₀]; group
        _ = g'⁻¹ * ((g' * c_t * g'⁻¹) * x) * g' := by rw [e1]
        _ = c_t * x₀ := by rw [hx₀]; group
    have hx₀N : x₀ ∈ (normalizer (L : Set G)) := h.centralizer_le_normalizer hc_tC hct2
      (mem_centralizer_singleton_iff.mpr hx₀c)
    have hx₀NC : x₀ ∈ normalizer ((centralizer (L : Set G)) : Set G) := by rw [hNC]; exact hx₀N
    have hy₀ : g'⁻¹ * y * g' ∈ T₀ := ⟨y, hy, by simp⟩
    rw [hT₀eq] at hy₀
    obtain ⟨hy₀C, hy₀c⟩ := hy₀
    have hy₀c' : g'⁻¹ * y * g' * c_t = c_t * (g'⁻¹ * y * g') :=
      mem_centralizer_singleton_iff.mp hy₀c
    have hxinv : x₀⁻¹ * c_t = c_t * x₀⁻¹ := by
      calc x₀⁻¹ * c_t = x₀⁻¹ * (c_t * x₀) * x₀⁻¹ := by group
        _ = x₀⁻¹ * (x₀ * c_t) * x₀⁻¹ := by rw [hx₀c]
        _ = c_t * x₀⁻¹ := by group
    have hmC : x₀ * (g'⁻¹ * y * g') * x₀⁻¹ ∈ (centralizer (L : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp hx₀NC _).mp hy₀C
    have hmc : x₀ * (g'⁻¹ * y * g') * x₀⁻¹ ∈ centralizer ({c_t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x₀ * (g'⁻¹ * y * g') * x₀⁻¹ * c_t
          = x₀ * (g'⁻¹ * y * g') * (x₀⁻¹ * c_t) := by group
        _ = x₀ * (g'⁻¹ * y * g') * (c_t * x₀⁻¹) := by rw [hxinv]
        _ = x₀ * ((g'⁻¹ * y * g') * c_t) * x₀⁻¹ := by group
        _ = x₀ * (c_t * (g'⁻¹ * y * g')) * x₀⁻¹ := by rw [hy₀c']
        _ = (x₀ * c_t) * (g'⁻¹ * y * g') * x₀⁻¹ := by group
        _ = (c_t * x₀) * (g'⁻¹ * y * g') * x₀⁻¹ := by rw [hx₀c]
        _ = c_t * (x₀ * (g'⁻¹ * y * g') * x₀⁻¹) := by group
    have hmem : x₀ * (g'⁻¹ * y * g') * x₀⁻¹ ∈ T₀ := by
      rw [hT₀eq]; exact Subgroup.mem_inf.mpr ⟨hmC, hmc⟩
    obtain ⟨τ, hτ, hτe⟩ := Subgroup.mem_map.mp hmem
    have hτe' : g'⁻¹ * τ * g' = x₀ * (g'⁻¹ * y * g') * x₀⁻¹ := by
      simpa [MulAut.conj_apply] using hτe
    have : x * y * x⁻¹ = τ := by
      have h2 : τ = g' * (x₀ * (g'⁻¹ * y * g') * x₀⁻¹) * g'⁻¹ := by rw [← hτe']; group
      rw [h2, hx₀]; group
    rw [this]; exact hτ
  exact ⟨s, n, hn2, hn, hsn, hsT, hTcyc, hsC', hTC, hnormT⟩

end CFSG.EvenSporadicStandard.TwoHS
