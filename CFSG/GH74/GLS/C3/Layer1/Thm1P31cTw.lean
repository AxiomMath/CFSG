module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Fus

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpElim

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem exists_twisted_commutator_central
    {L : Type} [Group L] [Finite L] (h : CFSG.GH74.E2.Shape2M12 L) (σ : MulAut L) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {P : Subgroup L} (hP : ⁅P, P⁆ = P) (hP2 : 2 < Nat.card ↥P)
    (hPσ : ∀ x ∈ P, σ x = x) {t₁ : L} (ht₁2 : orderOf t₁ = 2) (ht₁c : t₁ ∈ center L) :
    ∃ l : L, l * (σ l)⁻¹ = t₁ := by
  obtain ⟨t, π, hc⟩ := CFSG.GH74.KGroups.TwoM12.exists_isCover h
  have hq : CFSG.Assembly.IsQuasisimple L := ⟨Group.isPerfect_def.1 h.1.1, h.1.2.1⟩
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 hc.orderOf_t).2
  have htt₁ : t₁ = t := by
    have hmem : t₁ ∈ zpowers t := hc.center_eq ▸ ht₁c
    rcases eq_one_or_eq_of_mem_zpowers hc.orderOf_t hmem with h1 | h1
    · exfalso
      rw [h1, orderOf_one] at ht₁2
      omega
    · exact h1
  subst htt₁
  have ht₁tt : t₁ * t₁ = 1 := by rw [← sq, ← ht₁2, pow_orderOf_eq_one]
  have hσt : σ t₁ = t₁ := by
    have hmem : σ t₁ ∈ center L := by
      have : σ t₁ ∈ (center L).map (σ : L →* L) := ⟨t₁, ht₁c, rfl⟩
      rwa [Subgroup.map_center_eq σ] at this
    rcases eq_one_or_eq_of_mem_zpowers hc.orderOf_t (hc.center_eq ▸ hmem) with h1 | h1
    · exfalso
      exact ht1 (σ.injective (by rw [h1, map_one]))
    · exact h1
  by_cases hin : ∃ u : L, ∀ x : L, σ x = u * x * u⁻¹
  · obtain ⟨u, hu⟩ := hin
    have huu : u * u ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : σ (σ g) = g := by
        have := congrArg (fun f : MulAut L => f g) hσ2
        simpa using this
      rw [hu, hu] at h1
      have h2 : u * (u * g * u⁻¹) * u⁻¹ = g := h1
      calc g * (u * u) = (u * (u * g * u⁻¹) * u⁻¹) * (u * u) := by rw [h2]
        _ = (u * u) * g := by group
    have hPu : ∀ x ∈ P, x * u = u * x := by
      intro x hx
      have h1 := hPσ x hx
      rw [hu] at h1
      calc x * u = (u * x * u⁻¹) * u := by rw [h1]
        _ = u * x := by group
    rcases eq_one_or_eq_of_mem_zpowers hc.orderOf_t (hc.center_eq ▸ huu) with h1 | h1
    ·
      exfalso
      have hπuu : π u * π u = 1 := by rw [← map_mul, h1, map_one]
      have hπu1 : π u ≠ 1 := by
        intro h1'
        have hu_ker : u ∈ π.ker := h1'
        rw [hc.ker_eq, ← hc.center_eq] at hu_ker
        apply hσ1
        ext x
        rw [hu, MulAut.one_apply]
        have := Subgroup.mem_center_iff.1 hu_ker x
        calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [← this]
          _ = x := by group
      have hord : orderOf (π u) = 2 := orderOf_eq_prime (by rw [sq]; exact hπuu) hπu1
      obtain ⟨hfc, -, hlift0⟩ :=
        m12_double_cover_involution_lift_orders hq hc.orderOf_t hc.center_eq π hc.surjective hc.ker_eq
      have hfour : fixedCount (π u) = 4 := by
        rcases hfc _ hord with h4 | h0
        · exact h4
        · exfalso
          have hut := (hlift0 u hord h0).1
          rw [sq, h1] at hut
          exact ht1 hut.symm
      obtain ⟨g, hg⟩ := conj_elemR_of_fixedCount_four (π u) hord hfour
      obtain ⟨g', rfl⟩ := hc.surjective g
      obtain ⟨hP', hPu', hcard⟩ := CFSG.GH74.KGroups.TwoM12.conj_data (u := u) g' hP hPu
      have hu' : π (g'⁻¹ * u * g') = elemR := by
        rw [map_mul, map_mul, map_inv, ← hg]
        group
      have hle := CFSG.GH74.KGroups.TwoM12.card_le_two_of_comm_r hc hu' hP' hPu'
      rw [hcard] at hle
      omega
    ·
      have hu2 : u ^ 2 = t₁ := by rw [sq]; exact h1
      have htu : t₁ * u = u * t₁ := (Subgroup.mem_center_iff.1 ht₁c u).symm
      have htusq : (t₁ * u) ^ 2 = t₁ := by
        rw [Commute.mul_pow htu, hu2, sq t₁, ht₁tt, one_mul]
      obtain ⟨g, hg⟩ :=
        exists_conj_of_sq_eq hq hc.orderOf_t hc.center_eq π hc.surjective hc.ker_eq hu2 htusq
      refine ⟨g, ?_⟩
      rw [hu g]
      calc g * (u * g * u⁻¹)⁻¹ = (g * u * g⁻¹) * u⁻¹ := by group
        _ = t₁ * u * u⁻¹ := by rw [hg]
        _ = t₁ := by group
  · exact exists_twisted_commutator_outer hc hq σ hσ2 hσ1 hin hσt hc.orderOf_t

end CFSG.GH74.GLS.C3.Layer1.PumpElim
