module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshCentralQuotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFourGroup

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

theorem odd_normal_eq_bot_of_fourGroup {G : Type*} [Group G] [Finite G]
    (c e u : G) (Q : Subgroup G)
    (hec : e * c = c * e) (huc : u * c = c * u)
    (he2 : e * e = 1) (hu2 : u * u = 1) (heu : e * u = u * e)
    (hH : Nat.card (Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) :
      Subgroup G) = 384)
    (hfact : ∀ y ∈ (Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) :
      Subgroup G), orderOf y = 3 →
        ∃ z ∈ (Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) :
          Subgroup G), z * y * z⁻¹ ∉ Subgroup.zpowers y)
    (hQn : ∀ g : G, g * c = c * g → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQc : ∀ q ∈ Q, q * c = c * q)
    (hodd : Odd (Nat.card Q))
    (hfu : ∃ ℓ : G, ℓ * c = c * ℓ ∧ ℓ * e * ℓ⁻¹ = u)
    (hfue : ∃ ℓ : G, ℓ * c = c * ℓ ∧ ℓ * e * ℓ⁻¹ = u * e) :
    Q = ⊥ := by
  have hKe : ∀ k ∈ Q, e * k = k * e → k = 1 := by
    set H : Subgroup G :=
      Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) with hHdef
    have hmem : ∀ y, y ∈ H ↔ y * e = e * y ∧ y * c = c * y := fun y => by
      rw [hHdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
    have hQ₁ : Q ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
      refine odd_normal_eq_bot_of_order_three H _ hH (fun y hy => ?_) (fun h hh q hq => ?_)
        (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)) hfact
      · obtain ⟨hyQ, hye⟩ := Subgroup.mem_inf.1 hy
        exact (hmem y).2 ⟨Subgroup.mem_centralizer_singleton_iff.1 hye, hQc y hyQ⟩
      · obtain ⟨hqQ, hqe⟩ := Subgroup.mem_inf.1 hq
        obtain ⟨hhe, hhc⟩ := (hmem h).1 hh
        refine Subgroup.mem_inf.2 ⟨hQn h hhc q hqQ, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (((show Commute h e from hhe).mul_left
          (show Commute q e from Subgroup.mem_centralizer_singleton_iff.1 hqe)).mul_left
          (show Commute h e from hhe).inv_left)
    intro k hk hek
    have hk1 : k ∈ Q ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.2 ⟨hk, Subgroup.mem_centralizer_singleton_iff.2 hek.symm⟩
    rwa [hQ₁, Subgroup.mem_bot] at hk1
  have hconj : ∀ ℓ : G, ℓ * c = c * ℓ → ∀ k ∈ Q,
      (ℓ * e * ℓ⁻¹) * k = k * (ℓ * e * ℓ⁻¹) → k = 1 := by
    intro ℓ hℓ k hk hcomm
    have hℓ' : ℓ⁻¹ * c = c * ℓ⁻¹ := (show Commute ℓ c from hℓ).inv_left
    have hk' : ℓ⁻¹ * k * ℓ ∈ Q := by simpa using hQn ℓ⁻¹ hℓ' k hk
    have h1 : ℓ⁻¹ * k * ℓ = 1 := by
      refine hKe _ hk' ?_
      calc e * (ℓ⁻¹ * k * ℓ) = ℓ⁻¹ * ((ℓ * e * ℓ⁻¹) * k) * ℓ := by group
        _ = ℓ⁻¹ * (k * (ℓ * e * ℓ⁻¹)) * ℓ := by rw [hcomm]
        _ = (ℓ⁻¹ * k * ℓ) * e := by group
    calc k = ℓ * (ℓ⁻¹ * k * ℓ) * ℓ⁻¹ := by group
      _ = 1 := by rw [h1]; group
  refine eq_bot_of_fourGroup Q e u he2 hu2 heu (hQn e hec) (hQn u huc) hKe ?_ ?_
  · obtain ⟨ℓ, hℓ, hℓe⟩ := hfu
    intro k hk hcomm
    exact hconj ℓ hℓ k hk (by rw [hℓe]; exact hcomm)
  · obtain ⟨ℓ, hℓ, hℓe⟩ := hfue
    intro k hk hcomm
    exact hconj ℓ hℓ k hk (by rw [hℓe, ← heu]; exact hcomm)

end CFSG.EvenSporadicStandard.M12Std.Yosh
