module

public import CFSG.CGT.Timmesfeld75.Sec6Five

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n : ℕ}

theorem conj_mem_centralizer {g d : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    (hd : d ∈ Subgroup.centralizer (T : Set G)) :
    g * d * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hd ⊢
  intro t ht
  have h1 : g⁻¹ * t * g ∈ T := by
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hg) ht
    simpa using this
  have h2 := hd _ h1
  calc t * (g * d * g⁻¹) = g * ((g⁻¹ * t * g) * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * t * g)) * g⁻¹ := by rw [h2]
    _ = g * d * g⁻¹ * t := by group

theorem comm_mem_T {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHnorm : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hHC : H ⊓ Subgroup.centralizer (T : Set G) = T) {x c : G} (hx : x ∈ H)
    (hc : c ∈ Subgroup.centralizer (T : Set G)) : x⁻¹ * c⁻¹ * x * c ∈ T := by
  have hcN : c ∈ Subgroup.normalizer (T : Set G) := Subgroup.centralizer_le_normalizer _ hc
  have hcinvN : c⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).inv_mem hcN
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).inv_mem (hHN hx)
  have h1 : x⁻¹ * c⁻¹ * x * c ∈ H := by
    have h2 : c⁻¹ * x * c ∈ H := by
      have := hHnorm c⁻¹ hcinvN x hx
      simpa using this
    have := H.mul_mem (H.inv_mem hx) h2
    simpa [mul_assoc] using this
  have h3 : x⁻¹ * c⁻¹ * x * c ∈ Subgroup.centralizer (T : Set G) := by
    have h4 := conj_mem_centralizer hxinvN ((Subgroup.centralizer (T : Set G)).inv_mem hc)
    have := (Subgroup.centralizer (T : Set G)).mul_mem h4 hc
    simpa using this
  have := Subgroup.mem_inf.2 ⟨h1, h3⟩
  rwa [hHC] at this

theorem exists_mul_mem_centralizer_single (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n 1)
    {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHnorm : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hHC : H ⊓ Subgroup.centralizer (T : Set G) = T) {c x : G}
    (hcC : c ∈ Subgroup.centralizer (T : Set G)) (hx : x ∈ normD T) (hxT : x ∉ T) (hxH : x ∈ H) :
    ∃ s ∈ T, c * s ∈ Subgroup.centralizer ({x} : Set G) := by
  have hyD : c⁻¹ * x * c ∈ classD T := classD_conj hx.1 c
  have hcomm : x⁻¹ * c⁻¹ * x * c ∈ T := comm_mem_T hHN hHnorm hHC hxH hcC
  obtain ⟨s, hsT, hs⟩ := hc.eq_conj_of_mem_coset h62 h63 hx hxT hyD hcomm
    (by group)
  refine ⟨s⁻¹, T.inv_mem hsT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h1 : x * (c * s⁻¹) = (c * s⁻¹) * x := by
    calc x * (c * s⁻¹) = (c * s⁻¹) * (s * (c⁻¹ * x * c) * s⁻¹) := by group
      _ = (c * s⁻¹) * (s * (s⁻¹ * x * s) * s⁻¹) := by rw [hs]
      _ = (c * s⁻¹) * x := by group
  exact h1.symm

end CFSG.CGT.T75P
