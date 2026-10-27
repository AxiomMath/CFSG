module

public import CFSG.CGT.M24S.NaturalSL

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

theorem conjSubgroup_eq_of_mem_normalizer {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) : conjSubgroup g U = U := by
  ext x
  rw [mem_conjSubgroup]
  have hg' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem hg
  have := (Subgroup.mem_normalizer_iff.1 hg' x)
  simpa [inv_inv] using this.symm

theorem mem_conjSubgroup_of_le_centralizer {U : Subgroup G}
    (hC : Subgroup.centralizer (U : Set G) ≤ U) {g t : G}
    (hg : conjSubgroup g U ≤ Subgroup.centralizer ({t} : Set G)) :
    g⁻¹ * t * g ∈ U := by
  apply hC
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hgu : g * u * g⁻¹ ∈ conjSubgroup g U := by
    rw [mem_conjSubgroup]; simpa [mul_assoc] using hu
  have hc := hg hgu
  rw [Subgroup.mem_centralizer_iff] at hc
  have h1 := hc t (Set.mem_singleton t)
  calc u * (g⁻¹ * t * g) = g⁻¹ * (g * u * g⁻¹ * t) * g := by group
    _ = g⁻¹ * (t * (g * u * g⁻¹)) * g := by rw [h1]
    _ = g⁻¹ * t * g * u := by group

theorem isWC_of_centralizer_le {U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hC : Subgroup.centralizer (U : Set G) ≤ U)
    (htr : ∀ x ∈ U, x ≠ 1 → ∀ y ∈ U, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (U : Set G), n * x * n⁻¹ = y)
    (hN : ∀ t ∈ U, t ≠ 1 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    IsWC U := by
  refine ⟨hU, fun t ht ht1 => ⟨?_, fun g hg => ?_⟩⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := hU.1.is_comm.comm ⟨x, ht⟩ ⟨u, hu⟩
    exact congrArg Subtype.val this
  · have hs := mem_conjSubgroup_of_le_centralizer hC hg
    have hs1 : g⁻¹ * t * g ≠ 1 := by
      intro h
      apply ht1
      have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      rw [this, h]; group
    obtain ⟨n, hn, hnt⟩ := htr _ hs hs1 t ht ht1
    have hc : g * n⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have : g * n⁻¹ * x * (g * n⁻¹)⁻¹ = x := by
        calc g * n⁻¹ * x * (g * n⁻¹)⁻¹
            = g * n⁻¹ * (n * (g⁻¹ * x * g) * n⁻¹) * (g * n⁻¹)⁻¹ := by rw [hnt]
          _ = x := by group
      calc x * (g * n⁻¹) = g * n⁻¹ * x * (g * n⁻¹)⁻¹ * (g * n⁻¹) := by rw [this]
        _ = g * n⁻¹ * x := by group
    have hgN : g ∈ Subgroup.normalizer (U : Set G) := by
      have := mul_mem (hN t ht ht1 hc) hn
      simpa using this
    exact conjSubgroup_eq_of_mem_normalizer hgN

theorem isWC_of_naturalSL {U M : Subgroup G} (hUM : U ≤ M) (hnat : NaturalSL U M 4 1)
    (hU : IsElemAbelian 2 U) (hC : Subgroup.centralizer (U : Set G) ≤ U)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hzN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    IsWC U := by
  have hMN := le_normalizer_of_naturalSL_four hUM hnat
  have htr : ∀ x ∈ U, x ≠ 1 → ∀ y ∈ U, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (U : Set G), n * x * n⁻¹ = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨h, hh, hxy⟩ := transitive_of_naturalSL hUM hnat x hx hx1 y hy hy1
    exact ⟨h, hMN hh, hxy⟩
  refine isWC_of_centralizer_le hU hC htr fun t ht ht1 => ?_
  obtain ⟨n, hn, rfl⟩ := htr z hzU hz1 t ht ht1
  intro c hc
  have hc' : n⁻¹ * c * n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 := hc (n * x * n⁻¹) (Set.mem_singleton _)
    calc x * (n⁻¹ * c * n) = n⁻¹ * ((n * x * n⁻¹) * c) * n := by group
      _ = n⁻¹ * (c * (n * x * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * c * n * x := by group
  have := mul_mem (mul_mem hn (hzN hc')) (inv_mem hn)
  simpa [mul_assoc] using this

end CFSG.CGT.M24S
