module

public import CFSG.GF2Type.Aschbacher1976Full.HSBadLocal2
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCGen

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

theorem cruxS0_holds :
    ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z →
      ∀ k : G, ZF z = Subgroup.zpowers k → ∀ u : G, IsConj z u → u * k = k * u → u = z ∨ u ∈ Dinv z := by
  intro G _ _ z hset k hk u hconj huk
  by_cases huz : u = z
  · exact Or.inl huz
  refine Or.inr ?_
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨g, rfl⟩ := exists_conj hconj
  obtain ⟨hk4, hk2⟩ := gen_props hD hz hF2 (IsConj.refl z) hk
  have hkZ : k ∈ Z := (ZF_z hD hz hF2) ▸ (hk ▸ mem_zpowers k)
  have hZu : ZF (g⁻¹ * z * g) = zpowers (g⁻¹ * k * g) := by
    simpa using ZF_conj_zpowers g⁻¹ hk
  obtain ⟨hx4, hx2⟩ := gen_props hD hz hF2 hconj hZu
  obtain ⟨-, -, -, hu2, hu1⟩ := ZF_props hD hz hF2 hconj
  refine ⟨hconj, huz, ?_⟩
  rw [hZu, zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  set x := g⁻¹ * k * g with hxdef
  have hc : g * k * g⁻¹ ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * k * g⁻¹ * z = g * (k * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * k) * g⁻¹ := by rw [huk]
      _ = z * (g * k * g⁻¹) := by group
  have hkxk : k * x * k⁻¹ ∈ zpowers x := by
    rw [← hZu, ZF_conj hD hz hF2 g, Width.mem_conjugate_iff]
    have := Width.Z_conj_mem hD hz hc hkZ
    convert this using 1
    rw [hxdef]
    group
  have hord : orderOf (k * x * k⁻¹) = 4 := by
    have := Bad.orderOf_conj_inv x k⁻¹
    rwa [inv_inv, hx4] at this
  rcases Bad.eq_or_eq_inv_of_mem_zpowers hx4 hord hkxk with h | h
  · have hkx : k * x = x * k := by
      calc k * x = (k * x * k⁻¹) * k := by group
        _ = x * k := by rw [h]
    have hxk : Commute x k := hkx.symm
    rw [← hk2]
    exact (hxk.pow_right 2).eq
  · exfalso
    have hkxi : k * x = x⁻¹ * k := by
      calc k * x = (k * x * k⁻¹) * k := by group
        _ = x⁻¹ * k := by rw [h]
    have hkxi' : k * x⁻¹ = x * k := by
      have h1 : k * x⁻¹ * k⁻¹ = x := by
        have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
        rw [this, h, inv_inv]
      calc k * x⁻¹ = (k * x⁻¹ * k⁻¹) * k := by group
        _ = x * k := by rw [h1]
    have hkk : k ^ 2 * x = x * k ^ 2 := by
      calc k ^ 2 * x = k * (k * x) := by rw [pow_two]; group
        _ = k * (x⁻¹ * k) := by rw [hkxi]
        _ = (k * x⁻¹) * k := by group
        _ = x * k * k := by rw [hkxi']
        _ = x * k ^ 2 := by rw [pow_two]; group
    have hxH : x ∈ Hz z := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hk2]
      exact hkk.symm
    have hZ' := Width.Z_conj_mem hD hz hxH hkZ
    have hui : (g⁻¹ * z * g)⁻¹ = g⁻¹ * z * g := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    have hxkx : x * k * x⁻¹ = k * (g⁻¹ * z * g) := by
      calc x * k * x⁻¹ = k * x⁻¹ * x⁻¹ := by rw [← hkxi']
        _ = k * (x * x)⁻¹ := by group
        _ = k * (g⁻¹ * z * g)⁻¹ := by rw [← pow_two, hx2]
        _ = k * (g⁻¹ * z * g) := by rw [hui]
    rw [hxkx] at hZ'
    have huZ : g⁻¹ * z * g ∈ Z := by
      have := Z.mul_mem (Z.inv_mem hkZ) hZ'
      rwa [inv_mul_cancel_left] at this
    exact huz (Width.involution_eq hD hz huZ hu2 hu1)

end CFSG.GF2Type.Aschbacher1976Full.HS
