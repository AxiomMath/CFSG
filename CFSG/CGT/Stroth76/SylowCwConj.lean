module

public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.CGT.Stroth76

variable {G : Type*} [Group G] [Finite G]

theorem isConj_mul_of_isConj_central_of_conj (S : Sylow 2 G) {z v r : G}
    (hzS : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (hfact : ∀ x ∈ (S : Subgroup G), IsConj r x → x ≠ z →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * x * q = x * z)
    (hvz : IsConj v z) (hrS : r ∈ (S : Subgroup G)) (hrv : r * v = v * r) (hne : r ≠ v) :
    IsConj r (r * v) := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hvz
  set W := ((S : Subgroup G) ⊓ Subgroup.centralizer {v}).map (MulAut.conj g₀).toMonoidHom
  have hWz : W ≤ Subgroup.centralizer {z} := by
    rintro _ ⟨a, ha, rfl⟩
    have hav : a * v = v * a := Subgroup.mem_centralizer_singleton_iff.1 ha.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg₀]
    calc g₀ * a * g₀⁻¹ * (g₀ * v * g₀⁻¹) = g₀ * (a * v) * g₀⁻¹ := by group
      _ = g₀ * (v * a) * g₀⁻¹ := by rw [hav]
      _ = g₀ * v * g₀⁻¹ * (g₀ * a * g₀⁻¹) := by group
  have hWp : IsPGroup 2 W := (S.isPGroup'.to_le inf_le_left).map _
  obtain ⟨h, hh, hW⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (Subgroup.centralizer {z}) S hzS W hWz hWp
  have hhz : h * z * h⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hh
    rw [this]; group
  set n := h * g₀
  have hr' : n * r * n⁻¹ ∈ (S : Subgroup G) := by
    have := hW ⟨g₀ * r * g₀⁻¹, ⟨r, Subgroup.mem_inf.2 ⟨hrS,
      Subgroup.mem_centralizer_singleton_iff.2 hrv⟩, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    simpa [n, mul_assoc] using this
  have hnv : n * v * n⁻¹ = z := by
    calc n * v * n⁻¹ = h * (g₀ * v * g₀⁻¹) * h⁻¹ := by simp [n]; group
      _ = z := by rw [hg₀, hhz]
  have hr'z : n * r * n⁻¹ ≠ z := fun h' => hne (by
    calc r = n⁻¹ * (n * r * n⁻¹) * n := by group
      _ = n⁻¹ * (n * v * n⁻¹) * n := by rw [h', hnv]
      _ = v := by group)
  obtain ⟨q, -, hq⟩ := hfact _ hr' (isConj_iff.2 ⟨n, rfl⟩) hr'z
  rw [isConj_iff]
  refine ⟨n⁻¹ * q⁻¹ * n, ?_⟩
  calc n⁻¹ * q⁻¹ * n * r * (n⁻¹ * q⁻¹ * n)⁻¹
      = n⁻¹ * (q⁻¹ * (n * r * n⁻¹) * q) * n := by group
    _ = n⁻¹ * ((n * r * n⁻¹) * z) * n := by rw [hq]
    _ = n⁻¹ * ((n * r * n⁻¹) * (n * v * n⁻¹)) * n := by rw [hnv]
    _ = r * v := by group

end CFSG.CGT.Stroth76
