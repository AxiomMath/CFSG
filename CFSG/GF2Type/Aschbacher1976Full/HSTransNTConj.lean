module

public import CFSG.GF2Type.Aschbacher1976Full.WidthTI
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GF2Type.Aschbacher1976Full.HSDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup

namespace Transport

variable {G : Type} [Group G] [Finite G]

theorem exists_eq_of_isConj {z u : G} (h : IsConj z u) : ∃ g : G, u = g⁻¹ * z * g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by rw [← hc]; simp⟩

theorem Hz_eq (z g : G) : Hz (g⁻¹ * z * g) = conjugate (Hz z) g := by
  ext x
  rw [Width.mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * x) * g⁻¹ := by rw [h]
      _ = z * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * z * g * x := by group

theorem Fz_eq (z g : G) : Fz (g⁻¹ * z * g) = conjugate (Fz z) g := by
  have h : (Hz z).map (MulAut.conj g⁻¹).toMonoidHom = Hz (g⁻¹ * z * g) := (Hz_eq z g).symm
  let e : ↥(Hz z) ≃* ↥(Hz (g⁻¹ * z * g)) :=
    (MulEquiv.subgroupMap (MulAut.conj g⁻¹) (Hz z)).trans (MulEquiv.subgroupCongr h)
  have key := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  show (generalizedFitting ↥(Hz (g⁻¹ * z * g))).map (Hz (g⁻¹ * z * g)).subtype =
    ((generalizedFitting ↥(Hz z)).map (Hz z).subtype).map (MulAut.conj g⁻¹).toMonoidHom
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem ZF_eq (u g : G) : ZF (g * u * g⁻¹) = conjugate (ZF u) g⁻¹ := by
  have := CFSG.GF2Type.CenterFour.centerAt_conj u g⁻¹
  rwa [inv_inv] at this

theorem mem_Dinv_iff (z g u : G) : u ∈ Dinv (g⁻¹ * z * g) ↔ g * u * g⁻¹ ∈ Dinv z := by
  show (IsConj (g⁻¹ * z * g) u ∧ u ≠ g⁻¹ * z * g ∧ ZF u ≤ Hz (g⁻¹ * z * g)) ↔
    (IsConj z (g * u * g⁻¹) ∧ g * u * g⁻¹ ≠ z ∧ ZF (g * u * g⁻¹) ≤ Hz z)
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [isConj_iff, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨g * c * g⁻¹, by rw [← hc]; group⟩
    · rintro ⟨d, hd⟩
      refine ⟨g⁻¹ * d * g, ?_⟩
      calc g⁻¹ * d * g * (g⁻¹ * z * g) * (g⁻¹ * d * g)⁻¹ = g⁻¹ * (d * z * d⁻¹) * g := by group
        _ = u := by rw [hd]; group
  · constructor
    · intro h h'
      exact h (by rw [← h']; group)
    · intro h h'
      exact h (by rw [h']; group)
  · rw [ZF_eq, Hz_eq z g]
    constructor
    · intro h x hx
      have h1 := Width.mem_conjugate_iff.mp (h (Width.mem_conjugate_iff.mp hx))
      rwa [show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group] at h1
    · intro h y hy
      refine Width.mem_conjugate_iff.mpr (h (Width.mem_conjugate_iff.mpr ?_))
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group]

theorem hsTI_of_isConj {z p : G} (hti : HSTI z) (hp : IsConj z p) : HSTI p := by
  obtain ⟨g, rfl⟩ := exists_eq_of_isConj hp
  refine ⟨?_, fun u hu => ?_⟩
  · obtain ⟨u, hu⟩ := hti.1
    exact ⟨g⁻¹ * u * g, (mem_Dinv_iff z g _).mpr
      (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])⟩
  · obtain ⟨h1, h2⟩ := hti.2 _ ((mem_Dinv_iff z g u).mp hu)
    refine ⟨?_, fun y hy hyF => ?_⟩
    · rw [Fz_eq]
      exact Width.mem_conjugate_iff.mpr h1
    · refine h2 (g * y * g⁻¹) ?_ (Width.mem_conjugate_iff.mp (by rwa [Fz_eq] at hyF))
      rw [ZF_eq, hy]
      show (zpowers y).map (MulAut.conj g⁻¹⁻¹).toMonoidHom = zpowers (g * y * g⁻¹)
      rw [MonoidHom.map_zpowers]
      simp [MulAut.conj_apply]

end Transport

end CFSG.GF2Type.Aschbacher1976Full.HS
