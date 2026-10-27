module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Balance

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_mem_centralizer_singleton {b z x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    b * x * b⁻¹ ∈ Subgroup.centralizer ({b * z * b⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc (b * x * b⁻¹) * (b * z * b⁻¹) = b * (x * z) * b⁻¹ := by group
    _ = b * (z * x) * b⁻¹ := by rw [hx]
    _ = (b * z * b⁻¹) * (b * x * b⁻¹) := by group

omit [Finite G] in
private theorem conj_inv_mem_centralizer_singleton {b z y : G}
    (hy : y ∈ Subgroup.centralizer ({b * z * b⁻¹} : Set G)) :
    b⁻¹ * y * b ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc (b⁻¹ * y * b) * z = b⁻¹ * (y * (b * z * b⁻¹)) * b := by group
    _ = b⁻¹ * ((b * z * b⁻¹) * y) * b := by rw [hy]
    _ = z * (b⁻¹ * y * b) := by group

omit [Finite G] in
private def conjCentralizerEquiv (b z : G) :
    ↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer ({b * z * b⁻¹} : Set G)) where
  toFun x := ⟨b * (x : G) * b⁻¹, conj_mem_centralizer_singleton x.2⟩
  invFun y := ⟨b⁻¹ * (y : G) * b, conj_inv_mem_centralizer_singleton y.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem map_pCore_le {H H' : Type*} [Group H] [Group H'] (p : ℕ) (f : H ≃* H') :
    (CFSG.pCore p H).map f.toMonoidHom ≤ CFSG.pCore p H' := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold CFSG.pCore
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup ⟨Subgroup.Normal.map hK.1 f.toMonoidHom f.surjective,
    IsPGroup.map hK.2 f.toMonoidHom⟩

theorem oddCoreIn_centralizer_conj_eq_bot {b z : G}
    (h : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({b * z * b⁻¹} : Set G)) = ⊥ := by
  have hC : CFSG.Open.componentClassificationOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    rw [oddCoreIn] at h
    exact Subgroup.map_injective (Subgroup.centralizer ({z} : Set G)).subtype_injective
      (by rw [h, Subgroup.map_bot])
  have hD : CFSG.Open.componentClassificationOddCore
      ↥(Subgroup.centralizer ({b * z * b⁻¹} : Set G)) = ⊥ := by
    rw [← CFSG.ComponentClassification.OddCore.equiv_invariant (conjCentralizerEquiv b z), hC,
      Subgroup.map_bot]
  rw [oddCoreIn, hD, Subgroup.map_bot]

theorem conj_mem_pCore_centralizer_conj {b z e : G}
    (h : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype) :
    b * e * b⁻¹ ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({b * z * b⁻¹} : Set G))).map
      (Subgroup.centralizer ({b * z * b⁻¹} : Set G)).subtype := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp h
  exact Subgroup.mem_map.mpr ⟨conjCentralizerEquiv b z x,
    map_pCore_le 2 (conjCentralizerEquiv b z) (Subgroup.mem_map_of_mem _ hx), rfl⟩

end CFSG.ClassicalInvolution.Sp62Rec
